/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveReplayMenu

/-! # Removing response distinctions with no operational effect

Submission normalization preserves the exact public packet and complete
application effect, and can use only the sender's local observation. Replay
normalization replaces an unavailable replay by silence. The resulting finite
menus contain normal forms only. These are operational certificates; they do
not assert equilibrium equivalence with a game recording raw response syntax.
-/

noncomputable section

namespace Interaction.ReactiveApplication

variable {Principal : Type} (app : ReactiveApplication Principal)

structure SubmissionNormalization where
  normalize : Principal → app.LocalObservation → app.Submission → app.Submission
  idempotent : ∀ who view submission,
    normalize who view (normalize who view submission) = normalize who view submission
  packet : ∀ who view submission,
    app.packet (normalize who view submission) = app.packet submission
  submit : ∀ state who submission,
    app.submit state who (normalize who (app.observePlayer state who) submission) =
      app.submit state who submission

namespace SubmissionNormalization

variable {app} (normal : app.SubmissionNormalization)

/-- This test uses only remembered outputs, leaked packets and the ledger. -/
def ReplayKnown (past : List app.PlayerEntry) (view : app.PlayerView)
    (id : MessageId Principal) : Prop :=
  ∃ message ∈ ResponseMenu.knownPackets past view, message.id = id

open Classical in
def action (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView) :
    app.Action → app.Action
  | ⟨none⟩ => ⟨none⟩
  | ⟨some (.submit submission)⟩ =>
      ⟨some (.submit (normal.normalize who view.application submission))⟩
  | ⟨some (.replay id)⟩ => if ReplayKnown past view id then ⟨some (.replay id)⟩ else ⟨none⟩

theorem action_idempotent (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action) :
    normal.action who past view (normal.action who past view response) =
      normal.action who past view response := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => simp only [action, normal.idempotent]
      | replay id => by_cases known : ReplayKnown past view id <;> simp [action, known]

/-- A menu of semantic responses, obtained by normalizing every supplied choice. -/
def menu (raw : app.ResponseMenu) : app.ResponseMenu where
  actions who past view := by
    classical
    exact (raw.actions who past view).image (normal.action who past view)
  nonempty who past view := by
    classical
    exact (raw.nonempty who past view).image _

theorem menu_mem (raw : app.ResponseMenu) (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action) :
    response ∈ (normal.menu raw).actions who past view ↔
      ∃ original ∈ raw.actions who past view, normal.action who past view original = response := by
  classical
  exact Finset.mem_image

theorem menu_normal (raw : app.ResponseMenu) (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action)
    (member : response ∈ (normal.menu raw).actions who past view) :
    normal.action who past view response = response := by
  obtain ⟨original, _, rfl⟩ := (normal.menu_mem raw who past view response).mp member
  exact normal.action_idempotent who past view original

theorem menu_mem_iff_of_closed (raw : app.ResponseMenu) (who : Principal)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (closed : ∀ response ∈ raw.actions who past view,
      normal.action who past view response ∈ raw.actions who past view)
    (response : app.Action) :
    response ∈ (normal.menu raw).actions who past view ↔
      response ∈ raw.actions who past view ∧ normal.action who past view response = response := by
  constructor
  · intro member
    refine ⟨?_, normal.menu_normal raw who past view response member⟩
    obtain ⟨original, supported, rfl⟩ := (normal.menu_mem raw who past view response).mp member
    exact closed original supported
  · rintro ⟨member, fixed⟩
    exact (normal.menu_mem raw who past view response).mpr ⟨response, member, fixed⟩

variable [DecidableEq Principal]

theorem replayKnown_iff (execution : app.Execution) (who : Principal)
    (valid : execution.InputRecall app) (id : MessageId Principal) :
    ReplayKnown (execution.recall who) (execution.observe app who) id ↔
      ∃ message ∈ execution.network.known who, message.id = id := by
  rw [app.known_from_recall execution who valid]
  rfl

/-- Only the focal player's recorded raw response may differ. Packets, all
application state, receipts, scheduler recall and other players' recall agree. -/
theorem effects (execution : app.Execution) (who : Principal) (response : app.Action)
    (valid : execution.InputRecall app) :
    let normalized := execution.respond app who
      (normal.action who (execution.recall who) (execution.observe app who) response)
    let original := execution.respond app who response
    normalized.application = original.application ∧ normalized.network = original.network ∧
      normalized.receipts = original.receipts ∧
      normalized.environmentRecall = original.environmentRecall ∧
      ∀ observer, observer ≠ who → normalized.recall observer = original.recall observer := by
  have others (first second : app.Action) : ∀ observer, observer ≠ who →
      (execution.respond app who first).recall observer =
        (execution.respond app who second).recall observer := by
    intro observer different
    rw [app.respond_recall_other execution who observer different,
      app.respond_recall_other execution who observer different]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨rfl, rfl, rfl, rfl, others _ _⟩
  | some transmission =>
      cases transmission with
      | submit submission =>
          refine ⟨?_, ?_, rfl, rfl, others _ _⟩
          · exact normal.submit execution.application who submission
          · change (execution.network.submit who
                (app.packet (normal.normalize who _ submission))).2 = _
            rw [normal.packet]
            rfl
      | replay id =>
          classical
          by_cases known : ReplayKnown (execution.recall who) (execution.observe app who) id
          · simp [action, known]
          · have absent : (execution.network.known who).find?
                  (fun envelope => envelope.id = id) = none := by
              apply List.find?_eq_none.mpr
              intro message member same
              exact known ((replayKnown_iff execution who valid id).mpr
                ⟨message, member, of_decide_eq_true same⟩)
            refine ⟨?_, ?_, ?_, ?_, others _ _⟩
            all_goals simp [action, known, Execution.respond, MessageNetwork.replay, absent]

end SubmissionNormalization

namespace ResponseMenu

variable {app}

/-- Every supplied submission, silence, and every locally known replay. -/
def fromSubmissions (submissions : Finset app.Submission) : app.ResponseMenu := by
  classical
  exact withKnownReplays {
    actions := fun _ _ _ => insert ⟨none⟩
      (submissions.image fun submission => ⟨some (.submit submission)⟩)
    nonempty := fun _ _ _ => ⟨⟨none⟩, Finset.mem_insert_self _ _⟩ }

theorem fromSubmissions_mem (submissions : Finset app.Submission) (who : Principal)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action) :
    response ∈ (fromSubmissions submissions).actions who past view ↔
      match response.transmission with
      | none => True
      | some (.submit submission) => submission ∈ submissions
      | some (.replay id) => SubmissionNormalization.ReplayKnown past view id := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp [fromSubmissions, withKnownReplays]
  | some transmission =>
      cases transmission <;>
        simp [fromSubmissions, withKnownReplays, replayActions,
          SubmissionNormalization.ReplayKnown, eq_comm]

end ResponseMenu
end Interaction.ReactiveApplication

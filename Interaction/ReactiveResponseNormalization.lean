/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu

/-! # Removing response distinctions with no operational effect

Submission normalization preserves the exact public packet and complete
application effect, and can use only the sender's local observation and known
packets. The resulting finite menus contain normal forms only. These are
operational certificates; they do not assert equilibrium equivalence with a
game recording raw response syntax.
-/

noncomputable section

namespace Interaction.ReactiveApplication

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- The envelopes a player can cite: its remembered outputs, leaked packets and
the ledger. -/
def ResponseMenu.knownPackets {app : ReactiveApplication Principal}
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    List (Message Principal app.Payload) :=
  app.outputs past ++ view.messages.leaked ++ view.messages.ledger

structure SubmissionNormalization where
  normalize : Principal → app.LocalObservation → List (Message Principal app.Payload) →
    app.Submission → app.Submission
  idempotent : ∀ who view known submission,
    normalize who view known (normalize who view known submission) =
      normalize who view known submission
  packet : ∀ state who known submission,
    app.packet (app.submit state who submission) who known
        (normalize who (app.observePlayer state who) known submission) =
      app.packet (app.submit state who submission) who known submission
  submit : ∀ state who known submission,
    app.submit state who (normalize who (app.observePlayer state who) known submission) =
      app.submit state who submission

namespace SubmissionNormalization

variable {app} (normal : app.SubmissionNormalization)

def action (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView) :
    app.Action → app.Action
  | ⟨none⟩ => ⟨none⟩
  | ⟨some submission⟩ =>
      ⟨some (normal.normalize who view.application
        (ResponseMenu.knownPackets past view) submission)⟩

theorem action_idempotent (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action) :
    normal.action who past view (normal.action who past view response) =
      normal.action who past view response := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission => simp only [action, normal.idempotent]

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
  have known : ResponseMenu.knownPackets (execution.recall who) (execution.observe app who) =
      execution.network.known who := (app.known_from_recall execution who valid).symm
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨rfl, rfl, rfl, rfl, others _ _⟩
  | some submission =>
      refine ⟨?_, ?_, rfl, rfl, others _ _⟩
      · exact normal.submit execution.application who _ submission
      · change (execution.network.submit who
            (app.packet (app.submit execution.application who
              (normal.normalize who _ _ submission)) who (execution.network.known who)
                (normal.normalize who _ _ submission))).2 = _
        rw [known]
        change (execution.network.submit who
            (app.packet (app.submit execution.application who
              (normal.normalize who (app.observePlayer execution.application who)
                (execution.network.known who) submission)) who (execution.network.known who)
                (normal.normalize who (app.observePlayer execution.application who)
                  (execution.network.known who) submission))).2 = _
        rw [normal.submit, normal.packet]
        rfl

end SubmissionNormalization

namespace ResponseMenu

variable {app}

/-- Every information-local supplied submission, and silence. -/
def fromSubmissions
    (submissions : Principal → List app.PlayerEntry → app.PlayerView → Finset app.Submission) :
    app.ResponseMenu := by
  classical
  exact {
    actions := fun who past view => insert ⟨none⟩
      ((submissions who past view).image fun submission => ⟨some submission⟩)
    nonempty := fun _ _ _ => ⟨⟨none⟩, Finset.mem_insert_self _ _⟩ }

theorem fromSubmissions_mem
    (submissions : Principal → List app.PlayerEntry → app.PlayerView → Finset app.Submission)
    (who : Principal)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action) :
    response ∈ (fromSubmissions submissions).actions who past view ↔
      match response.transmission with
      | none => True
      | some submission => submission ∈ submissions who past view := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp [fromSubmissions]
  | some transmission => simp [fromSubmissions]

end ResponseMenu
end Interaction.ReactiveApplication

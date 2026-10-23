/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketTrembles

/-! # Support facts for prescribed play in the one-packet game

**Failed reveals.** A failed reveal persists under every source step
(`Vegas.SourceProgram.ProtocolState.revealFailed_step`), and whether a player's
reveal failed is the same at any two points every player, not only the owner,
observes alike (`Vegas.SourceProgram.ProtocolState.revealFailed_iff_of_observe_eq`):
publications are public.

**As-if-honest support.** At a native state whose configuration decodes at its
completed prefix, as-if-honest play of the owner is the intended strategy at
the owner's view of the decoded point (`Vegas.asIfHonestProfile_observe`), so
its support is the image of that strategy's support
(`Vegas.mem_support_asIfHonestProfile_observe`).

**Classification.** The pending event of a decision input is the owner's turn
event when its recall has not submitted for it (`Vegas.pendingEvent`). A first
activation is a decision input with a pending event at none of whose recalled
views that event was the owner's turn (`Vegas.FirstActivation`); a late
delivery has a pending event that was the owner's turn at some recalled view
(`Vegas.LateDelivery`). Both are functions of the information state, they
exclude each other, and every input with a pending event is one of them.

**Menu membership.** A canonical decision retained by the canonical menu,
whose local envelope the count verdict permits, lies in the one-packet menu
(`Vegas.canonical_mem_onePacket`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A failed reveal persists under every source step, whatever anyone plays. -/
theorem revealFailed_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    RevealFailed who program state → target ∈ (step program state joint).support →
      RevealFailed who program target
  | _, _, .ret _, _, _, _, failed, _ => failed.elim
  | _, _, .sample _ _ _ next, state, joint, target, failed, reached => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact revealFailed_step who next rest joint after failed supported
  | _, _, .commit _ _ _ _ next, state, joint, target, failed, reached => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact revealFailed_step who next rest joint after failed supported
  | _, _, .reveal _ _ _ _ _ _ next, state, joint, target, failed, reached => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases failed with ⟨own, publication⟩ | later
          · exact Or.inl ⟨own, (base_step next rest joint after supported).symm ▸ publication⟩
          · exact Or.inr (revealFailed_step who next rest joint after later supported)

/-- **Failed reveals are public.** Whether `who`'s reveal failed is the same at
two points that any player `observer` observes alike. -/
theorem revealFailed_iff_of_observe_eq (who observer : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    observe observer program left = observe observer program right →
      (RevealFailed who program left ↔ RevealFailed who program right)
  | _, _, .ret _, _, _, _ => Iff.rfl
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => exact Iff.rfl
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact revealFailed_iff_of_observe_eq who observer next first second
                (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => exact Iff.rfl
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact revealFailed_iff_of_observe_eq who observer next first second
                (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => exact Iff.rfl
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              have later := Sum.inr.inj same
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observe_eq observer next first second later) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, revealFailed_iff_of_observe_eq who observer next first second later]

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A failed reveal is closed under every source step. -/
theorem revealFailed_stepClosed {setup : Setup (Player := Player) (L := L)} (who : Player) :
    StepClosed setup (ProtocolState.RevealFailed who setup.program) :=
  fun state joint target failed reached =>
    ProtocolState.revealFailed_step who setup.program state joint target failed reached

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section AsIfHonest

/-- **As-if-honest play at a decoded state.** At an execution whose
configuration decodes at its completed prefix to a source point, as-if-honest
play of `who`, whatever its recall, is the intended strategy at `who`'s view of
that point. -/
theorem asIfHonestProfile_observe (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (execution : (application setup leaks).Execution) (rank : Nat)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup leaks).PlayerEntry) :
    asIfHonestProfile setup leaks assessment who
        (some (past, execution.observe (application setup leaks) who)) =
      (assessment.strategy who (setup.protocolObserve who (some point))).map Subtype.val := by
  unfold asIfHonestProfile
  rw [projectView_observe setup leaks who execution rank ordered point decoded past]

/-- The support of as-if-honest play at a decoded state is the image of the
intended strategy's support at the decoded view. -/
theorem mem_support_asIfHonestProfile_observe
    (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (execution : (application setup leaks).Execution) (rank : Nat)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup leaks).PlayerEntry) (choice : Option (OwnAction Player L)) :
    choice ∈ (asIfHonestProfile setup leaks assessment who
        (some (past, execution.observe (application setup leaks) who))).support ↔
      ∃ intended ∈ (assessment.strategy who (setup.protocolObserve who (some point))).support,
        intended.1 = choice := by
  rw [asIfHonestProfile_observe setup leaks assessment who execution rank ordered point decoded
    past, PMF.support_map]
  rfl

end AsIfHonest

section Classification

/-- The pending event of a decision input: the owner's turn event, provided its
recall has not submitted for it. -/
def pendingEvent (who : Player) : (application setup leaks).Info → Option (graph setup).EventId
  | none => none
  | some (past, view) => (view.application.publicView.ownTurn? who).filter fun event =>
      !(runtime setup).eventRecorded leaks past event

/-- The owner's turn was `event` at the view a recall entry was taken at. -/
def ActivatedAt (who : Player) (event : (graph setup).EventId)
    (entry : (application setup leaks).PlayerEntry) : Prop :=
  entry.beforeView.application.publicView.ownTurn? who = some event

/-- **First activation.** A decision input with a pending event that was the
owner's turn at none of its recalled views. -/
def FirstActivation (who : Player) (info : (application setup leaks).Info) : Prop :=
  ∃ past view event, info = some (past, view) ∧ pendingEvent setup leaks who info = some event ∧
    ∀ entry ∈ past, ¬ ActivatedAt setup leaks who event entry

/-- **Late delivery.** A decision input with a pending event that was the
owner's turn at some recalled view, at which it did not submit for it. -/
def LateDelivery (who : Player) (info : (application setup leaks).Info) : Prop :=
  ∃ past view event, info = some (past, view) ∧ pendingEvent setup leaks who info = some event ∧
    ∃ entry ∈ past, ActivatedAt setup leaks who event entry

variable {setup leaks}

/-- A pending event is the owner's ready turn event, and the recall has not
submitted for it. -/
theorem pendingEvent_spec {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event) :
    view.application.publicView.ownTurn? who = some event ∧
      view.application.publicView.EventReady event ∧ (graph setup).actor? event = some who ∧
      (runtime setup).eventRecorded leaks past event = false := by
  simp only [pendingEvent, Option.filter_eq_some_iff, Bool.not_eq_eq_eq_not, Bool.not_true]
    at pending
  have spec := view.application.publicView.ownTurn?_spec who event pending.1
  exact ⟨pending.1, spec.1, spec.2, pending.2⟩

theorem pendingEvent_of_spec {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (unsent : (runtime setup).eventRecorded leaks past event = false) :
    pendingEvent setup leaks who (some (past, view)) = some event := by
  simp only [pendingEvent, Option.filter_eq_some_iff, turn, unsent, Bool.not_false, and_self]

/-- First activations and late deliveries exclude each other. -/
theorem not_lateDelivery_of_firstActivation {who : Player}
    {info : (application setup leaks).Info} (first : FirstActivation setup leaks who info) :
    ¬ LateDelivery setup leaks who info := by
  rintro ⟨past', view', event', same', pending', entry, member, activated⟩
  obtain ⟨past, view, event, same, pending, never⟩ := first
  rw [same] at same'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same')
  rw [pending] at pending'
  cases Option.some.inj pending'
  exact never entry member activated

/-- Every decision input with a pending event is a first activation or a late
delivery. -/
theorem firstActivation_or_lateDelivery {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event) :
    FirstActivation setup leaks who (some (past, view)) ∨
      LateDelivery setup leaks who (some (past, view)) := by
  by_cases earlier : ∃ entry ∈ past, ActivatedAt setup leaks who event entry
  · exact Or.inr ⟨past, view, event, rfl, pending, earlier⟩
  · push Not at earlier
    exact Or.inl ⟨past, view, event, rfl, pending, earlier⟩

/-- At a first activation or a late delivery the event is pending at the
current view. -/
theorem FirstActivation.pending {who : Player} {info : (application setup leaks).Info}
    (first : FirstActivation setup leaks who info) :
    ∃ past view event, info = some (past, view) ∧
      view.application.publicView.ownTurn? who = some event ∧
      view.application.publicView.EventReady event ∧ (graph setup).actor? event = some who ∧
      (runtime setup).eventRecorded leaks past event = false := by
  obtain ⟨past, view, event, rfl, pending, _⟩ := first
  exact ⟨past, view, event, rfl, pendingEvent_spec pending⟩

theorem LateDelivery.pending {who : Player} {info : (application setup leaks).Info}
    (late : LateDelivery setup leaks who info) :
    ∃ past view event, info = some (past, view) ∧
      view.application.publicView.ownTurn? who = some event ∧
      view.application.publicView.EventReady event ∧ (graph setup).actor? event = some who ∧
      (runtime setup).eventRecorded leaks past event = false := by
  obtain ⟨past, view, event, rfl, pending, _⟩ := late
  exact ⟨past, view, event, rfl, pendingEvent_spec pending⟩

end Classification

section Membership

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- A canonical decision retained by the canonical menu, whose local envelope
the count verdict permits against the owner's earlier packets when it
transmits, lies in the one-packet menu. -/
theorem canonical_mem_onePacket (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (response : (application setup leaks).Action)
    (retained : response ∈ bounds.canonicalActions (runtime setup) leaks who past view)
    (permitted : ∀ material, response.transmission = some material →
      countPermits ((application setup leaks).outputs past)
        ((runtime setup).localEnvelope leaks who past view material) = true) :
    response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
  refine (bounds.mem_onePacketActions (runtime setup) leaks who past view response).mpr
    ⟨bounds.canonicalActions_effective (runtime setup) leaks who past view retained, ?_⟩
  cases sent : response.transmission with
  | none => exact Or.inl rfl
  | some material => exact Or.inr ⟨material, sent, permitted material sent⟩

end Membership

end Vegas

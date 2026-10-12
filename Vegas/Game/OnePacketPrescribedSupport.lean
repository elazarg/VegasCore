/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketTrembles

/-! # Support facts for prescribed play in the one-packet game

**Failed reveals.** A failed reveal persists under every source step
(`Vegas.SourceProgram.ProtocolState.revealFailed_step`), and whether a player's
reveal failed is the same at any two points every player, not only the owner,
observes alike (`Vegas.SourceProgram.ProtocolState.revealFailed_iff_of_observe_eq`):
publications are public. A failed reveal is paid
(`Vegas.SourceProgram.ProtocolState.failedReveals_pos_of_revealFailed`).

**As-if-honest support.** At a native state whose configuration decodes at its
completed prefix, as-if-honest play of the owner is the intended strategy at
the owner's view of the decoded point (`Vegas.asIfHonestProfile_observe`), so
its support is the image of that strategy's support
(`Vegas.mem_support_asIfHonestProfile_observe`), and every intended choice
there has positive probability when the assessment is fully mixed and the view
is an intended decision site (`Vegas.asIfHonestProfile_observe_pos`).

**Classification.** The pending event of a decision input is the owner's turn
event when its recall has not submitted for it (`Vegas.pendingEvent`). A first
activation is a decision input with a pending event at none of whose recalled
views that event was the owner's turn (`Vegas.FirstActivation`); a late
delivery has a pending event that was the owner's turn at some recalled view
(`Vegas.LateDelivery`). Both are functions of the information state, they
exclude each other, and every input with a pending event is one of them.

**Menu membership.** Every response in the support of the as-if-honest native
response is silence or the canonical decision of an encoded supported source
action (`Vegas.mem_support_honestResponse`). It lies in the one-packet menu as
soon as each of those canonical decisions does
(`Vegas.honestResponse_mem_onePacket`), which holds for a canonical decision
retained by the canonical menu whose local envelope the count verdict permits
(`Vegas.canonical_mem_onePacket`).

**Component factors.** A trembled component gives a main choice at least
`(1 - scale²)(1 - scale)` times its main mass, and an alternative choice at
least `(1 - scale²) scale` times its alternative mass; a choice outside the
main law has mass at most `scale² + scale`, and one outside both laws at most
`scale²` (`Vegas.trembledChoice_ge_main`, `Vegas.trembledChoice_ge_alternative`,
`Vegas.trembledChoice_le_of_main_zero`, `Vegas.trembledChoice_le_of_unprescribed`).
For a scale at most a quarter the main factor is at least `45/64`
(`Vegas.prescribedFactor_ge`). The prescribed component gives the choice of a
supported as-if-honest response at least that factor times its as-if-honest
mass (`Vegas.prescribedComponent_ge_honest`).
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

/-- A failed reveal is paid: every terminal store read from the point records a
failed reveal of its owner. -/
theorem failedReveals_pos_of_revealFailed (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (failed : RevealFailed who program state) {terminal : State L program.terminalCtx}
    (read : readout program state = some terminal) :
    1 ≤ failedReveals program who (publicOutcome program terminal) :=
  failedReveals_pos_of_indebted who program state (failed.indebted program state) read

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

/-- At a decoded state whose view is an intended decision site, a fully mixed
intended assessment gives every intended choice positive as-if-honest
probability. -/
theorem asIfHonestProfile_observe_pos (assessment : setup.intendedModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (who : Player) (execution : (application setup leaks).Execution) (rank : Nat)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup leaks).PlayerEntry)
    (site : setup.intendedModel.InformationSite who)
    (atSite : site.1 = setup.protocolObserve who (some point))
    (choice : setup.intendedModel.Choice who site.1) :
    choice.1 ∈ (asIfHonestProfile setup leaks assessment who
        (some (past, execution.observe (application setup leaks) who))).support := by
  rw [mem_support_asIfHonestProfile_observe setup leaks assessment who execution rank ordered
    point decoded past]
  obtain ⟨view, occurs⟩ := site
  subst atSite
  exact ⟨choice, mixed who ⟨_, occurs⟩ choice, rfl⟩

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

/-- **The as-if-honest native response.** At the owner's turn at `event`, every
response it supports is silence or the canonical decision of an encoded source
action that as-if-honest play supports. -/
theorem mem_support_honestResponse (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (response : (application setup leaks).Action)
    (supported : response ∈ (honestResponse setup leaks assessment who past view).support) :
    response = ⟨none⟩ ∨ ∃ action graphAction,
      some action ∈ (asIfHonestProfile setup leaks assessment who (some (past, view))).support ∧
      encodeEventAction? setup.program event action = some graphAction ∧
      response =
        (runtime setup).canonicalServiceDecision leaks who past view event graphAction := by
  unfold honestResponse at supported
  rw [turn] at supported
  obtain ⟨choice, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases choice with
  | none => exact Or.inl rfl
  | some action =>
      cases encoded : encodeEventAction? setup.program event action with
      | none =>
          left
          simp only [Option.bind_some, encoded]
      | some graphAction =>
          right
          refine ⟨action, graphAction, chosen, encoded, ?_⟩
          simp only [Option.bind_some, encoded]

/-- Away from the owner's turn the as-if-honest native response is silence. -/
theorem honestResponse_of_no_turn (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (turn : view.application.publicView.ownTurn? who = none) :
    honestResponse setup leaks assessment who past view = PMF.pure ⟨none⟩ := by
  unfold honestResponse
  rw [turn]

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

/-- **Menu membership of as-if-honest play.** At the owner's turn at `event`,
if the one-packet menu offers the canonical decision of every encoded source
action as-if-honest play supports, it offers every response of the
as-if-honest native response. -/
theorem honestResponse_mem_onePacket (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (offered : ∀ action graphAction,
      some action ∈ (asIfHonestProfile setup leaks assessment who (some (past, view))).support →
      encodeEventAction? setup.program event action = some graphAction →
      (runtime setup).canonicalServiceDecision leaks who past view event graphAction ∈
        bounds.onePacketActions (runtime setup) leaks who past view)
    (response : (application setup leaks).Action)
    (supported : response ∈ (honestResponse setup leaks assessment who past view).support) :
    response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
  rcases mem_support_honestResponse setup leaks assessment who past view event turn response
    supported with rfl | ⟨action, graphAction, chosen, encoded, rfl⟩
  · exact bounds.silence_onePacket (runtime setup) leaks who past view
  · exact offered action graphAction chosen encoded

end Membership

section Factors

/-- A point mass of a law is at most the mass of its image. -/
theorem le_map_apply {α β : Type} (law : PMF α) (f : α → β) (a : α) :
    law a ≤ law.map f (f a) := by
  classical
  rw [PMF.map_apply]
  exact (le_of_eq (by simp)).trans (ENNReal.le_tsum a)

private theorem toReal_mem_unit {α : Type} (law : PMF α) (a : α) :
    0 ≤ (law a).toReal ∧ (law a).toReal ≤ 1 :=
  ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one law a)⟩

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- A trembled component gives a choice at least `(1 - scale²)(1 - scale)`
times its main mass. -/
theorem trembledChoice_ge_main {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup leaks).Info)
    (main alternative :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :
    (1 - scale ^ 2) * (1 - scale) * (main choice).toReal ≤
      (trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who
        info main alternative choice).toReal := by
  rw [trembledChoice_apply_toReal]
  have := toReal_mem_unit ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy initial
    horizon scheduler who info) choice
  have := toReal_mem_unit alternative choice
  have square : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have : 0 ≤ (1 - scale ^ 2) * (scale * (alternative choice).toReal) := by positivity
  nlinarith [sq_nonneg scale]

/-- A trembled component gives a choice at least `(1 - scale²) scale` times its
alternative mass. -/
theorem trembledChoice_ge_alternative {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup leaks).Info)
    (main alternative :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :
    (1 - scale ^ 2) * scale * (alternative choice).toReal ≤
      (trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who
        info main alternative choice).toReal := by
  rw [trembledChoice_apply_toReal]
  have := toReal_mem_unit ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy initial
    horizon scheduler who info) choice
  have := toReal_mem_unit main choice
  have square : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have : 0 ≤ (1 - scale ^ 2) * ((1 - scale) * (main choice).toReal) := by
    have : 0 ≤ 1 - scale := by linarith
    positivity
  nlinarith [sq_nonneg scale]

/-- A choice outside the main law has mass at most `scale² + scale`. -/
theorem trembledChoice_le_of_main_zero {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup leaks).Info)
    (main alternative :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)
    (outside : main choice = 0) :
    (trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who
        info main alternative choice).toReal ≤ scale ^ 2 + scale := by
  rw [trembledChoice_apply_toReal, outside, ENNReal.toReal_zero]
  have uniform := toReal_mem_unit ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
    initial horizon scheduler who info) choice
  have other := toReal_mem_unit alternative choice
  have square : 0 ≤ scale ^ 2 := sq_nonneg scale
  have squareLe : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  nlinarith [mul_le_mul_of_nonneg_left uniform.2 square,
    mul_le_mul_of_nonneg_left other.2 nonnegative,
    mul_nonneg square (mul_nonneg nonnegative other.1)]

/-- A choice outside both the main and the alternative law has mass at most
`scale²`. -/
theorem trembledChoice_le_of_unprescribed {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup leaks).Info)
    (main alternative :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)
    (outsideMain : main choice = 0) (outsideAlternative : alternative choice = 0) :
    (trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who
        info main alternative choice).toReal ≤ scale ^ 2 := by
  rw [trembledChoice_apply_toReal, outsideMain, outsideAlternative, ENNReal.toReal_zero]
  have uniform := toReal_mem_unit ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
    initial horizon scheduler who info) choice
  nlinarith [mul_le_mul_of_nonneg_left uniform.2 (sq_nonneg scale)]

/-- For a scale at most a quarter, the main factor of a trembled component is at
least `45/64`. -/
theorem prescribedFactor_ge {scale : ℝ} (nonnegative : 0 ≤ scale) (small : scale ≤ 1 / 4) :
    45 / 64 ≤ (1 - scale ^ 2) * (1 - scale) := by
  have square : 15 / 16 ≤ 1 - scale ^ 2 := by nlinarith
  have linear : 3 / 4 ≤ 1 - scale := by linarith
  calc (45 / 64 : ℝ) = 15 / 16 * (3 / 4) := by norm_num
    _ ≤ (1 - scale ^ 2) * (1 - scale) :=
      mul_le_mul square linear (by norm_num) (by linarith)

/-- The choice of a response at a decision input has as-if-honest choice mass at
least the response's as-if-honest mass. -/
theorem honestChoice_ge (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action) :
    honestResponse setup leaks assessment who past view response ≤
      honestChoice setup leaks bounds initial horizon scheduler assessment who (some (past, view))
        (responseChoice setup leaks bounds initial horizon scheduler who (some (past, view))
          response) :=
  le_map_apply _ _ response

/-- **The prescribed factor.** The prescribed component gives the choice of a
response at least `(1 - scale²)(1 - scale)` times the response's as-if-honest
mass. -/
theorem prescribedComponent_ge_honest (assessment : setup.intendedModel.BehavioralAssessment)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action) :
    (1 - scale ^ 2) * (1 - scale) *
        (honestResponse setup leaks assessment who past view response).toReal ≤
      (prescribedComponent setup leaks bounds initial horizon scheduler assessment scale
        nonnegative le_one who (some (past, view))
        (responseChoice setup leaks bounds initial horizon scheduler who (some (past, view))
          response)).toReal := by
  refine le_trans ?_ (trembledChoice_ge_main setup leaks bounds initial horizon scheduler
    nonnegative le_one who _ _ _ _)
  have factor : 0 ≤ (1 - scale ^ 2) * (1 - scale) := by
    have : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
    have : 0 ≤ 1 - scale := by linarith
    nlinarith
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (honestChoice_ge setup leaks bounds initial horizon scheduler assessment who past view
      response)) factor

end Factors

end Vegas

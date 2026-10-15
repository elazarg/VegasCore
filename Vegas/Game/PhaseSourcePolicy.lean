/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryBindingComponent
import Vegas.Pending.PhaseOpeningPolicy
import Interaction.ReactiveMenuPolicy

/-! # Globally legal source-policy dispatch at phased physical inputs -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

open Classical in
private def requestedEvent (who : Player) (view : PhasePublicView (serviceGraph setup mode)) :
    Option (serviceGraph setup mode).EventId :=
  if offered : ∃ event, PhaseRuntimeState.requests view who ⟨view.attempt, event⟩ then
    some offered.choose else none

omit [Fintype Player] in
private theorem requestedEvent_of_request
    (state : PhaseRuntimeState (serviceGraph setup mode)) {inputs}
    (valid : state.Invariant inputs) (who : Player) (event : (serviceGraph setup mode).EventId)
    (request : state.SeedRequest who ⟨state.attempt, event⟩) :
    requestedEvent setup mode who state.publicView = some event := by
  classical
  have offered := (state.requests_publicView valid who ⟨state.attempt, event⟩).mpr request
  have possible : ∃ other, PhaseRuntimeState.requests state.publicView who
      ⟨state.publicView.attempt, other⟩ := ⟨event, offered⟩
  unfold requestedEvent
  rw [dite_eq_left possible]
  have selected := (state.requests_publicView valid who
    ⟨state.publicView.attempt, possible.choose⟩).mp possible.choose_spec
  have same := (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
    state.current.native.config.cut request.2.2.1 selected.2.2.1 request.2.2.2.1 selected.2.2.2.1
  exact congrArg some same

open Classical in
private def eventPolicyDispatch
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player)
    (event : (serviceGraph setup mode).EventId) : (phaseApplication runtime leaks).Policy :=
  match nodeView (serviceGraph setup mode) event with
  | .bind owner payload outputEq _ =>
      if owner = who then
        bindings owner event payload outputEq
      else fun _ _ => PMF.pure ⟨none⟩
  | .resolve owner payload binding _checks _outputEq _codeEq =>
      if owner = who then
        PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
          (fun _ _ => PMF.pure true)
      else fun _ _ => PMF.pure ⟨none⟩
  | .sample _ _ _ _ => fun _ _ => PMF.pure ⟨none⟩

private theorem eventPolicyDispatch_covered
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (covered : ∀ owner event payload binding past view response,
      response ∈ (bindings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (eventPolicyDispatch setup mode runtime leaks bounds bindings who event
      past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  cases node : nodeView (serviceGraph setup mode) event with
  | bind owner payload outputEq codeEq =>
      simp only [eventPolicyDispatch, node] at supported
      split at supported
      · rename_i same
        subst owner
        exact covered who event payload outputEq past view response supported
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [eventPolicyDispatch, node] at supported
      split at supported
      · rename_i same
        subst owner
        exact PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds who event payload binding
          (fun _ _ => PMF.pure true) past view response supported
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | sample payload law outputEq codeEq =>
      simp only [eventPolicyDispatch, node] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact PhaseCount.silence_onePacket runtime leaks bounds who past view

/-- The current public request selects the event. Binding choices use the supplied
local recipe; openings use canonical disclosure. Coverage follows from coverage
of the binding recipe; selecting the sites where it is pinned is separate. -/
def phasePolicyDispatch
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  match requestedEvent setup mode who view.application.2 with
  | none => PMF.pure ⟨none⟩
  | some event => eventPolicyDispatch setup mode runtime leaks bounds bindings who
      event past view

/-- Even malformed or unrealized inputs receive a law supported by the actual
bounded authenticated one-packet menu. -/
theorem phasePolicyDispatch_covered
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (covered : ∀ owner event payload binding past view response,
      response ∈ (bindings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phasePolicyDispatch setup mode runtime leaks bounds bindings who
      past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  unfold phasePolicyDispatch at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  · exact eventPolicyDispatch_covered setup mode runtime leaks bounds bindings covered who
      _ past view response supported

private theorem eventPolicyDispatch_binding
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload) :
    eventPolicyDispatch setup mode runtime leaks bounds bindings who event =
      bindings who event payload binding := by
  classical
  cases node : nodeView (serviceGraph setup mode) event with
  | bind owner actual outputEq codeEq =>
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj (outputEq.symm.trans binding)
      simp only [eventPolicyDispatch, node, ite_true]
  | resolve owner actual ref checks outputEq codeEq => cases outputEq.symm.trans binding
  | sample actual law outputEq codeEq => cases outputEq.symm.trans binding

/-- A genuine current request selects its actual binding branch, independently
of the choice made by the public selector on impossible inputs. -/
theorem phasePolicyDispatch_binding
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phasePolicyDispatch setup mode runtime leaks bounds bindings who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      bindings who event payload binding (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) := by
  have selected := requestedEvent_of_request setup mode execution.application valid who event
    request
  change (match requestedEvent setup mode who execution.application.publicView with
    | none => PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
    | some selected => eventPolicyDispatch setup mode runtime leaks bounds bindings
        who selected (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)) = _
  rw [selected]
  change eventPolicyDispatch setup mode runtime leaks bounds bindings who event
    (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) = _
  rw [eventPolicyDispatch_binding setup mode runtime leaks bounds bindings who event
    payload binding]

/-- Every genuine resolve request selects the canonical disclosure component;
no source opening-view decoder is used. -/
theorem phasePolicyDispatch_opening
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phasePolicyDispatch setup mode runtime leaks bounds bindings who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload binding
        (fun _ _ => PMF.pure true) (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) := by
  classical
  have selected := requestedEvent_of_request setup mode execution.application valid who event
    request
  unfold phasePolicyDispatch
  change (match requestedEvent setup mode who execution.application.publicView with
    | none => PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
    | some selected => eventPolicyDispatch setup mode runtime leaks bounds bindings
        who selected (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)) = _
  rw [selected]
  simp only [eventPolicyDispatch, nodeView_eq_resolve outputEq codeEq, ite_true]

/-- Copy the auxiliary source law at bindings and disclose canonically at openings. -/
def phaseSourcePolicy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player) :
    (phaseApplication runtime leaks).Policy :=
  phasePolicyDispatch setup mode runtime leaks bounds
    (fun owner event payload binding => phaseRecoveryBindingPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding) who

theorem phaseSourcePolicy_covered (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseSourcePolicy setup mode runtime leaks bounds wellFormed
      assessment who past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  exact phasePolicyDispatch_covered setup mode runtime leaks bounds
    (fun owner event payload binding => phaseRecoveryBindingPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding)
    (fun owner event payload binding past view response supported =>
      phaseRecoveryBindingPolicy_covered setup mode runtime leaks bounds wellFormed assessment
        owner event payload binding past view response supported) who past view response supported

theorem phaseSourcePolicy_binding (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed assessment who
        event payload binding (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) := by
  exact phasePolicyDispatch_binding setup mode runtime leaks bounds
    (fun owner event payload binding => phaseRecoveryBindingPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding)
    execution valid who event payload binding request

theorem phaseSourcePolicy_opening (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload binding
        (fun _ _ => PMF.pure true) (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) := by
  exact phasePolicyDispatch_opening setup mode runtime leaks bounds
    (fun owner event payload binding => phaseRecoveryBindingPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding)
    execution valid who event payload binding checks outputEq codeEq request

/-- The covered physical recipe has its exact finite-menu representation. -/
def phaseSourceStrategy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (who : Player) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial
      horizon scheduler).BehavioralPolicy who :=
  (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy initial horizon scheduler who
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who)

/-- Forgetting finite-menu witnesses recovers the complete physical law at
every input, without a fallback or a first-response wrapper. -/
theorem phaseSourceStrategy_map_val (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    ((phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
      scheduler who) (some (past, view))).map Subtype.val =
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        past view).map some := by
  exact (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy_map_val initial horizon
    scheduler who _ past view (fun response supported => phaseSourcePolicy_covered setup mode
      runtime leaks bounds wellFormed assessment who past view response supported)

end Vegas

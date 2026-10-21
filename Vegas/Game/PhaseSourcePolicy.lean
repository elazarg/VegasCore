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
def requestedEvent (who : Player) (view : PhasePublicView (serviceGraph setup mode)) :
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
def eventPolicyDispatch
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
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
        openings owner event payload binding
      else fun _ _ => PMF.pure ⟨none⟩
  | .sample _ _ _ _ => fun _ _ => PMF.pure ⟨none⟩

private theorem eventPolicyDispatch_covered
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (opened : ∀ owner event payload binding past view response,
      response ∈ (openings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view)
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
    (supported : response ∈ (eventPolicyDispatch setup mode runtime leaks openings bindings who
        event
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
        exact opened who event payload binding past view response supported
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | sample payload law outputEq codeEq =>
      simp only [eventPolicyDispatch, node] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact PhaseCount.silence_onePacket runtime leaks bounds who past view

/-- The current public request selects the event. Binding choices use the supplied
local recipe; openings use the supplied opening component. Coverage follows
from the two component families; selecting pinned sites is separate. -/
def phasePolicyDispatch
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  match requestedEvent setup mode who view.application.2 with
  | none => PMF.pure ⟨none⟩
  | some event => eventPolicyDispatch setup mode runtime leaks openings bindings who
      event past view

omit [Fintype Player] in
/-- The request dispatcher preserves equality of its actual component laws
at two recalls with the same current observation. -/
theorem phasePolicyDispatch_congr_input
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (who : Player) (first second : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (opened : ∀ owner event payload binding,
      openings owner event payload binding first view =
        openings owner event payload binding second view)
    (bound : ∀ owner event payload binding,
      bindings owner event payload binding first view =
        bindings owner event payload binding second view) :
    phasePolicyDispatch setup mode runtime leaks openings bindings who first view =
      phasePolicyDispatch setup mode runtime leaks openings bindings who second view := by
  unfold phasePolicyDispatch
  split
  · rfl
  · rename_i event _selected
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner payload outputEq codeEq =>
        simp only [eventPolicyDispatch, node]
        split
        · exact bound owner event payload outputEq
        · rfl
    | resolve owner payload binding checks outputEq codeEq =>
        simp only [eventPolicyDispatch, node]
        split
        · exact opened owner event payload binding
        · rfl
    | sample payload law outputEq codeEq => simp only [eventPolicyDispatch, node]

/-- Even malformed or unrealized inputs receive a law supported by the actual
bounded authenticated one-packet menu. -/
theorem phasePolicyDispatch_covered
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (opened : ∀ owner event payload binding past view response,
      response ∈ (openings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (covered : ∀ owner event payload binding past view response,
      response ∈ (bindings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phasePolicyDispatch setup mode runtime leaks openings bindings who
      past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  unfold phasePolicyDispatch at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  · exact eventPolicyDispatch_covered (opened := opened) setup mode runtime leaks bounds openings
      bindings covered who
      _ past view response supported

omit [Fintype Player] in
private theorem eventPolicyDispatch_binding
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload) :
    eventPolicyDispatch setup mode runtime leaks openings bindings who event =
      bindings who event payload binding := by
  classical
  cases node : nodeView (serviceGraph setup mode) event with
  | bind owner actual outputEq codeEq =>
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj (outputEq.symm.trans binding)
      simp only [eventPolicyDispatch, node, ite_true]
  | resolve owner actual ref checks outputEq codeEq => cases outputEq.symm.trans binding
  | sample actual law outputEq codeEq => cases outputEq.symm.trans binding

omit [Fintype Player] in
/-- A genuine current request selects its actual binding branch, independently
of the choice made by the public selector on impossible inputs. -/
theorem phasePolicyDispatch_binding
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phasePolicyDispatch setup mode runtime leaks openings bindings who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      bindings who event payload binding (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) := by
  have selected := requestedEvent_of_request setup mode execution.application valid who event
    request
  change (match requestedEvent setup mode who execution.application.publicView with
    | none => PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
    | some selected => eventPolicyDispatch setup mode runtime leaks openings bindings
        who selected (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)) = _
  rw [selected]
  change eventPolicyDispatch setup mode runtime leaks openings bindings who event
    (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) = _
  rw [eventPolicyDispatch_binding setup mode runtime leaks openings bindings who event
    payload binding]

omit [Fintype Player] in
/-- Every genuine resolve request selects its supplied opening component;
no source opening-view decoder is used. -/
theorem phasePolicyDispatch_opening
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
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
    phasePolicyDispatch setup mode runtime leaks openings bindings who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      openings who event payload binding (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) := by
  classical
  have selected := requestedEvent_of_request setup mode execution.application valid who event
    request
  unfold phasePolicyDispatch
  change (match requestedEvent setup mode who execution.application.publicView with
    | none => PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
    | some selected => eventPolicyDispatch setup mode runtime leaks openings bindings
        who selected (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)) = _
  rw [selected]
  simp only [eventPolicyDispatch, nodeView_eq_resolve outputEq codeEq, ite_true]

/-- Copy the auxiliary source law at bindings and disclose canonically at openings. -/
def phaseSourcePolicy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player) :
    (phaseApplication runtime leaks).Policy :=
  phasePolicyDispatch setup mode runtime leaks (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
      PMF.pure true))
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
  exact phasePolicyDispatch_covered (opened := (fun owner event payload binding past view response
      supported => PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner event payload
      binding (fun _ _ => PMF.pure true) past view response supported)) setup mode runtime leaks
      bounds (fun owner event payload binding => PhaseCount.phaseOpeningPolicy runtime leaks
      bounds owner event payload binding (fun _ _ => PMF.pure true))
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
  exact phasePolicyDispatch_binding setup mode runtime leaks (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
      PMF.pure true))
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
  exact phasePolicyDispatch_opening setup mode runtime leaks (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
      PMF.pure true))
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

/-- Every supported canonical binding transmission names a genuine current
request at its original callback. Count-token persistence alone would not imply
unfinishedness; the actual dispatcher selection supplies that fact. -/
theorem phaseSourcePolicy_request_of_binding_support (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseSourcePolicy setup mode runtime leaks bounds wellFormed
      assessment who (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who)).support)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (transmitted : response.transmission = some material)
    (event : (serviceGraph setup mode).EventId) (candidate : Handle (serviceGraph setup mode))
    (call : material.call.packet = .commitment event candidate) :
    execution.application.SeedRequest who ⟨execution.application.attempt, event⟩ := by
  classical
  unfold phaseSourcePolicy phasePolicyDispatch at supported
  change response ∈ (match requestedEvent setup mode who execution.application.publicView with
    | none => PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
    | some selected => eventPolicyDispatch setup mode runtime leaks (fun owner event payload
        binding => PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
        (fun _ _ => PMF.pure true))
        (fun owner event payload binding => phaseRecoveryBindingPolicy setup mode runtime leaks
          bounds wellFormed assessment owner event payload binding) who selected
          (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)).support at supported
  cases selected : requestedEvent setup mode who execution.application.publicView with
  | none =>
      rw [selected] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      cases transmitted
  | some selectedEvent =>
      rw [selected] at supported
      have request : execution.application.SeedRequest who
          ⟨execution.application.attempt, selectedEvent⟩ := by
        unfold requestedEvent at selected
        split at selected
        · rename_i offered
          have same := Option.some.inj selected
          have selectedRequest := (execution.application.requests_publicView valid who
            ⟨execution.application.publicView.attempt, offered.choose⟩).mp offered.choose_spec
          rwa [same] at selectedRequest
        · cases selected
      cases node : nodeView (serviceGraph setup mode) selectedEvent with
      | bind owner payload outputEq codeEq =>
          simp only [eventPolicyDispatch, node] at supported
          split at supported
          · rename_i same
            subst owner
            unfold phaseRecoveryBindingPolicy at supported
            split at supported
            · cases (PMF.mem_support_pure_iff _ _).mp supported
              cases transmitted
            · split at supported
              · dsimp only [phaseRecoveryBindingLaw] at supported
                obtain ⟨choice, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
                unfold phaseRecoveryBindingResponse at transmitted
                dsimp only at transmitted
                split at transmitted
                · cases transmitted
                · have sameMaterial := Option.some.inj transmitted
                  have sameCall := (congrArg (fun submitted : WitnessedSubmission
                    (serviceGraph setup mode) => submitted.call.packet) sameMaterial).trans call
                  have sameEvent := (Payload.commitment.inj sameCall).1
                  exact sameEvent ▸ request
              · cases (PMF.mem_support_pure_iff _ _).mp supported
                cases transmitted
          · cases (PMF.mem_support_pure_iff _ _).mp supported
            cases transmitted
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [eventPolicyDispatch, node] at supported
          split at supported
          · unfold PhaseCount.phaseOpeningPolicy at supported
            split at supported
            · dsimp only at supported
              split at supported
              · obtain ⟨disclose, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
                cases disclose
                · cases transmitted
                · have sameMaterial := Option.some.inj transmitted
                  have impossible := (congrArg (fun submitted : WitnessedSubmission
                    (serviceGraph setup mode) => submitted.call.packet) sameMaterial).trans call
                  cases impossible
              · cases (PMF.mem_support_pure_iff _ _).mp supported
                cases transmitted
            · cases (PMF.mem_support_pure_iff _ _).mp supported
              cases transmitted
          · cases (PMF.mem_support_pure_iff _ _).mp supported
            cases transmitted
      | sample payload law outputEq codeEq =>
          simp only [eventPolicyDispatch, node] at supported
          cases (PMF.mem_support_pure_iff _ _).mp supported
          cases transmitted


omit [Fintype Player] in
/-- Public request selection and a shared opening component preserve a binding
component's equality of supported response masses. No realized-input or
source-information correspondence is needed for this dispatcher fact. -/
theorem phasePolicyDispatch_apply_eq_of_support
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (first second : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (who : Player) (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (same : ∀ owner event payload binding,
      response ∈ (first owner event payload binding past view).support →
      response ∈ (second owner event payload binding past view).support →
        first owner event payload binding past view response =
          second owner event payload binding past view response)
    (left : response ∈ (phasePolicyDispatch setup mode runtime leaks openings first who past
      view).support)
    (right : response ∈ (phasePolicyDispatch setup mode runtime leaks openings second who past
      view).support) :
    phasePolicyDispatch setup mode runtime leaks openings first who past view response =
      phasePolicyDispatch setup mode runtime leaks openings second who past view response := by
  classical
  cases offered : requestedEvent setup mode who view.application.2 with
  | none => simp only [phasePolicyDispatch, offered]
  | some event =>
      simp only [phasePolicyDispatch, offered] at left right ⊢
      cases node : nodeView (serviceGraph setup mode) event with
      | bind owner payload binding code =>
          simp only [eventPolicyDispatch, node] at left right ⊢
          by_cases owned : owner = who
          · simp only [ite_eq_left owned] at left right ⊢
            exact same owner event payload binding left right
          · simp only [ite_eq_right owned]
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [eventPolicyDispatch, node]
      | sample payload law outputEq codeEq =>
          simp only [eventPolicyDispatch, node]


omit [Fintype Player] in
/-- A public request selects the same binding branch for every private member.
Every other dispatcher branch has one member-independent law. -/
theorem phasePolicyDispatch_indexed_cases {Index : Type}
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : Index → ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (who : Player) (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    (∃ law, ∀ index, phasePolicyDispatch setup mode runtime leaks openings (bindings index) who
      past view = law) ∨
    ∃ event payload, ∃ binding :
      (serviceGraph setup mode).outputLayout event = .binding who payload,
      ∀ index, phasePolicyDispatch setup mode runtime leaks openings (bindings index) who past
          view =
        bindings index who event payload binding past view := by
  classical
  cases offered : requestedEvent setup mode who view.application.2 with
  | none => exact Or.inl ⟨PMF.pure ⟨none⟩, fun _ => by
      simp only [phasePolicyDispatch, offered]⟩
  | some event =>
      cases node : nodeView (serviceGraph setup mode) event with
      | bind owner payload binding code =>
          by_cases owned : owner = who
          · subst owner
            exact Or.inr ⟨event, payload, binding, fun _ => by
              simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node, ite_true]⟩
          · exact Or.inl ⟨PMF.pure ⟨none⟩, fun _ => by
              simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node,
                ite_eq_right owned]⟩
      | resolve owner payload binding checks outputEq codeEq =>
          refine Or.inl ⟨if owner = who then openings owner event payload binding past view else
              PMF.pure ⟨none⟩,
            fun _ => ?_⟩
          simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node]
          split <;> rfl
      | sample payload law outputEq codeEq =>
          exact Or.inl ⟨PMF.pure ⟨none⟩, fun _ => by
            simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node]⟩

omit [Fintype Player] in
/-- Pointwise component domination passes through the SAME actual public
request dispatcher. Forced silence needs only that the retained mass is at
most one; no source query, reach, or qualification premise is involved. -/
theorem phasePolicyDispatch_probability_domination
    (firstOpen secondOpen : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (firstBind secondBind : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (factor : ℝ) (bounded : factor ≤ 1) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (openLower : ∀ owner event payload binding response,
      factor * (firstOpen owner event payload binding past view response).toReal ≤
        (secondOpen owner event payload binding past view response).toReal)
    (bindLower : ∀ owner event payload binding response,
      factor * (firstBind owner event payload binding past view response).toReal ≤
        (secondBind owner event payload binding past view response).toReal)
    (response : (phaseApplication runtime leaks).Action) :
    factor * (phasePolicyDispatch setup mode runtime leaks firstOpen firstBind who
      past view response).toReal ≤
      (phasePolicyDispatch setup mode runtime leaks secondOpen secondBind who
        past view response).toReal := by
  classical
  have silent : factor * ((PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action))
      response).toReal ≤ (PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
        response).toReal :=
    mul_le_of_le_one_left ENNReal.toReal_nonneg bounded
  cases offered : requestedEvent setup mode who view.application.2 with
  | none => simpa only [phasePolicyDispatch, offered] using silent
  | some event =>
      cases node : nodeView (serviceGraph setup mode) event with
      | bind owner payload binding code =>
          simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node]
          split
          · exact bindLower owner event payload binding response
          · exact silent
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node]
          split
          · exact openLower owner event payload binding response
          · exact silent
      | sample payload law outputEq codeEq =>
          simpa only [phasePolicyDispatch, offered, eventPolicyDispatch, node] using silent

end Vegas

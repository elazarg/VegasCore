/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhasePreparedBinding
import Vegas.Pending.ReactiveBinding
import Vegas.Pending.RecordedBindingReadback
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseSignedBindings
import Vegas.Pending.PhaseSolePacket
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseBindingSubmittedPreservation

/-! # Original authored binding meanings through physical phase recovery -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- An actual fresh binding declaration keeps its exact meaning through every
later raw operation, including exclusion, rollback and exhausted recovery. -/
theorem phase_recorded_binding_result (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some control))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (declared : entry.action = phaseBindingResponse runtime leaks who event payload result serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh) :
    control.execution.application.current.native.bindingResult (who, .prepared serial) payload =
      result := by
  let app := phaseApplication runtime leaks
  let property := fun execution : app.Execution =>
    ∀ who entry, entry ∈ execution.recall who → ∀ event payload result serial,
      entry.action = phaseBindingResponse runtime leaks who event payload result serial →
      entry.beforeView.application.1.candidates (.prepared serial) = .fresh →
      execution.application.current.native.candidates.lookup (who, .prepared serial) ≠ .fresh ∧
        execution.application.current.native.bindingResult (who, .prepared serial) payload = result
  have invariant : app.ServiceInvariant scheduler property := by
    constructor
    · intro execution who action valid observer entry retained event payload result serial
        declared fresh
      by_cases same : observer = who
      · subst observer
        have origin : entry ∈ execution.recall who ∨
            (entry.beforeView = execution.observe app who ∧ entry.action = action) := by
          rcases action with ⟨transmission⟩
          cases transmission <;>
            simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
              List.mem_singleton] at retained
          all_goals rcases retained with old | rfl
          all_goals first | exact Or.inl old | exact Or.inr ⟨rfl, rfl⟩
        rcases origin with old | ⟨viewed, chosen⟩
        · obtain ⟨fixed, meaning⟩ := valid who entry old event payload result serial declared fresh
          have stable := (phaseApplication_preservesFixedCandidates runtime leaks).respond
            execution who action (who, .prepared serial) fixed
          refine ⟨by rwa [stable], ?_⟩
          unfold State.bindingResult
          rw [stable]
          exact meaning
        · have actual : action = phaseBindingResponse runtime leaks who event payload result
              serial := chosen.symm.trans declared
          have freshState : execution.application.current.native.candidates.lookup
              (who, .prepared serial) = .fresh := by
            simpa only [viewed, ReactiveApplication.Execution.observe, phaseApplication,
              PhaseRuntimeState.playerView, State.playerView, app] using fresh
          rw [actual]
          refine ⟨?_, phaseBindingResponse_result runtime leaks execution who event payload result
            serial freshState⟩
          change (submitStep _ who (.commitment event (who, .prepared serial))).candidates.lookup
            (who, .prepared serial) ≠ .fresh
          exact submitStep_commitment_fixed _ who event (.prepared serial)
      · have old := app.respond_recall_other execution who observer same action
        obtain ⟨fixed, meaning⟩ := valid observer entry (old ▸ retained) event payload result serial
          declared fresh
        have stable := (phaseApplication_preservesFixedCandidates runtime leaks).respond
          execution who action (observer, .prepared serial) fixed
        refine ⟨by rwa [stable], ?_⟩
        unfold State.bindingResult
        rw [stable]
        exact meaning
    · intro execution next command valid _ reached observer entry retained event payload result
        serial declared fresh
      rw [app.environmentStep_recall execution next command reached] at retained
      obtain ⟨fixed, meaning⟩ := valid observer entry retained event payload result serial
        declared fresh
      have stable := (phaseApplication_preservesFixedCandidates runtime leaks).environmentStep
        execution next command reached (observer, .prepared serial) fixed
      exact ⟨by rwa [stable], by simpa only [State.bindingResult, stable] using meaning⟩
  exact ((invariant.history initial horizon (fun _ _ who entry member =>
    (List.not_mem_nil member).elim) trace) who entry retained event payload result serial
      declared fresh).2

end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- A completed binding on a clear history accepted the sole packet authored
for that event. A remembered SEND therefore determines its exact handle, even
after its original phase has advanced. -/
theorem accepted_binding_of_recorded_completed (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (P).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (declared : entry.action = phaseBindingResponse runtime leaks who event payload result serial)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed) :
    control.execution.application.current.native.accepted (.inr event) =
      some (who, .prepared serial) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have coverage := (phaseFailureCoverage_history runtime leaks plan inputs horizon
    scheduler raw).active
  have records := (phaseBindingRecord_history runtime leaks plan inputs horizon
    scheduler raw).active
  have inputRecall := (P).history_inputRecall initial horizon scheduler raw
  have present : ∃ candidate,
      control.execution.application.current.native.accepted (.inr event) = some candidate := by
    cases accepted : control.execution.application.current.native.accepted (.inr event) with
    | some candidate => exact ⟨candidate, rfl⟩
    | none =>
        have missed := (control.execution.application.current.native.publicView_missedBinding
          event who payload binding).mpr ⟨completed, accepted⟩
        have excluded := coverage.covered event who
          (graph.actor?_of_outputLayout_binding binding) (Or.inl missed)
        simp only [clear, Finset.notMem_empty] at excluded
  obtain ⟨candidate, accepted⟩ := present
  obtain ⟨actualPayload, typed⟩ := records.accepted_typed (.inr event) candidate accepted
  change graph.outputLayout event = .binding candidate.1 actualPayload at typed
  have ownerEq : candidate.1 = who := (EventField.binding.inj (binding.symm.trans typed)).1.symm
  obtain ⟨other, otherOutput, otherSender, otherCall⟩ :=
    (phaseSignedBindings_history runtime leaks plan inputs horizon scheduler raw).2.1.2
      event candidate accepted
  rw [ownerEq] at otherOutput otherSender
  obtain ⟨message, emitted, sender, sent⟩ := PhaseCount.recalled_submission_emitted runtime leaks
    initial horizon scheduler raw who entry retained _ (by rw [declared]; rfl)
  have output : message ∈ (P).outputs (control.execution.recall who) :=
    List.mem_filterMap.mpr ⟨entry, retained, emitted⟩
  have named : message.payload.packet.call = .commitment event (who, .prepared serial) := sent
  have mappedOutput (packet : Message Player (CommitAttemptPacket graph))
      (member : packet ∈ (P).outputs (control.execution.recall who)) :
      Message.mapPayload CommitAttemptPacket.packet packet ∈
        (N).outputs ((execution runtime leaks plan control.execution).recall who) := by
    rw [show (execution runtime leaks plan control.execution).recall who =
      (control.execution.recall who).map (playerEntry runtime leaks plan) from rfl, outputs]
    exact List.mem_map.mpr ⟨packet, member, rfl⟩
  have identifiers := output_identifiers_eq_of_clear runtime leaks plan bounds inputs horizon
    scheduler trace clear who (Message.mapPayload CommitAttemptPacket.packet message)
      (Message.mapPayload CommitAttemptPacket.packet other) (mappedOutput message output)
      (mappedOutput other otherOutput) (sender.trans otherSender.symm) event
      (by change message.payload.packet.call.event? graph = _; rw [named]; rfl)
      (by change other.payload.packet.call.event? graph = _; rw [otherCall]; rfl)
  have inputOf (packet : Message Player (CommitAttemptPacket graph))
      (member : packet ∈ (P).outputs (control.execution.recall who)) :
      packet ∈ control.execution.network.inputs := by
    rw [← inputRecall who] at member
    exact (List.mem_filter.mp member).1
  have same := (P).input_identifier_injective_history initial horizon scheduler control raw
    message other (inputOf message output) (inputOf other otherOutput) identifiers
  have handleEq : candidate = (who, .prepared serial) := by
    rw [same, otherCall] at named
    exact (Payload.commitment.inj named).2
  simpa only [handleEq] using accepted

/-- The action in the actual completed graph history is exactly the result of
its original authored fresh binding response. Native reachability and accepted
association are derived from this same initialized clear phase history. -/
theorem completed_binding_action_of_recorded (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (P).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (declared : entry.action = phaseBindingResponse runtime leaks who event payload result serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed) :
    ∃ original : graph.Action event,
      ⟨event, original⟩ ∈ control.execution.application.current.native.config.history ∧
      cast (congrArg EventField.Action binding) original = result := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨draw, valid⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler raw
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨original, recorded, meaning⟩ := bindings.active.completed_binding_action
    valid.active.reachable event who payload binding completed
  have accepted := accepted_binding_of_recorded_completed runtime leaks plan bounds inputs horizon
    scheduler trace clear who event payload binding result serial entry retained declared completed
  rw [accepted, Option.elim_some] at meaning
  exact ⟨original, recorded, meaning.trans (phase_recorded_binding_result runtime leaks _ horizon
    scheduler ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace)
      who event payload result serial entry retained declared fresh)⟩

end Vegas.EventGraphRuntime.PhaseNativeProjection

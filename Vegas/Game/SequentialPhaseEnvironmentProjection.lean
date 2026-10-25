/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryInformation
import Vegas.Game.SequentialPhaseEnvironment
import Vegas.Game.SequentialPhaseHandle
import Interaction.MessageNetworkMapOperations
import Interaction.ReactiveTrafficIdentity

/-! # Physical inclusion and application kernels under phase erasure -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

private theorem includePending_of_handle (current : (P).Execution) (identity : MessageId Player)
    (handles : ∀ message ∈ current.network.pending,
      ((P).handle current.application message).map PhaseRuntimeState.current =
        (R).handle current.application.current (Message.mapPayload CommitAttemptPacket.packet
          message)) :
    execution runtime leaks recoveryLeaks (current.includePending (P) identity) =
      (execution runtime leaks recoveryLeaks current).includePending (R) identity := by
  have projectedLookup : (execution runtime leaks recoveryLeaks current).network.lookup identity =
      (current.network.lookup identity).map (Message.mapPayload CommitAttemptPacket.packet) :=
    MessageNetwork.mapPayload_lookup _ _ _
  cases found : current.network.lookup identity with
  | none =>
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        projectedLookup, found, Option.map_none]
  | some message =>
      have handled := handles message (List.mem_of_find?_eq_some found)
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        projectedLookup, found, Option.map_some]
      dsimp only [execution]
      cases outcome : (P).handle current.application message with
      | none =>
          have rejected : (R).handle current.application.current
              (Message.mapPayload CommitAttemptPacket.packet message) = none := by
            simpa only [outcome, Option.map_none] using handled.symm
          simp only [rejected, Option.getD_none, Option.isSome_none,
            MessageNetwork.mapPayload, List.map_append, List.map_singleton,
            MessagePool.removeFirst_mapPayload]
      | some next =>
          have accepted : (R).handle current.application.current
              (Message.mapPayload CommitAttemptPacket.packet message) = some next.current := by
            simpa only [outcome, Option.map_some] using handled.symm
          simp only [accepted, Option.getD_some, Option.isSome_some,
            MessageNetwork.mapPayload, List.map_append, List.map_singleton,
            MessagePool.removeFirst_mapPayload]

/-- Waiting retains the entire projected execution and records the same scheduler input. -/
theorem environmentStep_wait (current : (P).Execution) :
    (current.environmentStep (P) .wait).map (execution runtime leaks recoveryLeaks) =
      (execution runtime leaks recoveryLeaks current).environmentStep (R) .wait := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, execution,
    List.map_append, List.map_cons, List.map_nil]
  rfl

end PhaseRecoveryProjection

namespace PhaseRecoveryProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph.sequentialize)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph.sequentialize))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

/-- Every actual application command projects with its full native chance law,
physical network, player recall, receipts and appended scheduler entry. -/
theorem environmentStep_application_history
    (plan : RuntimePhasePlan graph.sequentialize)
    (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    {control : (P).Control}
    (trace : ((P).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (operation : EnvironmentCommand graph.sequentialize) :
    (control.execution.environmentStep (P) (.application operation)).map
        (execution runtime leaks recoveryLeaks) =
      (execution runtime leaks recoveryLeaks control.execution).environmentStep (R)
        (.application operation) := by
  have law := phase_environment_current_sequential_history runtime leaks plan singletons inputs
    horizon scheduler trace operation
  let update : RecoveryState graph.sequentialize → (R).Execution := fun next =>
    { execution runtime leaks recoveryLeaks control.execution with
      application := next
      environmentRecall :=
        (execution runtime leaks recoveryLeaks control.execution).environmentRecall ++
          [⟨(execution runtime leaks recoveryLeaks control.execution).observeEnvironment (R),
            .application operation⟩] }
  calc
    _ = ((control.execution.application.environment runtime operation).map
        PhaseRuntimeState.current).map update := by
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp,
        Function.comp_def]
      congr 1
      funext next
      simp only [execution, List.map_append, List.map_cons, List.map_nil, update]
      rfl
    _ = (control.execution.application.current.environment runtime operation).map update := by
      rw [law]
    _ = _ := by
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp,
        Function.comp_def]
      rfl

variable [Fintype Player]

/-- Pending inclusion on an actual clear counted history retains the complete
original forced-exit effect, including rejected receipts and automatic cascades. -/
theorem includePending_clear_onePacket_history
    (plan : RuntimePhasePlan graph.sequentialize)
    (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (bounds : MessageBounds graph.sequentialize)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (identity : MessageId Player) :
    execution runtime leaks recoveryLeaks (control.execution.includePending (P) identity) =
      (execution runtime leaks recoveryLeaks control.execution).includePending (R) identity := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have retained := (P).retained_envelopes_mem_inputs control.execution
    ((P).history_provenance initial horizon scheduler rawTrace)
    ((P).history_inputRecall initial horizon scheduler rawTrace)
  apply includePending_of_handle runtime leaks recoveryLeaks control.execution identity
  intro message pending
  exact phase_handle_current_sequential_clear_onePacket_history runtime leaks plan singletons
    bounds inputs horizon scheduler trace clear message (retained.pending message pending)

/-- Physical inclusion also appends the exact projected scheduler entry. -/
theorem environmentStep_include_clear_onePacket_history
    (plan : RuntimePhasePlan graph.sequentialize)
    (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (bounds : MessageBounds graph.sequentialize)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (identity : MessageId Player) :
    (control.execution.environmentStep (P) (.include identity)).map
        (execution runtime leaks recoveryLeaks) =
      (execution runtime leaks recoveryLeaks control.execution).environmentStep (R)
        (.include identity) := by
  have included := includePending_clear_onePacket_history runtime leaks recoveryLeaks plan
    singletons bounds inputs horizon scheduler trace clear identity
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  change PMF.pure (execution runtime leaks recoveryLeaks
      { control.execution.includePending (P) identity with
        environmentRecall := control.execution.environmentRecall ++
          [⟨control.execution.observeEnvironment (P), .include identity⟩] }) = _
  have record : execution runtime leaks recoveryLeaks
      { control.execution.includePending (P) identity with
        environmentRecall := control.execution.environmentRecall ++
          [⟨control.execution.observeEnvironment (P), .include identity⟩] } =
      { (execution runtime leaks recoveryLeaks control.execution).includePending (R) identity with
        environmentRecall :=
          (execution runtime leaks recoveryLeaks control.execution).environmentRecall ++
            [⟨(execution runtime leaks recoveryLeaks control.execution).observeEnvironment (R),
              .include identity⟩] } := by
    rw [← included]
    simp only [execution, List.map_append, List.map_cons, List.map_nil]
    rfl
  rw [record]

end PhaseRecoveryProjection
end Vegas.EventGraphRuntime

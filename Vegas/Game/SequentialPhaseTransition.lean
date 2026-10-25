/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryResponse
import Vegas.Game.PhaseRecoveryActivation
import Vegas.Game.SequentialPhaseEnvironmentProjection
import Vegas.Game.SequentialPhaseSchedulerInformation
import Vegas.Pending.PhaseBindingCountTransport

/-! # Exact transition kernels before singleton phase exclusion

Complete option-control states project through the actual scheduler and every
physical command branch. First-exclusion successor states remain in the kernel;
no successor archive is decoded and no service contract is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks

/-- Retain the actual control rank and actor while erasing phase execution metadata. -/
def protocolState : (P).ProtocolState → (R).ProtocolState :=
  Option.map (control runtime leaks recoveryLeaks)

/-- Every optional response retains its identical authenticated submission material. -/
def jointActions (joint : Player → Option (P).Action) : Player → Option (R).Action :=
  fun who => (joint who).map (action runtime leaks recoveryLeaks)

end PhaseRecoveryProjection

namespace PhaseRuntimeState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Initial sequential normalization retains the original empty-exclusion recovery state. -/
theorem initial_current_sequential {graph : Vegas.EventGraph Player L}
    (plan : RuntimePhasePlan graph.sequentialize) (inputs : graph.sequentialize.Inputs) :
    (initial plan inputs).current =
      (⟨State.initial inputs, ∅⟩ : RecoveryState graph.sequentialize) :=
  (settle_current_eq_drain_sequential plan.phases 0 _ _ [] rfl
    (initial_checkpoint_frontier plan inputs)).trans (RecoveryState.drain_eq_of_empty _ rfl)

end PhaseRuntimeState

namespace PhaseRecoveryProjection

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "projection" => protocolState runtime leaks recoveryLeaks
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks

/-- All actual command branches commute with the complete execution projection. -/
theorem environmentStep_projected_clear_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (operation : (P).Command) :
    (control.execution.environmentStep (P) operation).map
        (execution runtime leaks recoveryLeaks) =
      (execution runtime leaks recoveryLeaks control.execution).environmentStep (R)
        (command runtime leaks recoveryLeaks operation) := by
  cases operation with
  | activate who =>
      exact activate_projected_history runtime leaks plan bounds inputs horizon scheduler trace
        clear
        who
  | «include» identity =>
      exact environmentStep_include_clear_onePacket_history runtime leaks recoveryLeaks plan
        (sequentialRuntimePhasePlan_singleton program) bounds inputs horizon scheduler trace clear
        identity
  | application operation =>
      exact environmentStep_application_history runtime leaks recoveryLeaks plan
        (sequentialRuntimePhasePlan_singleton program) inputs horizon scheduler
        ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace) operation
  | wait => exact environmentStep_wait runtime leaks recoveryLeaks control.execution

omit [Fintype Player] in
/-- The original initial draw projects exactly, before any physical scheduler decision. -/
theorem transition_projected_initial
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) (joint : Player → Option (P).Action) :
    ((P).transition (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler none joint).map
        projection =
      (R).transition (inputs.map fun input => (⟨State.initial input, ∅⟩ : RecoveryState _)) horizon
        (recoveryScheduler scheduler) none (jointActions runtime leaks recoveryLeaks joint) := by
  simp only [ReactiveApplication.transition, PMF.map_comp, Function.comp_def]
  congr 1
  funext input
  simp only [protocolState, Option.map_some, control, execution,
    ReactiveApplication.Execution.initial]
  rw [PhaseRuntimeState.initial_current_sequential]
  rfl

/-- Every actual clear counted prefix has the exact old recovery one-step law,
including first-exclusion endpoints and arbitrary admitted private preparations. -/
theorem transition_projected_clear_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {current : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (joint : Player → Option (P).Action)
    (admitted : ∀ who, current.actor = some who → (joint who).getD ⟨none⟩ ∈
      PhaseCount.onePacketActions runtime leaks bounds who (current.execution.recall who)
        (current.execution.observe (P) who)) :
    ((P).transition (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
        (some current) joint).map projection =
      (R).transition (inputs.map fun input => (⟨State.initial input, ∅⟩ : RecoveryState _)) horizon
        (recoveryScheduler scheduler) (projection (some current))
        (jointActions runtime leaks recoveryLeaks joint) := by
  cases acting : current.actor with
  | some who =>
      have member := admitted who acting
      have response := respond_of_allows runtime leaks recoveryLeaks current.execution who
        ((joint who).getD ⟨none⟩) (by
          intro material transmitted
          obtain ⟨_raw, silent | ⟨actual, sent, permitted⟩⟩ :=
            (PhaseCount.mem_onePacketActions runtime leaks bounds who _ _ _).mp member
          · rw [silent] at transmitted
            cases transmitted
          · have same : actual = material := Option.some.inj (sent.symm.trans transmitted)
            subst actual
            exact (PhaseBindingRepair.localEnvelope_admitted runtime leaks current.execution who
              material ((PhaseCount.permits_eq_true_iff _ _).mp permitted).1).1)
      simp only [ReactiveApplication.transition, acting, protocolState, Option.map_some, control,
        PMF.pure_map]
      cases chosen : joint who <;>
        simp only [jointActions, chosen, Option.map_none, Option.map_some, Option.getD_none,
          Option.getD_some, action] at response ⊢
      all_goals rw [response]
  | none =>
      cases remaining : current.remaining with
      | zero =>
          simp only [ReactiveApplication.transition, acting, remaining, protocolState,
            Option.map_some, control, PMF.pure_map]
      | succ remaining =>
          have schedule := SequentialPhaseSchedulerInformation.scheduler_history program runtime
            leaks recoveryLeaks bounds inputs horizon scheduler trace clear
          simp only [ReactiveApplication.transition, acting, remaining, protocolState,
            Option.map_some, control]
          rw [schedule, PMF.map_bind, PMF.bind_map]
          congr 1
          funext operation
          have step := environmentStep_projected_clear_history program runtime leaks bounds inputs
            horizon scheduler trace clear operation
          dsimp only [Function.comp_apply]
          rw [← step, PMF.map_comp, PMF.map_comp]
          congr 1
          funext next
          cases operation <;> rfl

end PhaseRecoveryProjection
end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseRecoveryPolicy
import Interaction.ReactiveLocalContinuation

/-! # Actual behavioral one-step laws before singleton phase exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))
  (included : menu.IncludedIn (PhaseCount.onePacketMenu runtime leaks bounds))
  (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "phaseInitial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "recoveryInitial" =>
  inputs.map (fun input => RecoveryState.mk (State.initial input) ∅)
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks scheduler
local notation "M" =>
  ReactiveApplication.ResponseMenu.information (menu) phaseInitial horizon scheduler
local notation "N" =>
  ReactiveApplication.information (R) recoveryInitial horizon recoveryScheduler
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks recoveryLeaks
local notation "projectAction" => PhaseRecoveryProjection.action runtime leaks recoveryLeaks

include included in
/-- The derived behavioral callback has the exact mapped counted law at every
actual clear player information fiber, including inactive observations. -/
theorem behavioralPolicy_history_map_val (who : Player) (original : (M).BehavioralPolicy who)
    {control : (P).Control}
    (trace : ((menu).protocol phaseInitial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    (behavioralPolicy program runtime leaks menu inputs horizon scheduler who original
      ((R).observe who (projection (some control)))).map Subtype.val =
      (original ((P).observe who (some control))).map
        (fun choice => choice.1.map projectAction) := by
  rw [behavioralPolicy_map_val]
  unfold PhaseRecoveryProjection.protocolState
  rw [PhaseRecoveryProjection.observe_state,
    SequentialPhasePlayerInformation.information_history program runtime leaks recoveryLeaks bounds
      inputs horizon scheduler (included.trace phaseInitial horizon scheduler trace) clear who]

omit [Fintype Player] in
private theorem singleton_joint (who : Player) (response : (P).Action) :
    PhaseRecoveryProjection.jointActions runtime leaks recoveryLeaks
      (fun observer => if observer = who then some response else none) =
      fun observer => if observer = who then some (projectAction response) else none := by
  funext observer
  by_cases same : observer = who <;>
    simp only [PhaseRecoveryProjection.jointActions, same, ↓reduceIte, Option.map_none,
      Option.map_some]

include included in
/-- Complete physical control kernels agree under the actually decoded profile.
All responses in every source counted menu remain available. -/
theorem controlStep_history
    (profile : ∀ who, (M).BehavioralPolicy who) {state : (P).ProtocolState}
    (trace : ((menu).protocol phaseInitial horizon scheduler).Trace state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
        state.current.excluded = ∅) state) :
    ((P).controlStep phaseInitial horizon scheduler
      ((menu).decodeProfile phaseInitial horizon scheduler profile) state).map projection =
      (R).controlStep recoveryInitial horizon recoveryScheduler
        (fun who => policy program runtime leaks
          ((menu).decodeProfile phaseInitial horizon scheduler profile who))
        (projection state) := by
  cases state with
  | none =>
      exact PhaseRecoveryProjection.transition_projected_initial program runtime leaks inputs
        horizon scheduler (fun _ => none)
  | some current =>
      cases acting : current.actor with
      | none =>
          have compared := PhaseRecoveryProjection.transition_projected_clear_history program
            runtime leaks bounds inputs horizon scheduler
            (included.trace phaseInitial horizon scheduler trace) clear (fun _ => none) (by
              intro who active
              rw [acting] at active
              cases active)
          simpa only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            PhaseRecoveryProjection.protocolState, Option.map_some,
            PhaseRecoveryProjection.control,
            Option.bind_some, acting, ReactiveApplication.transition]
            using compared
      | some who =>
          have callbacks := policy_history program runtime leaks menu bounds included
            inputs horizon scheduler
            ((menu).decodeProfile phaseInitial horizon scheduler profile who) trace clear who
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            PhaseRecoveryProjection.protocolState, Option.map_some,
            PhaseRecoveryProjection.control,
            Option.bind_some, acting]
          rw [callbacks, PMF.bind_map, PMF.map_bind]
          apply bind_congr_on_support
          intro response supported
          have member := (menu).decode_embedPolicy_covered phaseInitial horizon scheduler who
            (profile who) _ _ response supported
          have countedMember := included who _ _ member
          change response ∈ PhaseCount.onePacketActions runtime leaks bounds who
            (current.execution.recall who) (current.execution.observe (P) who) at countedMember
          have compared := PhaseRecoveryProjection.transition_projected_clear_history program
            runtime leaks bounds inputs horizon scheduler
            (included.trace phaseInitial horizon scheduler trace) clear
            (fun observer => if observer = who then some response else none) (by
              intro other active
              have same : other = who := Option.some.inj (active.symm.trans acting)
              subst other
              simpa only [↓reduceIte, Option.getD_some] using countedMember)
          rw [singleton_joint] at compared
          simpa only [PhaseRecoveryProjection.protocolState, Option.map_some,
            PhaseRecoveryProjection.control, acting, Function.comp_apply] using compared

include included in
/-- Every actual clear phase history and any matching recovery raw history have the
same entire physical one-step state law, including first-exclusion endpoints. -/
theorem run_one_map_state_history
    (profile : ∀ who, (M).BehavioralPolicy who)
    (first : ((menu).protocol phaseInitial horizon scheduler).History)
    (second : ((R).protocol recoveryInitial horizon recoveryScheduler).History)
    (same : projection first.state = second.state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState ((toEventGraph program).withMode .sequential) =>
        state.current.excluded = ∅) first.state) :
    ((M).runBehavioralFrom profile 1 first).map (fun next => projection next.state) =
      ((N).runBehavioralFrom
        (fun who => behavioralPolicy program runtime leaks menu inputs horizon scheduler who
          (profile who)) 1 second).map History.state := by
  have rawLaw : ((N).runBehavioralFrom
        (fun who => behavioralPolicy program runtime leaks menu inputs horizon scheduler who
          (profile who)) 1 second).map History.state =
      (R).controlStep recoveryInitial horizon recoveryScheduler
        (fun who => policy program runtime leaks
          ((menu).decodeProfile phaseInitial horizon scheduler profile who)) second.state := by
    unfold behavioralPolicy
    rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (N)
      ((R).singleMover recoveryInitial horizon recoveryScheduler), (R).run_map_state]
    simp only [Function.iterate_one, PMF.pure_bind]
    rfl
  rw [rawLaw, ← same, ← controlStep_history program runtime leaks menu bounds included
    inputs horizon scheduler
    profile first.trace clear]
  have mapped := congrArg (PMF.map projection)
    ((menu).run_map_controlSteps phaseInitial horizon scheduler profile 1 first)
  rw [PMF.map_comp] at mapped
  simpa only [Function.comp_def, Function.iterate_one, PMF.pure_bind] using mapped

end Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy

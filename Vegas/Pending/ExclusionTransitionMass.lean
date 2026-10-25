/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionClearStepMass
import Vegas.Pending.ExclusionClearHistory

/-! # Actual reactive transition probabilities before exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem liftProtocolState_injective : Function.Injective (liftProtocolState runtime leaks) :=
  Function.LeftInverse.injective (protocolState_liftProtocolState runtime leaks)

private theorem environment_control_lift_apply
    (current : (runtime.reactiveApplication leaks).Execution)
    (valid : ExclusionEvidence 0 ∅ (⟨current.application, ∅⟩ : RecoveryState graph))
    (remaining : Nat) (chosen : (runtime.reactiveApplication leaks).Command)
    (after : (runtime.reactiveApplication leaks).ProtocolState)
    (clear : ∀ control, after = some control →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState graph)) :
    (((liftExecution runtime leaks current).environmentStep (runtime.recoveryApplication leaks)
        (liftCommand runtime leaks chosen)).map fun next =>
          some (⟨remaining, (liftCommand runtime leaks chosen).actor?
            (runtime.recoveryApplication leaks), next⟩ :
              (runtime.recoveryApplication leaks).Control))
              (liftProtocolState runtime leaks after) =
      ((current.environmentStep (runtime.reactiveApplication leaks) chosen).map fun next =>
        some (⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩ :
          (runtime.reactiveApplication leaks).Control)) after := by
  classical
  have actorEq : (liftCommand runtime leaks chosen).actor? (runtime.recoveryApplication leaks) =
      chosen.actor? (runtime.reactiveApplication leaks) := by cases chosen <;> rfl
  by_cases supported : after ∈
      ((current.environmentStep (runtime.reactiveApplication leaks) chosen).map fun next =>
        some (⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩ :
          (runtime.reactiveApplication leaks).Control)).support
  · rw [PMF.mem_support_map_iff] at supported
    obtain ⟨next, nextSupported, rfl⟩ := supported
    have oldInjective : Function.Injective (fun next =>
        some (⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩ :
          (runtime.reactiveApplication leaks).Control)) := by
      intro first second same
      exact congrArg ReactiveApplication.Control.execution (Option.some.inj same)
    have newInjective : Function.Injective (fun next =>
        some (⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩ :
          (runtime.recoveryApplication leaks).Control)) := by
      intro first second same
      exact congrArg ReactiveApplication.Control.execution (Option.some.inj same)
    rw [actorEq]
    simp only [liftProtocolState, Option.map_some, liftControl]
    rw [pmf_map_apply_of_injective _ newInjective,
      pmf_map_apply_of_injective _ oldInjective]
    exact environmentStep_lift_apply runtime leaks current next valid chosen (clear _ rfl)
  · have absent : liftProtocolState runtime leaks after ∉
        (((liftExecution runtime leaks current).environmentStep
          (runtime.recoveryApplication leaks) (liftCommand runtime leaks chosen)).map fun next =>
            some (⟨remaining, (liftCommand runtime leaks chosen).actor?
              (runtime.recoveryApplication leaks), next⟩ :
                (runtime.recoveryApplication leaks).Control)).support := by
      intro present
      rw [PMF.mem_support_map_iff] at present
      obtain ⟨next, nextSupported, same⟩ := present
      have empty := liftProtocolState_clear runtime leaks after _ same.symm
      have projected := environmentStep_projected_support runtime leaks
        (liftExecution runtime leaks current) next (liftCommand runtime leaks chosen)
        rfl empty nextSupported
      rw [execution_liftExecution, command_liftCommand] at projected
      apply supported
      rw [PMF.mem_support_map_iff]
      refine ⟨execution runtime leaks next, projected, ?_⟩
      have mapped := congrArg (protocolState runtime leaks) same
      rw [protocolState_liftProtocolState] at mapped
      change some (⟨remaining, (liftCommand runtime leaks chosen).actor?
        (runtime.recoveryApplication leaks), execution runtime leaks next⟩ :
          (runtime.reactiveApplication leaks).Control) = after at mapped
      rw [actorEq] at mapped
      exact mapped
    rw [(PMF.apply_eq_zero_iff _ _).mpr absent, (PMF.apply_eq_zero_iff _ _).mpr supported]

/-- At every publicly clear target, actual native and recovery reactive
transition masses agree. The comparison scheduler is the projected recovery
scheduler evaluated at the complete clear lift of its inputs. -/
theorem transition_lift_apply (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (before after : (runtime.reactiveApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (valid : ∀ current, before = some current →
      ExclusionEvidence 0 ∅ (⟨current.execution.application, ∅⟩ : RecoveryState graph))
    (clear : ∀ current, after = some current →
      ExclusionEvidence 0 ∅ (⟨current.execution.application, ∅⟩ : RecoveryState graph)) :
    ((runtime.recoveryApplication leaks).transition initial horizon scheduler
        (liftProtocolState runtime leaks before) (liftJointActions runtime leaks joint))
        (liftProtocolState runtime leaks after) =
      ((runtime.reactiveApplication leaks).transition (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) before joint) after := by
  classical
  cases before with
  | none =>
    have law : (runtime.recoveryApplication leaks).transition initial horizon scheduler
        (liftProtocolState runtime leaks none) (liftJointActions runtime leaks joint) =
        ((runtime.reactiveApplication leaks).transition (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) none joint).map
            (liftProtocolState runtime leaks) := by
      simp only [liftProtocolState, Option.map_none, ReactiveApplication.transition,
        PMF.map_comp, Function.comp_def]
      apply map_congr_on_support
      intro state supported
      obtain ⟨inputs, rfl⟩ := initialized state supported
      rfl
    rw [law, pmf_map_apply_of_injective _ (liftProtocolState_injective runtime leaks)]
  | some current =>
    rcases current with ⟨remaining, actor, current⟩
    cases actor with
    | some who =>
      have law : (runtime.recoveryApplication leaks).transition initial horizon scheduler
          (liftProtocolState runtime leaks (some ⟨remaining, some who, current⟩))
          (liftJointActions runtime leaks joint) =
          ((runtime.reactiveApplication leaks).transition
            (initial.map RecoveryState.native) horizon
            (nativeScheduler runtime leaks scheduler) (some ⟨remaining, some who, current⟩)
            joint).map (liftProtocolState runtime leaks) := by
        cases chosen : joint who <;>
          simp only [liftProtocolState, Option.map_some, liftControl,
            ReactiveApplication.transition,
            liftJointActions, chosen, Option.map_none, Option.getD_none, Option.getD_some,
            PMF.pure_map, respond_lift]
        exact congrArg (fun execution => PMF.pure
          (some (⟨remaining, none, execution⟩ :
            (runtime.recoveryApplication leaks).Control)))
          (respond_lift runtime leaks current who ⟨none⟩)
      rw [law, pmf_map_apply_of_injective _ (liftProtocolState_injective runtime leaks)]
    | none =>
      cases remaining with
      | zero =>
        change (PMF.pure (liftProtocolState runtime leaks
          (some ⟨0, none, current⟩))) (liftProtocolState runtime leaks after) =
          (PMF.pure (some ⟨0, none, current⟩)) after
        rw [← PMF.pure_map (liftProtocolState runtime leaks),
          pmf_map_apply_of_injective _ (liftProtocolState_injective runtime leaks)]
      | succ remaining =>
        change ((scheduler (liftExecution runtime leaks current).environmentRecall
          ((liftExecution runtime leaks current).observeEnvironment
            (runtime.recoveryApplication leaks))).bind fun chosen =>
              ((liftExecution runtime leaks current).environmentStep
                (runtime.recoveryApplication leaks) chosen).map fun next =>
                  some (⟨remaining, chosen.actor? (runtime.recoveryApplication leaks), next⟩ :
                    (runtime.recoveryApplication leaks).Control))
                    (liftProtocolState runtime leaks after) = _
        change _ = (((scheduler
          (current.environmentRecall.map (liftEnvironmentEntry runtime leaks))
          (liftEnvironmentView runtime leaks
            (current.observeEnvironment (runtime.reactiveApplication leaks)))).map
            (command runtime leaks)).bind fun chosen =>
              (current.environmentStep (runtime.reactiveApplication leaks) chosen).map fun next =>
                some (⟨remaining, chosen.actor? (runtime.reactiveApplication leaks), next⟩ :
                  (runtime.reactiveApplication leaks).Control)) after
        rw [PMF.bind_map, PMF.bind_apply, PMF.bind_apply]
        apply tsum_congr
        intro chosen
        have matched := environment_control_lift_apply runtime leaks current (valid _ rfl)
          remaining (command runtime leaks chosen) after clear
        rw [liftCommand_command] at matched
        exact congrArg (fun mass => scheduler
          (liftExecution runtime leaks current).environmentRecall
          ((liftExecution runtime leaks current).observeEnvironment
            (runtime.recoveryApplication leaks)) chosen * mass) matched

end Vegas.EventGraphRuntime.RecoveryProjection

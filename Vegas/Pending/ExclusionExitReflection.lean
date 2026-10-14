/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.EqualMassFibers
import Vegas.Pending.ExclusionPairedTransition
import Vegas.Pending.ExclusionTransitionMass

/-! # Reflection of public-clear outcomes in actual transition couplings -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Exact masses of clear native atoms rule out crossed residual mass in a
coupling of actual transitions. Thus a public-clear native outcome has exactly
its empty-exclusion recovery lift as counterpart. -/
theorem paired_transition_clear_reflection
    (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (current : (runtime.recoveryApplication leaks).Control)
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some current)) (empty : current.execution.application.excluded = ∅)
    (joint : Player → Option (runtime.recoveryApplication leaks).Action)
    (paired : PMF ((runtime.reactiveApplication leaks).ProtocolState ×
      (runtime.recoveryApplication leaks).ProtocolState))
    (firstMarginal : paired.map Prod.fst = (runtime.reactiveApplication leaks).transition
      (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
      (some (control runtime leaks current)) (jointActions runtime leaks joint))
    (secondMarginal : paired.map Prod.snd = (runtime.recoveryApplication leaks).transition
      initial horizon scheduler (some current) joint)
    (forward : ∀ pair ∈ paired.support,
      (∀ next, pair.2 = some next → next.execution.application.excluded = ∅) →
      pair.1 = protocolState runtime leaks pair.2)
    (pair) (supported : pair ∈ paired.support)
    (clear : ∀ next, pair.1 = some next →
      PublicExclusionRecord (⟨next.execution.application, ∅⟩ : RecoveryState graph)) :
    pair.2 = liftProtocolState runtime leaks pair.1 := by
  have currentClear : ∀ next, (some current : (runtime.recoveryApplication leaks).ProtocolState) =
      some next → next.execution.application.excluded = ∅ := by
    intro next same
    cases Option.some.inj same
    exact empty
  have valid := nativeHistory_record runtime leaks initial initialized horizon scheduler trace
    currentClear
  have beforeEq := liftProtocolState_protocolState_of_history_clear runtime leaks initial horizon
    scheduler trace currentClear
  have mass := transition_lift_apply runtime leaks initial initialized horizon scheduler
    (protocolState runtime leaks (some current)) pair.1 (jointActions runtime leaks joint) valid
    clear
  rw [beforeEq, liftJointActions_jointActions] at mass
  apply fiber_reflection_of_equal_map_mass paired Prod.fst Prod.snd pair.1
    (liftProtocolState runtime leaks pair.1) ?_ ?_ pair supported rfl
  · intro other member lifted
    have otherClear : ∀ next, other.2 = some next → next.execution.application.excluded = ∅ := by
      rw [lifted]
      exact liftProtocolState_clear runtime leaks pair.1
    have same := forward other member otherClear
    rwa [lifted, protocolState_liftProtocolState] at same
  · rw [firstMarginal, secondMarginal]
    exact mass.symm

/-- The concrete actual-transition coupling can always be chosen with both
clear-outcome directions; no excluded recovery branch can accompany a clear native atom. -/
theorem exists_paired_transition_clear_reflection
    (initial : PMF (RecoveryState graph))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (current : (runtime.recoveryApplication leaks).Control)
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some current)) (empty : current.execution.application.excluded = ∅)
    (joint : Player → Option (runtime.recoveryApplication leaks).Action) :
    ∃ paired : PMF ((runtime.reactiveApplication leaks).ProtocolState ×
        (runtime.recoveryApplication leaks).ProtocolState),
      paired.map Prod.fst = (runtime.reactiveApplication leaks).transition
        (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
        (some (control runtime leaks current)) (jointActions runtime leaks joint) ∧
      paired.map Prod.snd = (runtime.recoveryApplication leaks).transition initial horizon scheduler
        (some current) joint ∧
      (∀ pair ∈ paired.support,
        (∀ next, pair.2 = some next → next.execution.application.excluded = ∅) →
        pair.1 = protocolState runtime leaks pair.2) ∧
      ∀ pair ∈ paired.support,
        (∀ next, pair.1 = some next →
          PublicExclusionRecord (⟨next.execution.application, ∅⟩ : RecoveryState graph)) →
        pair.2 = liftProtocolState runtime leaks pair.1 := by
  obtain ⟨paired, first, second, forward⟩ := exists_paired_transition runtime leaks initial horizon
    scheduler current trace empty joint
  exact ⟨paired, first, second, forward,
    paired_transition_clear_reflection runtime leaks initial initialized horizon scheduler current
      trace empty joint paired first second forward⟩

end Vegas.EventGraphRuntime.RecoveryProjection

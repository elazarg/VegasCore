/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionTransitionMass
import Vegas.Pending.ExclusionNativeProfile
import GameTheoryExtensions.Analysis.Protocol.ReachBounds

/-! # Exact behavioral reach before public exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph))
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
  (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeModel" => ReactiveApplication.information
  (reactiveApplication runtime leaks) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler

/-- The two real step coefficients agree at paired clear histories under the
concrete profile evaluated at clear native information. -/
theorem stepProb_recoveryTrace
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    {before after : (runtime.reactiveApplication leaks).ProtocolState}
    (prior : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler runtime leaks scheduler)).Trace before)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (legal : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler runtime leaks scheduler)).Legal before joint)
    (valid : ∀ current, before = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph))
    (clear : ∀ current, after = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)) :
    (RecoveryModel).stepProb profile
        (recoveryTrace runtime leaks initial initialized horizon scheduler prior valid)
        ⟨liftJointActions runtime leaks joint,
          liftJointActions_legal runtime leaks initial horizon scheduler before joint legal⟩
        (liftProtocolState runtime leaks after) =
      (NativeModel).stepProb (nativeProfile runtime leaks initial horizon scheduler profile)
        prior ⟨joint, legal⟩ after := by
  rw [InformationModel.stepProb, InformationModel.stepProb,
    InformationModel.behavioralJoint_prob_eq_prod,
    InformationModel.behavioralJoint_prob_eq_prod]
  apply congrArg₂ (fun first second : ℝ => first * second)
  · apply Finset.prod_congr rfl
    intro who _member
    have newVal := pmf_map_apply_of_injective
      (profile who ((RecoveryModel).infoOf who
        (recoveryTrace runtime leaks initial initialized horizon scheduler prior valid)))
      Subtype.val_injective
      ((RecoveryModel).choicesOfLegal
        (recoveryTrace runtime leaks initial initialized horizon scheduler prior valid)
        ⟨liftJointActions runtime leaks joint,
          liftJointActions_legal runtime leaks initial horizon scheduler before joint legal⟩ who)
    have oldVal := pmf_map_apply_of_injective
      (nativeProfile runtime leaks initial horizon scheduler profile who
        ((NativeModel).infoOf who prior)) Subtype.val_injective
      ((NativeModel).choicesOfLegal prior ⟨joint, legal⟩ who)
    rw [← newVal, ← oldVal]
    have info := infoOf_recoveryHistory runtime leaks initial initialized horizon scheduler
      ⟨before, prior⟩ valid who
    change (RecoveryModel).infoOf who
        (recoveryTrace runtime leaks initial initialized horizon scheduler prior valid) =
      liftInformation runtime leaks ((NativeModel).infoOf who prior) at info
    change (fun input => (((profile who input).map Subtype.val)
        (liftJointActions runtime leaks joint who)).toReal)
        ((RecoveryModel).infoOf who
          (recoveryTrace runtime leaks initial initialized horizon scheduler prior valid)) = _
    rw [info]
    exact congrArg ENNReal.toReal (nativeProfile_option_apply runtime leaks initial horizon
      scheduler profile who ((NativeModel).infoOf who prior) (joint who)).symm
  · exact congrArg ENNReal.toReal (transition_lift_apply runtime leaks initial initialized horizon
      scheduler before after joint valid clear)

omit [Fintype Player] in
private theorem native_initialized
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph)) :
    ∀ native ∈ (initial.map RecoveryState.native).support, ∃ inputs,
      native = State.initial inputs := by
  intro native supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨state, sourceSupported, rfl⟩ := supported
  obtain ⟨inputs, rfl⟩ := initialized state sourceSupported
  exact ⟨inputs, rfl⟩

/-- Exact real reach weights follow by multiplying the paired local choice
and actual transition masses along the complete realized trace. -/
theorem historyReachWeight_recoveryHistory_toReal
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who) :
    ∀ {state} (trace : ((runtime.reactiveApplication leaks).protocol
        (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)).Trace state)
      (clear : ∀ current, state = some current →
        PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)),
      ((RecoveryModel).historyReachWeight profile
        (recoveryHistory runtime leaks initial initialized horizon scheduler ⟨state, trace⟩
          clear)).toReal =
      ((NativeModel).historyReachWeight
        (nativeProfile runtime leaks initial horizon scheduler profile) ⟨state, trace⟩).toReal := by
  intro state trace
  induction trace with
  | start =>
    intro _clear
    change ((RecoveryModel).historyReachWeight profile
      ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).initHistory).toReal =
      ((NativeModel).historyReachWeight
        (nativeProfile runtime leaks initial horizon scheduler profile)
        ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler)).initHistory).toReal
    rw [InformationModel.historyReachWeight_initHistory,
      InformationModel.historyReachWeight_initHistory]
  | @extend before after prior joint legal realized ih =>
    intro clear
    have valid := native_clear_before_transition runtime leaks (initial.map RecoveryState.native)
      (native_initialized initial initialized) horizon (nativeScheduler runtime leaks scheduler)
      prior joint realized clear
    change ((RecoveryModel).historyReachWeight profile
      ⟨_, .extend (recoveryTrace runtime leaks initial initialized horizon scheduler prior valid)
        (liftJointActions runtime leaks joint) _ _⟩).toReal = _
    rw [InformationModel.historyReachProbability_extend,
      InformationModel.historyReachProbability_extend,
      stepProb_recoveryTrace runtime leaks initial initialized horizon scheduler profile prior
        joint legal valid clear]
    exact congrArg (fun weight => weight *
      (NativeModel).stepProb (nativeProfile runtime leaks initial horizon scheduler profile)
        prior ⟨joint, legal⟩ after) (ih valid)

/-- A publicly clear native history and its actual recovery lift have exactly
the same behavioral reach weight. -/
theorem historyReachWeight_recoveryHistory
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    {state : (runtime.reactiveApplication leaks).ProtocolState}
    (trace : ((runtime.reactiveApplication leaks).protocol
      (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)).Trace
        state)
    (clear : ∀ current, state = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)) :
    (RecoveryModel).historyReachWeight profile
        (recoveryHistory runtime leaks initial initialized horizon scheduler ⟨state, trace⟩ clear) =
      (NativeModel).historyReachWeight
        (nativeProfile runtime leaks initial horizon scheduler profile) ⟨state, trace⟩ := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  exact historyReachWeight_recoveryHistory_toReal runtime leaks initial initialized horizon
    scheduler profile trace clear

include initialized in
/-- Projecting an actual clear recovery history preserves its exact reach
weight under the concrete native profile. -/
theorem historyReachWeight_nativeHistory
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (history : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    (RecoveryModel).historyReachWeight profile history =
      (NativeModel).historyReachWeight
        (nativeProfile runtime leaks initial horizon scheduler profile)
        (nativeHistory runtime leaks initial horizon scheduler history clear) := by
  have paired := historyReachWeight_recoveryHistory runtime leaks initial initialized horizon
    scheduler profile (nativeTrace runtime leaks initial horizon scheduler history.trace clear)
    (nativeHistory_record runtime leaks initial initialized horizon scheduler history.trace clear)
  change (RecoveryModel).historyReachWeight profile
      (recoveryHistory runtime leaks initial initialized horizon scheduler
        (nativeHistory runtime leaks initial horizon scheduler history clear)
        (nativeHistory_record runtime leaks initial initialized horizon scheduler
          history.trace clear)) = _ at paired
  rw [recoveryHistory_nativeHistory] at paired
  exact paired

/-- The actual bijection of complete information fibers preserves every
history's reach weight, including histories with zero reach. -/
theorem informationHistoryEquiv_reachWeight
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (who : Player) (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (valid : PublicExclusionRecord (⟨reference.execution.application, ∅⟩ : RecoveryState graph))
    (history : (RecoveryModel).InformationHistory who (liftInformation runtime leaks
      ((runtime.reactiveApplication leaks).observe who (some reference)))) :
    (RecoveryModel).historyReachWeight profile history.1 =
      (NativeModel).historyReachWeight
        (nativeProfile runtime leaks initial horizon scheduler profile)
        ((informationHistoryEquiv runtime leaks initial initialized horizon scheduler who
          reference active valid) history).1 := by
  have observed := history.2
  simp only [ReactiveApplication.information, ReactiveApplication.info] at observed
  have clear := informationFiber_clear runtime leaks who reference active history.1.state observed
  change (RecoveryModel).historyReachWeight profile history.1 =
    (NativeModel).historyReachWeight
      (nativeProfile runtime leaks initial horizon scheduler profile)
      (nativeHistory runtime leaks initial horizon scheduler history.1 clear)
  exact historyReachWeight_nativeHistory runtime leaks initial initialized horizon scheduler
    profile history.1 clear

end Vegas.EventGraphRuntime.RecoveryProjection

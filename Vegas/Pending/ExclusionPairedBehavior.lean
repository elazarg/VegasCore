/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPairedTransition
import Vegas.Pending.ExclusionNativeProfile
import Vegas.Pending.ExclusionExitReflection
import GameTheoryExtensions.Math.Probability.Support

/-! # Coupling actual behavioral steps before exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeModel" => ReactiveApplication.information (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.information
  (recoveryApplication runtime leaks)
  initial horizon scheduler
local notation "NativeProtocol" => ReactiveApplication.protocol (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "RecoveryProtocol" => ReactiveApplication.protocol
  (recoveryApplication runtime leaks)
  initial horizon scheduler

/-- Projecting an actually legal recovery joint response gives the legal native
joint response at the projected state. -/
def projectedJoint (before : (RecoveryProtocol).State)
    (draw : { joint // (RecoveryProtocol).Legal before joint }) :
    { joint // (NativeProtocol).Legal (protocolState runtime leaks before) joint } :=
  ⟨jointActions runtime leaks draw.1,
    jointActions_legal runtime leaks initial horizon scheduler before draw.1 draw.2⟩

/-- The actual behavioral joint law, including legality, commutes with projection
at a clear history under the concrete native comparison profile. -/
theorem behavioralJoint_nativeHistory
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (history : (RecoveryProtocol).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (running : ¬ (RecoveryProtocol).terminal history.state) :
    ((RecoveryModel).behavioralJoint profile history.trace running).map
        (projectedJoint runtime leaks initial horizon scheduler history.state) =
      (NativeModel).behavioralJoint
        (nativeProfile runtime leaks initial horizon scheduler profile)
        (nativeHistory runtime leaks initial horizon scheduler history clear).trace
        (fun stopped => running ((terminal_protocolState runtime leaks history.state).mp
          stopped)) := by
  classical
  have info who :
      (RecoveryModel).infoOf who history.trace = liftInformation runtime leaks
        ((NativeModel).infoOf who
          (nativeHistory runtime leaks initial horizon scheduler history clear).trace) := by
    simp only [ReactiveApplication.information, ReactiveApplication.info]
    change (runtime.recoveryApplication leaks).observe who history.state =
      liftInformation runtime leaks ((runtime.reactiveApplication leaks).observe who
        (protocolState runtime leaks history.state))
    rw [← observe_lift, liftProtocolState_protocolState_of_history_clear runtime leaks initial
      horizon scheduler history.trace clear]
  have erased :
      (((RecoveryModel).behavioralJoint profile history.trace running).map
          (projectedJoint runtime leaks initial horizon scheduler history.state)).map Subtype.val =
        ((NativeModel).behavioralJoint
          (nativeProfile runtime leaks initial horizon scheduler profile)
          (nativeHistory runtime leaks initial horizon scheduler history clear).trace
          (fun stopped => running ((terminal_protocolState runtime leaks history.state).mp
            stopped))).map Subtype.val := by
    rw [PMF.map_comp]
    have composition : Subtype.val ∘
        projectedJoint runtime leaks initial horizon scheduler history.state =
        jointActions runtime leaks ∘ Subtype.val := rfl
    rw [composition, ← PMF.map_comp]
    change (((RecoveryModel).behavioralJoint profile history.trace running).map Subtype.val).map
      (jointActions runtime leaks) = _
    rw [InformationModel.behavioralJoint_map_val, InformationModel.behavioralJoint_map_val]
    change (independentProduct fun who => (profile who
      ((RecoveryModel).infoOf who history.trace)).map Subtype.val).map
        (fun draw who => (draw who).map (action runtime leaks)) = _
    rw [independentProduct_map]
    congr 1
    funext who
    rw [nativeProfile_map_val, info who]
  ext draw
  exact (pmf_map_apply_of_injective _ Subtype.val_injective draw).symm.trans
    ((congrArg (fun law => law draw.1) erased).trans
      (pmf_map_apply_of_injective _ Subtype.val_injective draw))

/-- Couple the two complete one-step history laws. Outcomes that first introduce
exclusion remain in both marginals; every clear outcome retains the exact
projected endpoint. No continuation agreement after exclusion is assumed. -/
theorem exists_paired_behavioralStep
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (history : (RecoveryProtocol).History)
    (current : (runtime.recoveryApplication leaks).Control)
    (state : history.state = some current) (empty : current.execution.application.excluded = ∅)
    (running : ¬ (RecoveryProtocol).terminal history.state) :
    let clear := fun next (same : history.state = some next) =>
      (Option.some.inj (state.symm.trans same)) ▸ empty
    let native := nativeHistory runtime leaks initial horizon scheduler history clear
    ∃ paired : PMF ((NativeProtocol).History × (RecoveryProtocol).History),
      paired.map Prod.fst = (NativeModel).runBehavioralFrom
        (nativeProfile runtime leaks initial horizon scheduler profile) 1 native ∧
      paired.map Prod.snd = (RecoveryModel).runBehavioralFrom profile 1 history ∧
      ∀ next ∈ paired.support,
        (∀ nextClear : ∀ control, next.2.state = some control →
            control.execution.application.excluded = ∅,
          next.1 = nativeHistory runtime leaks initial horizon scheduler next.2 nextClear) ∧
        ((∀ control, next.1.state = some control →
            PublicExclusionRecord (⟨control.execution.application, ∅⟩ : RecoveryState graph)) →
          ∀ control, next.2.state = some control → control.execution.application.excluded = ∅) := by
  classical
  intro clear native
  let draws := (RecoveryModel).behavioralJoint profile history.trace running
  let project := projectedJoint runtime leaks initial horizon scheduler history.state
  have nativeRunning : ¬ (NativeProtocol).terminal native.state :=
    fun stopped => running ((terminal_protocolState runtime leaks history.state).mp stopped)
  have coupled draw := exists_paired_transition_clear_reflection runtime leaks initial initialized
    horizon scheduler current (state ▸ history.trace) empty draw
  let kernel := fun draw : { joint // (RecoveryProtocol).Legal history.state joint } =>
    Classical.choose (coupled draw.1)
  have marginal (draw : { joint // (RecoveryProtocol).Legal history.state joint }) :=
    Classical.choose_spec (coupled draw.1)
  have first draw : (kernel draw).map Prod.fst =
      (NativeProtocol).step native.state (project draw) := by
    change (kernel draw).map Prod.fst = (runtime.reactiveApplication leaks).transition
      (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
      (protocolState runtime leaks history.state) (jointActions runtime leaks draw.1)
    exact (marginal draw).1.trans (congrArg
      (fun before => (runtime.reactiveApplication leaks).transition
        (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
        (protocolState runtime leaks before) (jointActions runtime leaks draw.1)) state).symm
  have second draw : (kernel draw).map Prod.snd =
      (RecoveryProtocol).step history.state draw := by
    change (kernel draw).map Prod.snd = (runtime.recoveryApplication leaks).transition
      initial horizon scheduler history.state draw.1
    exact (marginal draw).2.1.trans (congrArg
      (fun before => (runtime.recoveryApplication leaks).transition initial horizon scheduler
        before draw.1) state).symm
  let extend := fun draw (pair : (NativeProtocol).State × (RecoveryProtocol).State)
      (supported : pair ∈ (kernel draw).support) =>
    (native.extend (target := pair.1) (project draw).2 (by
        have reached : pair.1 ∈ ((kernel draw).map Prod.fst).support := by
          rw [PMF.mem_support_map_iff]
          exact ⟨pair, supported, rfl⟩
        exact (first draw) ▸ reached),
      history.extend (target := pair.2) draw.2 (by
        have reached : pair.2 ∈ ((kernel draw).map Prod.snd).support := by
          rw [PMF.mem_support_map_iff]
          exact ⟨pair, supported, rfl⟩
        exact (second draw) ▸ reached))
  let paired := draws.bind fun draw => (kernel draw).bindOnSupport fun pair supported =>
    PMF.pure (extend draw pair supported)
  refine ⟨paired, ?_, ?_, ?_⟩
  · rw [(NativeModel).runBehavioralFrom_succ_of_not_terminal _ 0 nativeRunning,
      ← behavioralJoint_nativeHistory runtime leaks initial horizon scheduler profile history
        clear running, PMF.bind_map]
    change (draws.bind _).map Prod.fst = draws.bind _
    rw [PMF.map_bind]
    apply bind_congr_on_support
    intro draw _supported
    trans ((kernel draw).map Prod.fst).bindOnSupport
      (fun next supported => PMF.pure (native.extend (project draw).2
        ((first draw) ▸ supported)))
    · rw [bindOnSupport_map, map_bindOnSupport]
      apply bindOnSupport_congr
      intro pair supported
      rw [PMF.pure_map]
    · apply bindOnSupport_congr_measure (first draw)
      intro next _first _second
      rfl
  · rw [(RecoveryModel).runBehavioralFrom_succ_of_not_terminal _ 0 running]
    change (draws.bind _).map Prod.snd = draws.bind _
    rw [PMF.map_bind]
    apply bind_congr_on_support
    intro draw _supported
    trans ((kernel draw).map Prod.snd).bindOnSupport
      (fun next supported => PMF.pure (history.extend draw.2
        ((second draw) ▸ supported)))
    · rw [bindOnSupport_map, map_bindOnSupport]
      apply bindOnSupport_congr
      intro pair supported
      rw [PMF.pure_map]
    · apply bindOnSupport_congr_measure (second draw)
      intro next _first _second
      rfl
  · intro next supported
    rw [PMF.mem_support_bind_iff] at supported
    obtain ⟨draw, _drawn, supported⟩ := supported
    rw [PMF.mem_support_bindOnSupport_iff] at supported
    obtain ⟨pair, member, supported⟩ := supported
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp supported
    constructor
    · intro nextClear
      exact StateSymmetry.history_extend_congr rfl rfl
        ((marginal draw).2.2.1 pair member nextClear)
    · intro nativeClear control same
      have lifted := (marginal draw).2.2.2 pair member nativeClear
      exact liftProtocolState_clear runtime leaks pair.1 control (lifted.symm.trans same)

end Vegas.EventGraphRuntime.RecoveryProjection

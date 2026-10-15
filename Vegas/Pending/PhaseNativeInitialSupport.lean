/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePolicyRun
import Interaction.ReactiveInitialSupport

/-! # Pointwise initialized native laws at supported original draws -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- The original all-history premises apply to each supported initial draw. -/
theorem controlLaw_projection_of_supported_input (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (players : Player → (P).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (safe : ∀ (current : (P).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (input : graph.Inputs) (supported : input ∈ inputs.support)
    (fuel : Nat) :
    ((fun law => law.bind ((P).controlStep ((PMF.pure input).map (PhaseRuntimeState.initial plan))
      horizon scheduler players))^[fuel] (PMF.pure none)).map
        (protocolState runtime leaks plan) =
      (fun law => law.bind ((N).controlStep ((PMF.pure input).map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)
        (fun who => nativePolicy runtime leaks plan (players who))))^[fuel] (PMF.pure none) := by
  have included : ((PMF.pure input).map (PhaseRuntimeState.initial plan)).support ⊆
      (inputs.map (PhaseRuntimeState.initial plan)).support := by
    rw [PMF.support_map, PMF.support_map]
    apply Set.image_mono
    intro value present
    have same := (PMF.mem_support_pure_iff input value).mp present
    subst value
    exact supported
  have restrictedSafe : ∀ (current : (P).Control)
      (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((PMF.pure input).map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅ := by
    intro current trace faithful
    exact safe current ((PhaseCount.onePacketMenu runtime leaks
      bounds).trace_of_initial_support_subset
       _ _ included horizon scheduler trace) faithful
  exact controlLaw_projection runtime leaks plan bounds ordered maximal (PMF.pure input)
    horizon scheduler players covered restrictedSafe fuel


/-- The original all-history premises apply to each supported initial draw. -/
theorem exists_paired_control_run_of_supported_input (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (players : Player → (P).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (safe : ∀ (current : (P).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (input : graph.Inputs) (supported : input ∈ inputs.support)
    (fuel : Nat) :
    ∃ paired : PMF ((N).ProtocolState × (P).ProtocolState),
      paired.map Prod.fst = (fun law => law.bind ((N).controlStep ((PMF.pure input).map
    State.initial)
        horizon (nativeScheduler runtime leaks plan scheduler)
        (fun who => nativePolicy runtime leaks plan (players who))))^[fuel] (PMF.pure none) ∧
      paired.map Prod.snd = (fun law => law.bind ((P).controlStep
        ((PMF.pure input).map (PhaseRuntimeState.initial plan)) horizon scheduler players))^[fuel]
          (PMF.pure none) ∧
      ∀ pair ∈ paired.support,
        pair.1 = protocolState runtime leaks plan pair.2 ∧
        PairedPublicRecord runtime leaks plan pair.1 pair.2 := by
  have included : ((PMF.pure input).map (PhaseRuntimeState.initial plan)).support ⊆
      (inputs.map (PhaseRuntimeState.initial plan)).support := by
    rw [PMF.support_map, PMF.support_map]
    apply Set.image_mono
    intro value present
    have same := (PMF.mem_support_pure_iff input value).mp present
    subst value
    exact supported
  have restrictedSafe : ∀ (current : (P).Control)
      (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((PMF.pure input).map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅ := by
    intro current trace faithful
    exact safe current ((PhaseCount.onePacketMenu runtime leaks
      bounds).trace_of_initial_support_subset
       _ _ included horizon scheduler trace) faithful
  exact exists_paired_control_run runtime leaks plan bounds ordered maximal (PMF.pure input)
    horizon scheduler players covered restrictedSafe fuel


/-- The original all-history premises apply to each supported initial draw. -/
theorem native_controlLaw_eq_of_local_agreement_of_supported_input (bounds : MessageBounds graph)
  (ordered : graph.RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
  (players : Player → (P).Policy) (nativePlayers : Player → (N).Policy)
  (covered : ∀ (who : Player) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (response : (P).Action), response ∈ (players who past view).support →
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
  (safe : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    (∀ who, (players who).Consistent (current.execution.recall who)) →
      current.execution.application.current.excluded = ∅)
  (agreement : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    current.execution.application.current.excluded = ∅ →
    (∀ who, (players who).Consistent (current.execution.recall who)) →
    (∀ who, (nativePlayers who).Consistent
      ((execution runtime leaks plan current.execution).recall who)) →
    ∀ who, current.actor = some who → nativePlayers who
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      nativePolicy runtime leaks plan (players who)
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who))
    (input : graph.Inputs) (supported : input ∈ inputs.support)
    (fuel : Nat) :
    (fun law => law.bind ((N).controlStep ((PMF.pure input).map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler) nativePlayers))^[fuel] (PMF.pure none) =
    (fun law => law.bind ((N).controlStep ((PMF.pure input).map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)
      (fun who => nativePolicy runtime leaks plan (players who))))^[fuel] (PMF.pure none) := by
  have included : ((PMF.pure input).map (PhaseRuntimeState.initial plan)).support ⊆
      (inputs.map (PhaseRuntimeState.initial plan)).support := by
    rw [PMF.support_map, PMF.support_map]
    apply Set.image_mono
    intro value present
    have same := (PMF.mem_support_pure_iff input value).mp present
    subst value
    exact supported
  have restrictedSafe : ∀ (current : (P).Control)
      (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((PMF.pure input).map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅ := by
    intro current trace faithful
    exact safe current ((PhaseCount.onePacketMenu runtime leaks
      bounds).trace_of_initial_support_subset
       _ _ included horizon scheduler trace) faithful
  have restrictedAgreement := fun current trace => agreement current
    ((PhaseCount.onePacketMenu runtime leaks bounds).trace_of_initial_support_subset
      ((PMF.pure input).map (PhaseRuntimeState.initial plan))
      (inputs.map (PhaseRuntimeState.initial plan)) included horizon scheduler trace)
  exact native_controlLaw_eq_of_local_agreement runtime leaks plan bounds ordered maximal
    (PMF.pure input)
    horizon scheduler players nativePlayers covered restrictedSafe restrictedAgreement fuel


/-- The original all-history premises apply to each supported initial draw. -/
theorem exists_paired_behavioral_run_of_local_agreement_of_supported_input (bounds :
    MessageBounds graph)
  (ordered : graph.RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
  (players : Player → (P).Policy) (nativePlayers : Player → (N).Policy)
  (covered : ∀ (who : Player) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (response : (P).Action), response ∈ (players who past view).support →
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
  (safe : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    (∀ who, (players who).Consistent (current.execution.recall who)) →
      current.execution.application.current.excluded = ∅)
  (agreement : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    current.execution.application.current.excluded = ∅ →
    (∀ who, (players who).Consistent (current.execution.recall who)) →
    (∀ who, (nativePlayers who).Consistent
      ((execution runtime leaks plan current.execution).recall who)) →
    ∀ who, current.actor = some who → nativePlayers who
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      nativePolicy runtime leaks plan (players who)
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who))
    (input : graph.Inputs) (supported : input ∈ inputs.support)
    (fuel : Nat) :
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let physicalInitial := (PMF.pure input).map (PhaseRuntimeState.initial plan)
    let nativeInitial := (PMF.pure input).map State.initial
    let imageScheduler := nativeScheduler runtime leaks plan scheduler
    ∃ paired : PMF ((N).ProtocolState × (P).ProtocolState),
      paired.map Prod.fst = (((N).information nativeInitial horizon
        imageScheduler).runSingleMoverBehavioralFrom
          ((N).singleMover nativeInitial horizon imageScheduler)
          (fun who => (N).encodePolicy (nativePlayers who)) fuel
            ((N).protocol nativeInitial horizon imageScheduler).initHistory).map History.state ∧
      paired.map Prod.snd = ((menu.information physicalInitial horizon scheduler).runBehavioralFrom
        (fun who => menu.restrictPolicy physicalInitial horizon scheduler who (players who)) fuel
          (menu.protocol physicalInitial horizon scheduler).initHistory).map History.state ∧
      ∀ pair ∈ paired.support,
        pair.1 = protocolState runtime leaks plan pair.2 ∧
        PairedPublicRecord runtime leaks plan pair.1 pair.2 := by
  have included : ((PMF.pure input).map (PhaseRuntimeState.initial plan)).support ⊆
      (inputs.map (PhaseRuntimeState.initial plan)).support := by
    rw [PMF.support_map, PMF.support_map]
    apply Set.image_mono
    intro value present
    have same := (PMF.mem_support_pure_iff input value).mp present
    subst value
    exact supported
  have restrictedSafe : ∀ (current : (P).Control)
      (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((PMF.pure input).map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅ := by
    intro current trace faithful
    exact safe current ((PhaseCount.onePacketMenu runtime leaks
      bounds).trace_of_initial_support_subset
       _ _ included horizon scheduler trace) faithful
  have restrictedAgreement := fun current trace => agreement current
    ((PhaseCount.onePacketMenu runtime leaks bounds).trace_of_initial_support_subset
      ((PMF.pure input).map (PhaseRuntimeState.initial plan))
      (inputs.map (PhaseRuntimeState.initial plan)) included horizon scheduler trace)
  exact exists_paired_behavioral_run_of_local_agreement runtime leaks plan bounds ordered
    maximal (PMF.pure input)
    horizon scheduler players nativePlayers covered restrictedSafe restrictedAgreement fuel

end Vegas.EventGraphRuntime.PhaseNativeProjection

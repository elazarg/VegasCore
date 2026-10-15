/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePairedTransition

/-! # The first physical exclusion has an actual native failure history -/

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

/-- A genuine transition from a clear physical history that excludes an owner
extends the actual native prefix to a public failure of that owner. The native
history is retained before physical rollback, so no assumption of continued
clearance or desired target history is needed. -/
theorem exists_native_failure_exit (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (current next : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (joint : Player → Option (P).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal (some current) joint)
    (reached : some next ∈ ((P).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some current) joint).support)
    (owner : Player) (excluded : owner ∈ next.execution.application.current.excluded) :
    ∃ (native : (N).Control)
      (target : ((N).protocol (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)).Trace (some native)),
      TracePrefix (nativeTrace runtime leaks plan bounds ordered maximal inputs horizon
        scheduler trace (fun _ same => Option.some.inj same ▸ clear)) target ∧
      PublicExclusionRecord (⟨native.execution.application,
        next.execution.application.current.excluded⟩ : RecoveryState graph) ∧
      ∃ event, graph.actor? event = some owner ∧
        native.execution.application.PublicFailure event := by
  obtain ⟨paired, first, second, valid⟩ := exists_paired_transition runtime leaks plan bounds
    ordered maximal inputs horizon scheduler current trace clear joint legal
  have physicalSupported : some next ∈ (paired.map Prod.snd).support := by
    rw [second]
    exact reached
  obtain ⟨pair, supported, physical⟩ := PMF.mem_support_map_iff .. |>.mp physicalSupported
  have record := (valid pair supported).2
  cases nativeState : pair.1 with
  | none =>
      change PairedPublicRecord runtime leaks plan pair.1 pair.2 at record
      rw [nativeState, physical] at record
      exact record.elim
  | some native =>
      have nativeSupported : some native ∈ ((N).transition (inputs.map State.initial)
          horizon (nativeScheduler runtime leaks plan scheduler)
          (some (control runtime leaks plan current))
          (jointActions runtime leaks plan joint)).support := by
        rw [← first, PMF.mem_support_map_iff]
        exact ⟨pair, supported, nativeState⟩
      let prior := nativeTrace runtime leaks plan bounds ordered maximal inputs horizon scheduler
        trace (fun _ same => Option.some.inj same ▸ clear)
      have nativeLegal := jointActions_legal runtime leaks plan bounds inputs horizon scheduler
        (some current) joint legal
      let target := prior.extend (jointActions runtime leaks plan joint) nativeLegal nativeSupported
      have recorded : PublicExclusionRecord (⟨native.execution.application,
          next.execution.application.current.excluded⟩ : RecoveryState graph) := by
        change PairedPublicRecord runtime leaks plan pair.1 pair.2 at record
        rw [nativeState, physical] at record
        exact record
      exact ⟨native, target, .extend .refl _ _ _, recorded,
        (recorded.excluded owner).mp excluded⟩

/-- Every excluded actual history contains an original transition from empty
permanent exclusion to nonempty exclusion. The witnesses retain the genuine
chronological prefix, including its actual legal joint action and support. -/
theorem exists_first_exclusion_transition (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    {state : (P).ProtocolState}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state)
    (failed : ∃ current, state = some current ∧
      current.execution.application.current.excluded.Nonempty) :
    ∃ (before after : (P).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
      (joint : Player → Option (P).Action)
      (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal (some before) joint)
      (realized : some after ∈ ((P).transition (inputs.map (PhaseRuntimeState.initial plan))
        horizon scheduler (some before) joint).support),
      before.execution.application.current.excluded = ∅ ∧
      after.execution.application.current.excluded.Nonempty ∧
      TracePrefix (prior.extend joint legal realized) trace := by
  revert failed
  refine Trace.rec (motive := fun state trace =>
    (∃ current, state = some current ∧ current.execution.application.current.excluded.Nonempty) →
      ∃ (before after : (P).Control)
        (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
        (joint : Player → Option (P).Action)
        (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal
            (some before) joint)
        (realized : some after ∈ ((P).transition (inputs.map (PhaseRuntimeState.initial plan))
          horizon scheduler (some before) joint).support),
        before.execution.application.current.excluded = ∅ ∧
        after.execution.application.current.excluded.Nonempty ∧
        TracePrefix (prior.extend joint legal realized) trace) ?_ ?_ trace
  · intro failed
    obtain ⟨current, impossible, _failed⟩ := failed
    cases impossible
  · intro source target prior joint legal realized ih failed
    change target ∈ ((P).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler source joint).support at realized
    cases source with
    | none =>
        simp only [ReactiveApplication.transition] at realized
        obtain ⟨physical, supported, rfl⟩ := PMF.support_map .. ▸ realized
        obtain ⟨input, _supported, rfl⟩ := PMF.support_map .. ▸ supported
        obtain ⟨current, same, owner, excluded⟩ := failed
        cases Option.some.inj same
        have initialClear := (PhaseRuntimeState.settle_physical plan.phases 0
          (⟨State.initial input, ∅⟩ : RecoveryState graph) ⟨State.initial input, ∅⟩ []).1
        change (PhaseRuntimeState.initial plan input).current.excluded = ∅ at initialClear
        change owner ∈ (PhaseRuntimeState.initial plan input).current.excluded at excluded
        rw [initialClear] at excluded
        exact (Finset.notMem_empty owner excluded).elim
    | some before =>
        by_cases clear : before.execution.application.current.excluded = ∅
        · obtain ⟨after, rfl, excluded⟩ := failed
          exact ⟨before, after, prior, joint, legal, realized, clear, excluded, .refl⟩
        · obtain ⟨first, next, firstTrace, actions, permitted, reached, wasClear, excluded,
            isPrefix⟩ := ih ⟨before, rfl, Finset.nonempty_iff_ne_empty.mpr clear⟩
          exact ⟨first, next, firstTrace, actions, permitted, reached, wasClear, excluded,
            .extend isPrefix joint legal realized⟩

end Vegas.EventGraphRuntime.PhaseNativeProjection

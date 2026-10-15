/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeRoundLaw
import Interaction.ReactiveInitialSupport

/-! # Complete execution laws at supported original initial draws -/

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

/-- Full original-premise safety applies at each supported initial draw. -/
theorem rounds_projection_of_local_agreement_of_supported_input (bounds : MessageBounds graph)
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
    (input : graph.Inputs) (supported : input ∈ inputs.support) :
    ((P).roundsFrom ((PMF.pure input).map (PhaseRuntimeState.initial plan)) scheduler players
      horizon).map
      (execution runtime leaks plan) =
      (N).roundsFrom ((PMF.pure input).map State.initial) (nativeScheduler runtime leaks plan
      scheduler)
        nativePlayers horizon := by
  have included : ((PMF.pure input).map (PhaseRuntimeState.initial plan)).support ⊆
      (inputs.map (PhaseRuntimeState.initial plan)).support := by
    rw [PMF.support_map, PMF.support_map]
    apply Set.image_mono
    intro value present
    have same := (PMF.mem_support_pure_iff input value).mp present
    subst value
    exact supported
  apply rounds_projection_of_local_agreement runtime leaks plan bounds ordered maximal
    (PMF.pure input) horizon scheduler players nativePlayers covered
  · intro current trace faithful
    exact safe current ((PhaseCount.onePacketMenu runtime leaks
      bounds).trace_of_initial_support_subset
      _ _ included horizon scheduler trace) faithful
  · intro current trace
    exact agreement current
      ((PhaseCount.onePacketMenu runtime leaks bounds).trace_of_initial_support_subset
        _ _ included horizon scheduler trace)

end Vegas.EventGraphRuntime.PhaseNativeProjection

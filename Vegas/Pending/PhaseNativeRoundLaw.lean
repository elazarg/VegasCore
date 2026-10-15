/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePolicyRun

/-! # Complete original phased and native execution laws -/

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

/-- Finite control-law transport identifies the complete original executions
through the owning rank-bounded evaluator, including all recall and receipts. -/
theorem finish_projection_of_local_agreement (bounds : MessageBounds graph)
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
        ((execution runtime leaks plan current.execution).observe N who)) :
    ((P).finish (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players none).map
      (protocolState runtime leaks plan) =
      (N).finish (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler) nativePlayers none := by
  let fuel := max ((P).rank horizon none) ((N).rank horizon none)
  have law := controlLaw_projection runtime leaks plan bounds ordered maximal inputs horizon
    scheduler players covered safe fuel
  rw [← native_controlLaw_eq_of_local_agreement runtime leaks plan bounds ordered maximal inputs
    horizon scheduler players nativePlayers covered safe agreement fuel] at law
  rw [(P).iterate_eq_finish (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players
    fuel none (Nat.le_max_left _ _),
    (N).iterate_eq_finish (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler) nativePlayers fuel none (Nat.le_max_right _ _)]
      at law
  exact law

/-- The full scheduler-round evaluator of the actual physical policies projects
exactly to the original native evaluator of the matched prescribed policies. -/
theorem rounds_projection_of_local_agreement (bounds : MessageBounds graph)
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
        ((execution runtime leaks plan current.execution).observe N who)) :
    ((P).roundsFrom (inputs.map (PhaseRuntimeState.initial plan)) scheduler players horizon).map
      (execution runtime leaks plan) =
      (N).roundsFrom (inputs.map State.initial) (nativeScheduler runtime leaks plan scheduler)
        nativePlayers horizon := by
  apply pmf_map_injective (f := (some : (N).Execution → Option (N).Execution))
    (Option.some_injective _)
  have law := congrArg (fun distribution => distribution.map
    (Option.map (fun current : (N).Control => current.execution)))
      (finish_projection_of_local_agreement runtime leaks plan bounds ordered maximal inputs
        horizon scheduler players nativePlayers covered safe agreement)
  simpa only [ReactiveApplication.finish, ReactiveApplication.finished,
    ReactiveApplication.roundsFrom, PMF.map_bind, PMF.map_comp, Function.comp_def,
    protocolState, control, Option.map_some] using law

end Vegas.EventGraphRuntime.PhaseNativeProjection

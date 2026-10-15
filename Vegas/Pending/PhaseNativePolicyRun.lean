/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePolicyConsistency
import Vegas.Pending.PhaseNativeBehavioralRun

/-! # Original native execution laws from local policy agreement -/

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

/-- Local matching at actual clear callbacks identifies the original complete
native control law. Policies away from these supported callbacks are arbitrary. -/
theorem native_controlLaw_eq_of_local_agreement (bounds : MessageBounds graph)
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
    (fuel : Nat) :
    (fun law => law.bind ((N).controlStep (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler) nativePlayers))^[fuel] (PMF.pure none) =
    (fun law => law.bind ((N).controlStep (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)
      (fun who => nativePolicy runtime leaks plan (players who))))^[fuel] (PMF.pure none) := by
  let stepP := (P).controlStep (inputs.map (PhaseRuntimeState.initial plan))
    horizon scheduler players
  let stepN := (N).controlStep (inputs.map State.initial) horizon
    (nativeScheduler runtime leaks plan scheduler)
    (fun who => nativePolicy runtime leaks plan (players who))
  let stepOther := (N).controlStep (inputs.map State.initial) horizon
    (nativeScheduler runtime leaks plan scheduler) nativePlayers
  change (fun law => law.bind stepOther)^[fuel] (PMF.pure none) =
    (fun law => law.bind stepN)^[fuel] (PMF.pure none)
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have projected := controlLaw_projection runtime leaks plan bounds ordered maximal inputs
        horizon scheduler players covered safe fuel
      change ((fun law => law.bind stepP)^[fuel] (PMF.pure none)).map
        (protocolState runtime leaks plan) =
          (fun law => law.bind stepN)^[fuel] (PMF.pure none) at projected
      rw [← projected, PMF.bind_map, PMF.bind_map]
      apply bind_congr_on_support
      intro state supported
      cases state with
      | none => rfl
      | some current =>
          obtain ⟨trace, faithful⟩ := supported_control_play runtime leaks plan bounds inputs
            horizon scheduler players covered fuel (some current) supported
          have physicalFaithful := faithful current rfl
          have clear := safe current trace physicalFaithful
          have nativeFaithful := nativePolicies_consistent_of_local_agreement runtime leaks plan
            bounds inputs horizon scheduler players nativePlayers agreement trace clear
              physicalFaithful
          have kernels := agreement current trace clear physicalFaithful nativeFaithful
          rcases current with ⟨remaining, actor, original⟩
          cases actor with
          | none => rfl
          | some who =>
              change (nativePlayers who ((execution runtime leaks plan original).recall who)
                ((execution runtime leaks plan original).observe N who)).bind _ =
                (nativePolicy runtime leaks plan (players who)
                  ((execution runtime leaks plan original).recall who)
                  ((execution runtime leaks plan original).observe N who)).bind _
              rw [kernels who rfl]

/-- The prescribed native profile and the original counted behavioral run have
both actual marginals, using only local matching on supported clear histories. -/
theorem exists_paired_behavioral_run_of_local_agreement (bounds : MessageBounds graph)
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
    (fuel : Nat) :
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let physicalInitial := inputs.map (PhaseRuntimeState.initial plan)
    let nativeInitial := inputs.map State.initial
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
  intro menu physicalInitial nativeInitial imageScheduler
  obtain ⟨paired, first, second, valid⟩ := exists_paired_behavioral_run runtime leaks plan bounds
    ordered maximal inputs horizon scheduler players covered safe fuel
  refine ⟨paired, ?_, second, valid⟩
  rw [(N).run_map_state] at first ⊢
  change paired.map Prod.fst = (fun law => law.bind ((N).controlStep
    (inputs.map State.initial) horizon (nativeScheduler runtime leaks plan scheduler)
      nativePlayers))^[fuel] (PMF.pure none)
  rw [native_controlLaw_eq_of_local_agreement runtime leaks plan bounds ordered maximal inputs
    horizon scheduler players nativePlayers covered safe agreement fuel]
  exact first

end Vegas.EventGraphRuntime.PhaseNativeProjection

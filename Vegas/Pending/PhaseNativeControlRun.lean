/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeSupportedPlay

/-! # Exact native projection of whole initialized clear physical control laws -/

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

omit [Fintype Player] in
private theorem initial_controlStep_projection (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) (players : Player → (P).Policy) :
    ((P).controlStep (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players
      none).map (protocolState runtime leaks plan) =
    (N).controlStep (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)
      (fun who => nativePolicy runtime leaks plan (players who)) none := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_none,
    ReactiveApplication.transition, PMF.map_comp]
  apply map_congr_on_support
  intro input _supported
  have physical := (PhaseRuntimeState.settle_of_clear plan.phases 0
    (⟨State.initial input, ∅⟩ : RecoveryState graph) ⟨State.initial input, ∅⟩ [] rfl).1
  have same : execution runtime leaks plan
      (ReactiveApplication.Execution.initial P (PhaseRuntimeState.initial plan input)) =
        ReactiveApplication.Execution.initial N (State.initial input) := by
    simp only [execution, ReactiveApplication.Execution.initial, PhaseRuntimeState.initial,
      physical, MessageNetwork.mapPayload_empty, List.map_nil]
  change some (⟨horizon, none, execution runtime leaks plan
    (ReactiveApplication.Execution.initial P (PhaseRuntimeState.initial plan input))⟩ :
      (N).Control) = _
  rw [same]
  rfl

/-- Physical safety concerns only actual counted histories whose complete
recalls are consistent with the selected policies. Actual supported play
supplies those traces and consistency; a desired kernel law is not assumed. -/
theorem controlLaw_projection (bounds : MessageBounds graph)
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
    (fuel : Nat) :
    ((fun law => law.bind ((P).controlStep (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler players))^[fuel] (PMF.pure none)).map
        (protocolState runtime leaks plan) =
      (fun law => law.bind ((N).controlStep (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)
        (fun who => nativePolicy runtime leaks plan (players who))))^[fuel] (PMF.pure none) := by
  classical
  let stepP := (P).controlStep (inputs.map (PhaseRuntimeState.initial plan))
    horizon scheduler players
  let stepN := (N).controlStep (inputs.map State.initial) horizon
    (nativeScheduler runtime leaks plan scheduler)
    (fun who => nativePolicy runtime leaks plan (players who))
  change ((fun law => law.bind stepP)^[fuel] (PMF.pure none)).map
    (protocolState runtime leaks plan) = (fun law => law.bind stepN)^[fuel] (PMF.pure none)
  have clearSupported (count : Nat) (current : (P).Control)
      (supported : some current ∈
        ((fun law => law.bind stepP)^[count] (PMF.pure none)).support) :
      current.execution.application.current.excluded = ∅ := by
    obtain ⟨trace, faithful⟩ := supported_control_play runtime leaks plan bounds inputs horizon
      scheduler players covered count (some current) supported
    exact safe current trace (faithful current rfl)
  induction fuel with
  | zero =>
      simp only [Function.iterate_zero_apply, PMF.pure_map]
      rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', PMF.map_bind,
        ← ih, PMF.bind_map]
      apply bind_congr_on_support
      intro state priorSupported
      cases state with
      | none =>
          exact initial_controlStep_projection runtime leaks plan inputs horizon scheduler players
      | some current =>
          obtain ⟨trace, faithful⟩ := supported_control_play runtime leaks plan bounds inputs
            horizon scheduler players covered fuel (some current) priorSupported
          have clear := safe current trace (faithful current rfl)
          by_cases stopped : (P).terminal (some current)
          · rcases current with ⟨remaining, actor, execution⟩
            rcases stopped with ⟨rfl, rfl⟩
            dsimp only [stepP, stepN]
            simp only [Function.comp_def, protocolState, Option.map_some, control,
              ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
              ReactiveApplication.transition, PMF.pure_map]
          · obtain ⟨paired, first, second, valid⟩ := exists_paired_controlStep runtime leaks plan
              bounds ordered maximal inputs horizon scheduler players covered current trace clear
                stopped
            have projected : ∀ pair ∈ paired.support,
                pair.1 = protocolState runtime leaks plan pair.2 := by
              intro pair supported
              apply (valid pair supported).1
              intro next same
              have nextSupported : pair.2 ∈ (stepP (some current)).support := by
                change pair.2 ∈ ((P).controlStep
                  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players
                    (some current)).support
                rw [← second, PMF.mem_support_map_iff]
                exact ⟨pair, supported, rfl⟩
              have wholeSupported : pair.2 ∈
                  ((fun law => law.bind stepP)^[fuel + 1] (PMF.pure none)).support := by
                rw [Function.iterate_succ_apply', PMF.mem_support_bind_iff]
                exact ⟨some current, priorSupported, nextSupported⟩
              rw [same] at wholeSupported
              exact clearSupported (fuel + 1) next wholeSupported
            calc
              (stepP (some current)).map (protocolState runtime leaks plan) =
                  (paired.map Prod.snd).map (protocolState runtime leaks plan) := by rw [second]
              _ = paired.map Prod.fst := by
                rw [PMF.map_comp]
                apply map_congr_on_support
                intro pair supported
                exact (projected pair supported).symm
              _ = stepN (protocolState runtime leaks plan (some current)) := first

/-- Both marginals are the actual initialized finite-fuel control laws. The
original draw is shared through initialization, and each coupled endpoint
retains the full projected control and its exact public exclusion record. -/
theorem exists_paired_control_run (bounds : MessageBounds graph)
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
    (fuel : Nat) :
    ∃ paired : PMF ((N).ProtocolState × (P).ProtocolState),
      paired.map Prod.fst = (fun law => law.bind ((N).controlStep (inputs.map State.initial)
        horizon (nativeScheduler runtime leaks plan scheduler)
        (fun who => nativePolicy runtime leaks plan (players who))))^[fuel] (PMF.pure none) ∧
      paired.map Prod.snd = (fun law => law.bind ((P).controlStep
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players))^[fuel]
          (PMF.pure none) ∧
      ∀ pair ∈ paired.support,
        pair.1 = protocolState runtime leaks plan pair.2 ∧
        PairedPublicRecord runtime leaks plan pair.1 pair.2 := by
  let stepP := (P).controlStep (inputs.map (PhaseRuntimeState.initial plan))
    horizon scheduler players
  let law := (fun law => law.bind stepP)^[fuel] (PMF.pure none)
  refine ⟨law.map (fun state => (protocolState runtime leaks plan state, state)), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact controlLaw_projection runtime leaks plan bounds ordered maximal inputs horizon scheduler
      players covered safe fuel
  · rw [PMF.map_comp]
    exact PMF.map_id law
  · intro pair supported
    obtain ⟨state, drawSupported, rfl⟩ := PMF.mem_support_map_iff .. |>.mp supported
    refine ⟨rfl, ?_⟩
    cases state with
    | none => trivial
    | some current =>
        obtain ⟨trace, faithful⟩ := supported_control_play runtime leaks plan bounds inputs horizon
          scheduler players covered fuel (some current) drawSupported
        exact clear_publicRecord runtime leaks plan bounds inputs horizon scheduler trace
          (safe current trace (faithful current rfl))

end Vegas.EventGraphRuntime.PhaseNativeProjection

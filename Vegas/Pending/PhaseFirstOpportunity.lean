/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseFirstResponseRecall
import Vegas.Pending.PhaseActivationResponse
import Interaction.ReactiveRecordedEnvironment
import Interaction.ReactiveDecisionPredecessor

/-! # First response deadlines from actual phase service

A genuine idle predecessor prevents the current activation from satisfying
its own overdue opportunity obligation. Recorded earlier activations supply
actual response views, with request validity derived from initialized phase
invariants. No calendar or pending-observation assumption is needed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- At an idle raw prefix, an unrecorded request has not passed its reaction bound. -/
theorem unrecorded_idle_clock_bound (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some current))
    (idle : current.actor = none) (delay : graph.EventId → Nat)
    (opportunity : OpportunityAt runtime leaks current.execution delay)
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (request : current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩)
    (activated : current.execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨current.execution.application.attempt, event⟩ (current.execution.recall owner)) :
    current.execution.application.current.native.clock ≤ entered + delay event := by
  by_contra late
  have elapsed : entered + delay event < current.execution.application.current.native.clock :=
    Nat.lt_of_not_ge late
  obtain ⟨entry, member, command, attempt, ready, _stamp⟩ :=
    opportunity event owner entered request.2.2.2.1
      ((current.execution.application.current.native.publicView_eventReady event).mpr
        request.2.2.1) activated elapsed
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨before, prior, _prefix, _idle, _remaining, viewed, _chosen, _tail⟩ :=
    menu.recorded_environment_prefix initial horizon scheduler current trace entry member
  have raw := menu.toRawTrace initial horizon scheduler prior
  have live := (phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact ⟨PhaseRuntimeState.initial_frontier plan draw,
        PhaseRuntimeState.initial_live plan draw⟩) raw
  have geometry := (phaseApplication_quiescent runtime leaks ordered).history initial horizon
    scheduler (fun state supported => by
      obtain ⟨draw, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact phaseApplication_initial_quiescent plan ordered maximal draw) raw
  have wasReady : before.execution.application.current.native.config.cut.Ready event := by
    apply (before.execution.application.current.native.publicView_eventReady event).mp
    simpa only [viewed, ReactiveApplication.Execution.observeEnvironment, phaseApplication,
      PhaseRuntimeState.publicView] using ready
  have requested := before.execution.application.request_of_ready ordered live.1 live.2
    geometry.2.1 geometry.2.2 event wasReady owner request.2.2.2.1
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  have requestView : PhaseRuntimeState.requests entry.beforeView.application owner
      ⟨current.execution.application.attempt, event⟩ := by
    have sameAttempt : before.execution.application.attempt =
        current.execution.application.attempt := by
      simpa only [viewed, ReactiveApplication.Execution.observeEnvironment, phaseApplication,
        PhaseRuntimeState.publicView] using attempt
    rw [viewed, ← sameAttempt]
    exact (before.execution.application.requests_publicView valid owner _).mpr requested
  rcases activation_response_or_current runtime leaks initial horizon scheduler current
      (menu.toRawTrace initial horizon scheduler trace) entry member owner command with
    responded | waiting
  · obtain ⟨response, recalled, view⟩ := responded
    exact first ⟨response, recalled, view ▸ requestView⟩
  · rw [idle] at waiting
    cases waiting.1

/-- The actual first callback has a genuine idle predecessor, so a currently
pending activation cannot itself satisfy an overdue reaction obligation. -/
theorem first_response_clock_bound (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (delay : graph.EventId → Nat)
    (opportunity : Opportunity runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler delay)
    (remaining : Nat) (execution : (app).Execution) (owner : Player)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (entered : Nat)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (activated : execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨execution.application.attempt, event⟩ (execution.recall owner)) :
    execution.application.current.native.clock ≤ entered + delay event := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨before, ⟨prior⟩, same, recalled⟩ :=
    menu.decision_predecessor initial horizon scheduler trace rfl
  have requestBefore : before.application.SeedRequest owner ⟨before.application.attempt, event⟩ :=
    same ▸ request
  have stamp : before.application.current.native.activatedAt event = some entered :=
    same ▸ activated
  have absent : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨before.application.attempt, event⟩ (before.recall owner) := by
    rw [same, recalled]
    exact first
  have bound := unrecorded_idle_clock_bound runtime leaks menu plan ordered maximal inputs horizon
    scheduler ⟨remaining + 1, none, before⟩ prior rfl delay
      (opportunity _ (menu.toRawTrace initial horizon scheduler prior)) event owner entered
        requestBefore stamp absent
  simpa only [same] using bound

/-- At the actual first response, the entire declared inclusion budget fits
strictly before expiry under the supplied relative deadline schedule. -/
theorem first_response_protected (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat)
    (opportunity : Opportunity runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler delay) (timely : runtime.AsyncTimely delay bound)
    (remaining : Nat) (execution : (app).Execution) (owner : Player)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (entered : Nat)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (activated : execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨execution.application.attempt, event⟩ (execution.recall owner)) :
    execution.application.current.native.clock - entered + bound event < runtime.deadline event ∧
      execution.application.current.native.WithinDeadline runtime event := by
  have responseBound := first_response_clock_bound runtime leaks menu plan ordered maximal inputs
    horizon scheduler delay opportunity remaining execution owner trace event entered request
      activated first
  have slack := timely event (by rw [request.2.2.2.1]; rfl)
  refine ⟨by omega, ?_⟩
  simp only [State.WithinDeadline, activated]
  omega

end Vegas.EventGraphRuntime.PhaseService

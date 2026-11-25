module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.EventGraph.SolitaryEvent
public import Vegas.Pending.ExclusionPolicyDistribution
public import Vegas.Pending.CanonicalOutcomeHead

@[expose] public section

/-! # Native continuation while waiting for public chance

A ready chance event is the unique ready event of the sequential graph. Native commands
and arbitrary responses preserve its canonical remaining-run law: sampling executes the
same chance kernel followed by automatic completion, and other commands preserve the
configuration. Bounded waiting therefore preserves the full continuation even when its
budget ends before sampling, without a completion or initialization premise.
The stopped output law applies to solitary chance events on actor-serial graphs.
-/
noncomputable section

namespace Vegas

open EventGraph Interaction GameTheory.Math.Probability
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem ownerless_step_bind_runPlan
    (profile : graph.sequentialize.BehavioralProfile) (config : graph.sequentialize.Config)
    (event : graph.sequentialize.EventId) (ready : config.cut.Ready event)
    (ownerless : graph.sequentialize.actor? event = none) (action :
      graph.sequentialize.Action event) :
    (config.step event ready action).bind (fun next => graph.sequentialize.runPlan
      (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
      next.remaining next) =
      graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        config.remaining config := by
  have nonzero : config.remaining ≠ 0 := by
    intro zero
    have terminal := config.terminal_iff_remaining_zero.mpr zero
    apply ready.1
    rw [EventOrder.Cut.Terminal] at terminal
    rw [terminal]
    exact Finset.mem_univ _
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  symm
  rw [fuelEq, graph.sequentialize.runPlan_canonical_ownerless profile fuel config event ready
    (fun _ pending => graph.sequentialize_ready_le_unfinished config.cut ready
      pending)
    ownerless]
  rw [(graph.sequentialize.nodes event).action_eq_of_actor_none ownerless
    (EventCode.actionOfActorNone (graph.sequentialize.nodes event) ownerless) action]
  apply bind_congr_on_support _
  intro next member
  have progress := config.remaining_step event ready action next member
  have remaining : next.remaining = fuel := by omega
  rw [remaining]

private theorem resume_config
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (actor : Option Player) (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (reached : next ∈ (((reactiveApplication timeouts) leaks).resume players actor
      execution).support) :
    next.application.config = execution.application.config := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | some who =>
      change next ∈ (((reactiveApplication timeouts) leaks).invoke players who execution).support
        at reached
      rw [ReactiveApplication.invoke, PMF.support_map] at reached
      obtain ⟨response, _, rfl⟩ := reached
      exact ((reactive_respond_application timeouts) leaks execution who response).1

private theorem chance_environment_bind_runPlan
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (state : EventGraphRuntime.State graph)
    (command : EnvironmentCommand graph) (event :
      graph.EventId) (solitary : graph.Solitary event)
    (headStep : ∀ (config : graph.Config)
      (ready : config.cut.Ready event) (action : graph.Action event),
      (config.step event ready action).bind continuation = continuation config)
    (ready : state.config.cut.Ready event) (ownerless :
      graph.actor? event = none) :
    ((((reactiveApplication timeouts) leaks).environment state command).bind fun next =>
      continuation next.config) =
      continuation state.config := by
  refine (show ((environmentStep timeouts state command).map EventGraphRuntime.State.drain).bind
      (fun next => continuation next.config) =
        (environmentStep timeouts state command).bind (fun next => continuation next.config) by
    rw [PMF.bind_map]
    exact bind_congr_on_support _ fun next _ => drained next).trans ?_
  have sole (other : graph.EventId)
    (otherReady : state.config.cut.Ready other) :
      other = event := solitary state.config.cut otherReady ready
  cases node : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      have actor := nodeView_bind_actor outputEq codeEq
      rw [ownerless] at actor
      cases actor
  | resolve owner payload binding checks outputEq codeEq =>
      have actor := nodeView_resolve_actor outputEq codeEq
      rw [ownerless] at actor
      cases actor
  | sample payload law outputEq codeEq =>
      cases command with
      | advanceClock => simp only [environmentStep, PMF.pure_bind]
      | executeSample other =>
          by_cases otherReady : state.config.cut.Ready other
          · have same := sole other otherReady
            subst other
            rw [environmentStep_executeSample_eq timeouts state event ready payload law outputEq
              codeEq node, PMF.bind_map]
            exact headStep state.config ready _
          · rw [environmentStep_executeSample_of_not_ready timeouts state other otherReady,
              PMF.pure_bind]
      | expire other =>
          have pure : environmentStep timeouts state (.expire other) = PMF.pure state := by
            by_cases otherReady : state.config.cut.Ready other
            · have same := sole other otherReady
              subst other
              cases activated : state.activatedAt event with
              | none =>
                  exact environmentStep_expire_of_not_activated timeouts state event ready activated
              | some entered =>
                  by_cases due : timeouts.duration event ≤ state.clock - entered
                  · exact environmentStep_expire_sample_eq timeouts state event ready entered
                      activated due payload law outputEq codeEq node
                  · exact environmentStep_expire_of_not_due timeouts state event ready entered
                      activated due
            · exact environmentStep_expire_of_not_ready timeouts state other otherReady
          rw [pure, PMF.pure_bind]

/-- Every native command preserves the remaining canonical law while the ready
event is a public chance event. Sampling includes its atomic automatic tail. -/
private theorem chance_dispatch_bind_runPlan
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command) (event :
      graph.EventId) (solitary : graph.Solitary event)
    (headStep : ∀ (config : graph.Config)
      (ready : config.cut.Ready event) (action : graph.Action event),
      (config.step event ready action).bind continuation = continuation config)
    (ready : execution.application.config.cut.Ready event)
    (ownerless : graph.actor? event = none) :
    ((((reactiveApplication timeouts) leaks).dispatch players command execution).bind fun next =>
      continuation next.application.config) =
      continuation execution.application.config := by
  let app := (reactiveApplication timeouts) leaks
  let onward := fun next : app.Execution => continuation next.application.config
  change (app.dispatch players command execution).bind onward = onward execution
  unfold ReactiveApplication.dispatch
  rw [PMF.bind_bind]
  have resumed (middle : app.Execution) :
      (app.resume players (command.actor? app) middle).bind onward = onward middle := by
    calc
      _ = (app.resume players (command.actor? app) middle).bind
          (fun _ => onward middle) := by
        apply bind_congr_on_support _
        intro next reached
        dsimp only [onward]
        rw [resume_config timeouts leaks players _ middle next reached]
      _ = _ := PMF.bind_const _ _
  simp_rw [resumed]
  have stays : (∀ next ∈ (execution.environmentStep app command).support,
      next.application.config = execution.application.config) →
      (execution.environmentStep app command).bind onward = onward execution := by
    intro fixed
    calc
      _ = (execution.environmentStep app command).bind (fun _ => onward execution) := by
        apply bind_congr_on_support _
        intro next reached
        dsimp only [onward]
        rw [fixed next reached]
      _ = _ := PMF.bind_const _ _
  cases command with
  | activate who =>
      apply stays
      intro next reached
      unfold ReactiveApplication.Execution.environmentStep at reached
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | wait =>
      apply stays
      intro next reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | «include» id =>
      apply stays
      intro next reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message =>
          change ((app.handle execution.application message).getD execution.application).config = _
          cases accepted : app.handle execution.application message with
          | none => rfl
          | some next =>
              obtain ⟨native, handled, _⟩ := reactiveHandle_call accepted
              obtain ⟨named, namedEq, namedReady, _, _⟩ := handle_config_mem_step timeouts
                execution.application native ⟨message.id, message.payload.call⟩ handled
              have same := solitary
                execution.application.config.cut namedReady ready
              subst named
              have actor := handle_sender_actor timeouts execution.application native
                ⟨message.id, message.payload.call⟩ handled event namedEq
              rw [ownerless] at actor
              cases actor
  | application command =>
      change (execution.environmentStep app (.application command)).bind onward = _
      simp only [ReactiveApplication.Execution.environmentStep, PMF.bind_map]
      exact chance_environment_bind_runPlan timeouts leaks continuation drained
        execution.application command event solitary headStep ready ownerless

/-- Bounded waiting for a ready solitary chance event preserves every
continuation that automatic completion leaves unchanged and that the chance step
preserves, including runs whose budget ends before sampling. -/
theorem chance_runUntil_bind_continuation
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (solitary :
      graph.Solitary event)
    (headStep : ∀ (config : graph.Config)
      (ready : config.cut.Ready event) (action : graph.Action event),
      (config.step event ready action).bind continuation = continuation config) (ownerless :
        graph.actor? event = none) :
    ∀ (count : Nat) (execution : ((reactiveApplication timeouts) leaks).Execution),
      execution.application.config.cut.Ready event →
      ((((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).bind
        fun final => continuation final.application.config) =
        continuation execution.application.config := by
  classical
  let app := (reactiveApplication timeouts) leaks
  let onward := fun next : app.Execution => continuation next.application.config
  intro count
  induction count with
  | zero => intro execution _; simp only [ReactiveApplication.runUntil, PMF.pure_bind]
  | succ count ih =>
      intro execution ready
      rw [ReactiveApplication.runUntil, ite_eq_right ready.1, PMF.bind_bind]
      calc
        _ = (app.round scheduler players execution).bind onward := by
          apply bind_congr_on_support _
          intro next reached
          by_cases completed : event ∈ next.application.config.cut.completed
          · rw [app.runUntil_of_stop scheduler players _ count next completed, PMF.pure_bind]
          · have path : Relation.ReflTransGen EventGraph.Config.Step
                execution.application.config next.application.config := by
              obtain ⟨command, _, dispatched⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨middle, moved, resumed⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
              have same := resume_config timeouts leaks players _ middle next resumed
              rw [same]
              exact ((reactiveApplication_graphSteps timeouts) leaks).environmentStep
                execution middle command moved
            have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
              (fun _ otherReady => solitary _ otherReady ready)
              completed path
            exact ih next (same.symm ▸ ready)
        _ = onward execution := by
          unfold ReactiveApplication.round
          rw [PMF.bind_bind]
          calc
            _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
                (fun _ => onward execution) :=
              bind_congr_on_support _ (fun command _ =>
                chance_dispatch_bind_runPlan timeouts leaks continuation drained players
                  execution command event solitary headStep ready ownerless)
            _ = _ := PMF.bind_const _ _

/-- Bounded waiting for a ready chance event preserves its complete canonical
continuation, including runs whose budget ends before sampling. -/
theorem chance_runUntil_bind_runPlan (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (profile : graph.sequentialize.BehavioralProfile)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.sequentialize.EventId) (ownerless : graph.sequentialize.actor? event =
      none) :
    ∀ (count : Nat) (execution : ((reactiveApplication timeouts) leaks).Execution),
      execution.application.config.cut.Ready event →
      ((((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).bind
        fun final => graph.sequentialize.runPlan
          (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
          final.application.config.remaining final.application.config) =
        graph.sequentialize.runPlan
          (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
          execution.application.config.remaining execution.application.config :=
  chance_runUntil_bind_continuation timeouts leaks
    (fun config => graph.sequentialize.runPlan
      (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        config.remaining config)
    (fun state => (EventGraphRuntime.State.drain_runPlan_canonical graph profile
      state).symm) scheduler players event (graph.sequentialize_solitary event)
    (fun config ready action => ownerless_step_bind_runPlan profile config event ready ownerless
      action) ownerless

private theorem runPlan_output_distribution {compiled : Vegas.EventGraph Player L}
    (plan : compiled.EventPlan) (fuel : Nat) (config : compiled.Config)
    (event : compiled.EventId) (completed : event ∈ config.cut.completed) :
    (compiled.runPlan plan fuel config).map (fun final => final.outputs event) =
      PMF.pure (config.outputs event) := by
  calc
    _ = (compiled.runPlan plan fuel config).map (fun _ => config.outputs event) := by
      exact map_congr_on_support _ (fun after reached =>
        path_outputs_of_completed (runPlan_graph_steps plan fuel config after reached) completed)
    _ = _ := pmf_map_fun_const _ _

/-- Once a ready chance event has completed, its stopped output has exactly
its graph sampling law, including any automatic completions after the draw. -/
theorem chance_completed_output_distribution
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (serial : graph.ActorSerial)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId)
    (ownerless : graph.actor? event =
      none) (solitary : graph.Solitary event)
    (count : Nat) (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (completed : ∀ final ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).support,
      event ∈ final.application.config.cut.completed) :
    (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).map
        (fun final => final.application.config.outputs event) =
      (execution.application.config.step event ready
        (EventCode.actionOfActorNone (graph.nodes event) ownerless)).map
          (fun final => final.outputs event) := by
  let choices := fun who event (actor : graph.actor? event = some who) =>
    PMF.pure ((graph.nodes event).failureAction who actor)
  let profile : graph.BehavioralProfile := fun who event actor _ _ => choices who event actor
  have independent : ReadyIndependent profile := serial.readyIndependent_of_eventDistributions
    choices
  let plan := graph.policyPlan profile graph.canonicalScheduler
  let read := fun config : graph.Config => config.outputs event
  have keyed (left right : graph.Config) (same : runKey left = runKey right) :
      read left = read right := congrFun (congrArg (fun key => key.2.1) same) (.inr event)
  have waiting := chance_runUntil_bind_continuation timeouts leaks
    (outcomeDistribution profile read) (fun state => outcomeDistribution_drain independent read
      keyed state)
    scheduler players event solitary
    (fun config ready action => step_bind_outcomeDistribution_ownerless profile read config event
      ready
      (fun other pending => by
        obtain ⟨earlier, earlierReady, before⟩ :=
          config.cut.exists_ready_le_of_unfinished other pending
        rw [solitary _ earlierReady ready] at before
        exact before) ownerless action) ownerless count execution ready
  change _ = (graph.runPlan plan execution.application.config.remaining
    execution.application.config).map read at waiting
  have law := waiting
  dsimp only [outcomeDistribution, read] at law
  have left :
      ((((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).bind
        fun final => (graph.runPlan plan final.application.config.remaining
          final.application.config).map (fun config => config.outputs event)) =
      (((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).map
          (fun final => final.application.config.outputs event) := by
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro final supported
    exact runPlan_output_distribution plan _ _ event (completed final supported)
  change _ = (graph.runPlan plan execution.application.config.remaining
    execution.application.config).map (fun final => final.outputs event) at law
  rw [left] at law
  rw [law]
  have nonzero : execution.application.config.remaining ≠ 0 := by
    intro zero
    have terminal := execution.application.config.terminal_iff_remaining_zero.mpr zero
    exact ready.1 (terminal ▸ Finset.mem_univ event)
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  rw [fuelEq, graph.runPlan_canonical_ownerless profile fuel
    execution.application.config event ready
    (fun other pending => by
      obtain ⟨earlier, earlierReady, before⟩ :=
        execution.application.config.cut.exists_ready_le_of_unfinished other pending
      rw [solitary _ earlierReady ready] at before
      exact before)
    ownerless, PMF.map_bind]
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro next supported
  apply runPlan_output_distribution plan fuel next event
  rw [execution.application.config.step_cut event ready _ next supported,
    EventOrder.Cut.mem_complete]
  exact Or.inl rfl

end Vegas

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceAsyncStep
import Vegas.Pending.ExclusionPolicyLaw

/-! # Native continuation while waiting for public chance

A ready chance event is the unique ready event of the sequential graph. Native commands
and arbitrary responses preserve its canonical remaining-run law: sampling executes the
same chance kernel followed by automatic completion, and other commands preserve the
configuration. Bounded waiting therefore preserves the full continuation even when its
budget ends before sampling, without a completion or initialization premise.
-/
noncomputable section

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

private theorem ownerless_step_bind_runPlan
    (profile : (graph setup).BehavioralProfile) (config : (graph setup).Config)
    (event : (graph setup).EventId) (ready : config.cut.Ready event)
    (ownerless : (graph setup).actor? event = none) (action : (graph setup).Action event) :
    (config.step event ready action).bind (fun next => (graph setup).runPlan
      ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
      next.remaining next) =
      (graph setup).runPlan
        ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
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
  rw [fuelEq, (graph setup).runPlan_canonical_ownerless profile fuel config event ready
    (fun _ pending => setup.eventGraph.sequentialize_ready_le_unfinished config.cut ready pending)
    ownerless]
  rw [((graph setup).nodes event).action_eq_of_actor_none ownerless
    (EventCode.actionOfActorNone ((graph setup).nodes event) ownerless) action]
  apply bind_congr_on_support _
  intro next member
  have progress := config.remaining_step event ready action next member
  have remaining : next.remaining = fuel := by omega
  rw [remaining]

private theorem resume_config
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (actor : Option Player) (execution next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ ((runtime.reactiveApplication leaks).resume players actor
      execution).support) :
    next.application.config = execution.application.config := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | some who =>
      change next ∈ ((runtime.reactiveApplication leaks).invoke players who execution).support
        at reached
      rw [ReactiveApplication.invoke, PMF.support_map] at reached
      obtain ⟨response, _, rfl⟩ := reached
      exact (runtime.reactive_respond_application leaks execution who response).1

private theorem chance_environment_bind_runPlan
    {Result : Type*} (continuation : (serviceGraph setup mode).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup mode),
      continuation state.drain.config = continuation state.config)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (command : EnvironmentCommand (serviceGraph setup mode)) (event :
      (serviceGraph setup mode).EventId) (solitary : (serviceGraph setup mode).Solitary event)
    (headStep : ∀ (config : (serviceGraph setup mode).Config)
      (ready : config.cut.Ready event) (action : (serviceGraph setup mode).Action event),
      (config.step event ready action).bind continuation = continuation config)
    (ready : state.config.cut.Ready event) (ownerless :
      (serviceGraph setup mode).actor? event = none) :
    (((runtime.reactiveApplication leaks).environment state command).bind fun next =>
      continuation next.config) =
      continuation state.config := by
  refine (show ((environmentStep runtime state command).map EventGraphRuntime.State.drain).bind
      (fun next => continuation next.config) =
        (environmentStep runtime state command).bind (fun next => continuation next.config) by
    rw [PMF.bind_map]
    exact bind_congr_on_support _ fun next _ => drained next).trans ?_
  have sole (other : (serviceGraph setup mode).EventId)
    (otherReady : state.config.cut.Ready other) :
      other = event := solitary state.config.cut otherReady ready
  cases node : nodeView (serviceGraph setup mode) event with
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
            rw [environmentStep_executeSample_eq runtime state event ready payload law outputEq
              codeEq node, PMF.bind_map]
            exact headStep state.config ready _
          · rw [environmentStep_executeSample_of_not_ready runtime state other otherReady,
              PMF.pure_bind]
      | expire other =>
          have pure : environmentStep runtime state (.expire other) = PMF.pure state := by
            by_cases otherReady : state.config.cut.Ready other
            · have same := sole other otherReady
              subst other
              cases activated : state.activatedAt event with
              | none =>
                  exact environmentStep_expire_of_not_activated runtime state event ready activated
              | some entered =>
                  by_cases due : runtime.deadline event ≤ state.clock - entered
                  · exact environmentStep_expire_sample_eq runtime state event ready entered
                      activated due payload law outputEq codeEq node
                  · exact environmentStep_expire_of_not_due runtime state event ready entered
                      activated due
            · exact environmentStep_expire_of_not_ready runtime state other otherReady
          rw [pure, PMF.pure_bind]

/-- Every native command preserves the remaining canonical law while the ready
event is a public chance event. Sampling includes its atomic automatic tail. -/
private theorem chance_dispatch_bind_runPlan
    {Result : Type*} (continuation : (serviceGraph setup mode).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup mode),
      continuation state.drain.config = continuation state.config)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command) (event :
      (serviceGraph setup mode).EventId) (solitary : (serviceGraph setup mode).Solitary event)
    (headStep : ∀ (config : (serviceGraph setup mode).Config)
      (ready : config.cut.Ready event) (action : (serviceGraph setup mode).Action event),
      (config.step event ready action).bind continuation = continuation config)
    (ready : execution.application.config.cut.Ready event)
    (ownerless : (serviceGraph setup mode).actor? event = none) :
    (((runtime.reactiveApplication leaks).dispatch players command execution).bind fun next =>
      continuation next.application.config) =
      continuation execution.application.config := by
  let app := runtime.reactiveApplication leaks
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
        rw [resume_config runtime leaks players _ middle next reached]
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
      rw [activation_application (setup := setup) leaks execution next who reached]
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
              obtain ⟨named, namedEq, namedReady, _, _⟩ := handle_config_mem_step runtime
                execution.application native ⟨message.id, message.payload.call⟩ handled
              have same := solitary
                execution.application.config.cut namedReady ready
              subst named
              have actor := handle_sender_actor runtime execution.application native
                ⟨message.id, message.payload.call⟩ handled event namedEq
              rw [ownerless] at actor
              cases actor
  | application command =>
      change (execution.environmentStep app (.application command)).bind onward = _
      simp only [ReactiveApplication.Execution.environmentStep, PMF.bind_map]
      exact chance_environment_bind_runPlan runtime leaks continuation drained
        execution.application command event solitary headStep ready ownerless

/-- Bounded waiting for a ready solitary chance event preserves every
continuation that automatic completion leaves unchanged and that the chance step
preserves, including runs whose budget ends before sampling. -/
theorem chance_runUntil_bind_continuation
    {Result : Type*} (continuation : (serviceGraph setup mode).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup mode),
      continuation state.drain.config = continuation state.config)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (event : (serviceGraph setup mode).EventId) (solitary :
      (serviceGraph setup mode).Solitary event)
    (headStep : ∀ (config : (serviceGraph setup mode).Config)
      (ready : config.cut.Ready event) (action : (serviceGraph setup mode).Action event),
      (config.step event ready action).bind continuation = continuation config) (ownerless :
        (serviceGraph setup mode).actor? event = none) :
    ∀ (count : Nat) (execution : (runtime.reactiveApplication leaks).Execution),
      execution.application.config.cut.Ready event →
      (((runtime.reactiveApplication leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).bind
        fun final => continuation final.application.config) =
        continuation execution.application.config := by
  classical
  let app := runtime.reactiveApplication leaks
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
              have same := resume_config runtime leaks players _ middle next resumed
              rw [same]
              exact (runtime.reactiveApplication_graphSteps leaks).environmentStep
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
                chance_dispatch_bind_runPlan runtime leaks continuation drained players
                  execution command event solitary headStep ready ownerless)
            _ = _ := PMF.bind_const _ _

/-- Bounded waiting for a ready chance event preserves its complete canonical
continuation, including runs whose budget ends before sampling. -/
theorem chance_runUntil_bind_runPlan (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (event : (graph setup).EventId) (ownerless : (graph setup).actor? event = none) :
    ∀ (count : Nat) (execution : (application setup runtime leaks).Execution),
      execution.application.config.cut.Ready event →
      (((application setup runtime leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).bind
        fun final => (graph setup).runPlan
          ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          final.application.config.remaining final.application.config) =
        (graph setup).runPlan
          ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          execution.application.config.remaining execution.application.config :=
  chance_runUntil_bind_continuation runtime leaks
    (fun config => (graph setup).runPlan
      ((graph setup).policyPlan profile (graph setup).canonicalScheduler) config.remaining config)
    (fun state => (EventGraphRuntime.State.drain_runPlan_canonical setup.eventGraph profile
      state).symm) scheduler players event (setup.eventGraph.sequentialize_solitary event)
    (fun config ready action => ownerless_step_bind_runPlan profile config event ready ownerless
      action) ownerless

private theorem runPlan_store_law {compiled : Vegas.EventGraph Player L}
    (plan : compiled.EventPlan) :
    ∀ (fuel : Nat) (config : compiled.Config) (field : compiled.Field)
      (value : (compiled.layout field).Value), config.store field = some value →
      (compiled.runPlan plan fuel config).map (fun final => final.store field) =
        PMF.pure (some value) := by
  intro fuel
  induction fuel with
  | zero =>
      intro config field value stored
      simpa only [EventGraph.runPlan, PMF.pure_map] using congrArg PMF.pure stored
  | succ fuel ih =>
      intro config field value stored
      rw [EventGraph.runPlan]
      split
      · simpa only [PMF.pure_map] using congrArg PMF.pure stored
      · simp only [PMF.map_bind]
        calc
          _ = (plan config _).bind (fun _ => PMF.pure (some value)) := by
            apply bind_congr_on_support _
            intro choice _chosen
            calc
              _ = (config.step choice.1.1 choice.1.2 choice.2).bind
                  (fun _ => PMF.pure (some value)) := by
                apply bind_congr_on_support _
                intro next supported
                exact ih next field value
                  (config.step_store_of_some next choice.1.1 choice.1.2 choice.2 supported
                    field value stored)
              _ = _ := PMF.bind_const _ _
          _ = _ := PMF.bind_const _ _

private theorem runPlan_output_law {compiled : Vegas.EventGraph Player L}
    (plan : compiled.EventPlan) (fuel : Nat) (config : compiled.Config)
    (event : compiled.EventId) (completed : event ∈ config.cut.completed) :
    (compiled.runPlan plan fuel config).map (fun final => final.outputs event) =
      PMF.pure (config.outputs event) := by
  obtain ⟨value, stored⟩ :=
    Option.isSome_iff_exists.mp ((config.output_available event).mpr completed)
  change config.outputs event = some value at stored
  change (compiled.runPlan plan fuel config).map (fun final => final.store (.inr event)) = _
  rw [stored]
  exact runPlan_store_law plan fuel config (.inr event) value stored

/-- Once a ready chance event has completed, its stopped output has exactly
its graph sampling law, including any automatic completions after the draw. -/
theorem chance_completed_output_law
    {setup : Setup (Player := Player) (L := L)} (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (event : (graph setup).EventId) (ownerless : (graph setup).actor? event = none)
    (count : Nat) (execution : (application setup runtime leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (completed : ∀ final ∈ ((application setup runtime leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).support,
      event ∈ final.application.config.cut.completed) :
    ((application setup runtime leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count execution).map
        (fun final => final.application.config.outputs event) =
      (execution.application.config.step event ready
        (EventCode.actionOfActorNone ((graph setup).nodes event) ownerless)).map
          (fun final => final.outputs event) := by
  let plan := (graph setup).policyPlan profile (graph setup).canonicalScheduler
  have law := congrArg (PMF.map (fun final : (graph setup).Config => final.outputs event))
    (chance_runUntil_bind_runPlan runtime leaks profile scheduler players event ownerless
      count execution ready)
  simp only [PMF.map_bind] at law
  have left :
      (((application setup runtime leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).bind
        fun final => ((graph setup).runPlan plan final.application.config.remaining
          final.application.config).map (fun config => config.outputs event)) =
      ((application setup runtime leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).map
          (fun final => final.application.config.outputs event) := by
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro final supported
    exact runPlan_output_law plan _ _ event (completed final supported)
  change _ = ((graph setup).runPlan plan execution.application.config.remaining
    execution.application.config).map (fun final => final.outputs event) at law
  rw [left] at law
  rw [law]
  have nonzero : execution.application.config.remaining ≠ 0 := by
    intro zero
    have terminal := execution.application.config.terminal_iff_remaining_zero.mpr zero
    exact ready.1 (terminal ▸ Finset.mem_univ event)
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  rw [fuelEq, (graph setup).runPlan_canonical_ownerless profile fuel
    execution.application.config event ready
    (fun _ pending => setup.eventGraph.sequentialize_ready_le_unfinished _ ready pending)
    ownerless, PMF.map_bind]
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro next supported
  apply runPlan_output_law plan fuel next event
  rw [execution.application.config.step_cut event ready _ next supported,
    EventOrder.Cut.mem_complete]
  exact Or.inl rfl



end Vegas

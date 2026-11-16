module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveInvariant
public import Interaction.ReactiveEnvironmentStep
public import Interaction.ReactiveStopping
public import Vegas.Pending.ReactiveRuntime
public import Vegas.EventGraph.OwnedStep
public import Vegas.EventGraph.BarrierBlocks
public import Vegas.EventGraph.DefaultFailure

@[expose] public section

/-! # Finite graph paths for raw ledger transitions

Inclusion and expiry can trigger several automatic completions. Every such
completion uses the graph executor, independently of player responses,
pending observations and scheduler choices.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A response registers private material while retaining the graph configuration
and the public application view. -/
theorem reactive_respond_application (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (action : ((reactiveApplication timeouts) leaks).Action) :
    (execution.respond ((reactiveApplication timeouts) leaks) who action).application.config =
        execution.application.config ∧
      (execution.respond ((reactiveApplication timeouts) leaks) who action).application.publicView =
        execution.application.publicView := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨rfl, rfl⟩
  | some material =>
      exact ⟨(submitStep_config _ who material.call.packet).trans
        (material.call.register_facts who execution.application).1,
        (submitStep_publicView _ who material.call.packet).trans
          (material.call.register_facts who execution.application).2⟩

/-- Native environment service stutters or performs one supported graph step. -/
theorem environmentStep_graph_steps (timeouts : EventTimeouts graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (supported : next ∈ (environmentStep timeouts state command).support) :
    Relation.ReflTransGen EventGraph.Config.Step state.config next.config := by
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at supported
      subst next
      exact .refl
  | executeSample event =>
      rcases (environmentStep_executeSample_config_activated timeouts state next event
        supported).2 with same | ⟨ready, action, moved, _⟩
      · rw [same.1]
      · exact .single ⟨event, ready, action, moved⟩
  | expire event =>
      rcases (environmentStep_expire_config_activated timeouts state next event supported).2
        with same | ⟨ready, action, moved, _⟩
      · rw [same.1]
      · exact .single ⟨event, ready, action, moved⟩

/-- All application operations follow finite paths of the sole graph executor. -/
theorem reactiveApplication_graphSteps (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    ((reactiveApplication timeouts) leaks).StepRelation (fun before after =>
      Relation.ReflTransGen EventGraph.Config.Step before.config after.config) where
  refl := fun _ => .refl
  submit state who material := by
    change Relation.ReflTransGen EventGraph.Config.Step state.config
      (submitStep (material.call.register state who) who material.call.packet).config
    rw [submitStep_config, (material.call.register_facts who state).1]
  handle state message next accepted := by
    obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
    rw [← nextEq]
    obtain ⟨event, _, ready, action, moved⟩ :=
      handle_config_mem_step timeouts state native ⟨message.id, message.payload.call⟩ handled
    exact (Relation.ReflTransGen.single ⟨event, ready, action, moved⟩).trans
      native.drain_graph_steps
  environment state command next supported := by
    change next ∈ ((environmentStep timeouts state command).map State.drain).support at supported
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ supported
    exact (environmentStep_graph_steps timeouts state native command moved).trans
      native.drain_graph_steps

/-- A scheduler round follows a finite path of the graph executor, including
all automatic completions triggered by its command. -/
theorem reactive_round_graph_steps (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (before after : ((reactiveApplication timeouts) leaks).Execution)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).round scheduler players
      before).support) :
    Relation.ReflTransGen Config.Step before.application.config after.application.config := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have path := ((reactiveApplication_graphSteps timeouts) leaks).environmentStep
    before middle command moved
  cases actor : command.actor? app with
  | none =>
      change after ∈ (app.resume players (command.actor? app) middle).support at resumed
      simp only [actor, ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      subst after
      exact path
  | some who =>
      change after ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor] at resumed
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      exact path.trans
        (((reactiveApplication_graphSteps timeouts) leaks).respond middle who response)

/-- A round cannot change the graph configuration before its unique ready
event completes, even when the command may perform automatic completion. -/
theorem reactive_round_config_eq_of_pending (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (before after : ((reactiveApplication timeouts) leaks).Execution)
    (unique : ∀ other, before.application.config.cut.Ready other → other = event)
    (pending : event ∉ after.application.config.cut.completed)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).round scheduler players
      before).support) : after.application.config = before.application.config :=
  Config.Step.path_eq_of_ready_of_not_completed event unique pending
    (reactive_round_graph_steps timeouts leaks scheduler players before after reached)

/-- Every finite native round sequence follows a supported graph path, including automatic
completions performed by the rounds. -/
theorem reactive_runRounds_graph_steps (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (count : Nat) (before after : ((reactiveApplication timeouts) leaks).Execution)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).runRounds scheduler players
      count before).support) :
    Relation.ReflTransGen Config.Step before.application.config after.application.config := by
  induction count generalizing before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact .refl
  | succ count ih =>
      obtain ⟨middle, first, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      exact (reactive_round_graph_steps timeouts leaks scheduler players before middle first).trans
        (ih middle rest)

/-- Every stopped native execution follows a finite supported graph path.
The path may contain several automatic completions in one scheduler round. -/
theorem reactive_runUntil_graph_steps (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (stop : ((reactiveApplication timeouts) leaks).Execution → Prop) [DecidablePred stop]
    (count : Nat) (before after : ((reactiveApplication timeouts) leaks).Execution)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      stop count before).support) :
    Relation.ReflTransGen Config.Step before.application.config after.application.config := by
  induction count generalizing before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact .refl
  | succ count ih =>
      by_cases stopped : stop before
      · simp only [ReactiveApplication.runUntil, stopped, ↓reduceIte,
          PMF.mem_support_pure_iff] at reached
        subst after
        exact .refl
      · simp only [ReactiveApplication.runUntil, stopped, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        exact (reactive_round_graph_steps timeouts leaks scheduler players before middle
          moved).trans
          (ih middle rest)

/-- A native command ending before any public default stutters or performs
one supported graph step. Automatic tails are empty in this internally clear region. -/
theorem reactive_environmentStep_config_eq_or_step (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (reached : next ∈ (execution.environmentStep ((reactiveApplication timeouts) leaks)
      command).support)
    (clear : next.application.config.defaulted = ∅) :
    next.application.config = execution.application.config ∨
      ∃ (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
        (action : graph.Action event),
        next.application.config ∈
          (execution.application.config.step event ready action).support := by
  have undrained (native state : State graph) (drained : native.drain = state)
      (empty : state.config.defaulted = ∅) : native.drain = native := by
    apply native.drain_eq_of_empty
    have defaults : native.drain.config.defaulted = native.config.defaulted :=
      native.drainFuel_defaulted native.config.remaining
    rw [← defaults, drained]
    exact empty
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      exact Or.inl rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact Or.inl rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      cases found : execution.network.lookup id with
      | none =>
          left
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
      | some message =>
          cases accepted :
              ((reactiveApplication timeouts) leaks).handle execution.application message with
          | none =>
              left
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
                found, accepted, Option.getD_none]
          | some state =>
              have empty : state.config.defaulted = ∅ := by
                simpa only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending,
                  found, accepted, Option.getD_some] using clear
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
              obtain ⟨event, _, ready, action, moved⟩ :=
                handle_config_mem_step timeouts execution.application native _ handled
              refine Or.inr ⟨event, ready, action, ?_⟩
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
                found, accepted, Option.getD_some]
              rw [← drained, undrained native state drained empty]
              exact moved
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep timeouts execution.application operation).map
        State.drain).support at changed
      obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
      change native.drain.config.defaulted = ∅ at clear
      rw [undrained native native.drain rfl clear]
      cases operation with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff] at moved
          subst native
          exact Or.inl rfl
      | executeSample event =>
          rcases (environmentStep_executeSample_config_activated timeouts execution.application
            native event moved).2 with ⟨same, _⟩ | ⟨ready, action, sampled, _⟩
          · exact Or.inl same
          · exact Or.inr ⟨event, ready, action, sampled⟩
      | expire event =>
          rcases environmentStep_expire_config_eq_or_mem_step timeouts execution.application native
            event moved with same | ⟨ready, action, expired⟩
          · exact Or.inl same
          · exact Or.inr ⟨event, ready, action, expired⟩

/-- Arbitrary raw responses and scheduler choices refine finite supported graph paths. -/
theorem reactive_protocol_graph_steps (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (before after : ((reactiveApplication timeouts) leaks).Control)
    (joint : Player → Option ((reactiveApplication timeouts) leaks).Action)
    (supported : some after ∈ (((reactiveApplication timeouts) leaks).transition
      initial horizon scheduler (some before) joint).support) :
    Relation.ReflTransGen EventGraph.Config.Step before.execution.application.config
      after.execution.application.config :=
  (reactiveApplication_graphSteps timeouts leaks).transition
    initial horizon scheduler before after joint supported

/-- A native protocol transition ending with no public defaults either stutters
or performs one supported graph step. Automatic tails are empty in this region. -/
theorem reactive_protocol_config_eq_or_step_of_clear (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (before after : ((reactiveApplication timeouts) leaks).Control)
    (joint : Player → Option ((reactiveApplication timeouts) leaks).Action)
    (supported : some after ∈ (((reactiveApplication timeouts) leaks).transition
      initial horizon scheduler (some before) joint).support)
    (clear : after.execution.application.config.defaulted = ∅) :
    after.execution.application.config = before.execution.application.config ∨
      ∃ (event : graph.EventId) (ready : before.execution.application.config.cut.Ready event)
        (action : graph.Action event), after.execution.application.config ∈
          (before.execution.application.config.step event ready action).support := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
      exact Or.inl ((reactive_respond_application timeouts) leaks execution who _).1
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
          exact Or.inl rfl
      | succ remaining =>
          obtain ⟨command, _selected, moved⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
          obtain ⟨next, reached, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          exact reactive_environmentStep_config_eq_or_step timeouts leaks execution next command
            reached clear

/-- No physical transition can restore a publicly defaulted player. -/
theorem reactive_protocol_defaulted_mono (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (before after : ((reactiveApplication timeouts) leaks).Control)
    (joint : Player → Option ((reactiveApplication timeouts) leaks).Action)
    (supported : some after ∈ (((reactiveApplication timeouts) leaks).transition
      initial horizon scheduler (some before) joint).support) :
    before.execution.application.config.defaulted ⊆ after.execution.application.config.defaulted :=
  EventGraph.Config.Step.path_defaulted_mono
    (reactive_protocol_graph_steps timeouts leaks initial horizon scheduler before after joint
      supported)

/-- An accepted authentic opening records true, even when its publication fails.
Automatic completion preserves that authoritative record. -/
theorem reactiveHandle_opening_decision
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (accepted : ((reactiveApplication timeouts) leaks).handle state
      ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩ = some next) :
    ∃ defaultEvent, (⟨event,
        some (cast (congrArg EventField.Action outputEq.symm) true), defaultEvent⟩ :
        graph.Completion) ∈ next.config.history := by
  obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
  obtain ⟨active, ready, timely, owner', payload', binding', checks', outputEq', codeEq',
    value, result, actualNode, sender, owned, associated, rawEq, fixed, stored, resolved,
    nativeEq⟩ := (handle_opening_iff timeouts state native id event candidate raw).mp handled
  rw [node] at actualNode
  cases actualNode
  have actor := nodeView_resolve_actor outputEq codeEq
  change (graph.nodes event).actor = some owner at actor
  have activeOwner : owner ∉ state.config.defaulted := by simpa only [sender] using active
  have decision : state.config.actualDecision event
      (cast (congrArg EventField.Action outputEq.symm) true) =
        some (cast (congrArg EventField.Action outputEq.symm) true) := by
    change (graph.nodes event).actualDecision state.config.defaulted _ = _
    simp only [EventCode.actualDecision, actor, ite_eq_right activeOwner]
  obtain ⟨tail, historyEq⟩ :=
    EventGraph.Config.Step.path_history_prefix native.drain_graph_steps
  rw [nextEq] at historyEq
  refine ⟨(graph.nodes event).defaultEvent
    (cast (congrArg EventField.Action outputEq.symm) true)
    (cast (congrArg EventField.Value outputEq.symm) result), ?_⟩
  rw [← historyEq]
  apply List.mem_append_left
  rw [nativeEq]
  simp only [State.complete, Config.complete_history, decision]
  exact List.mem_append_right _ (List.mem_singleton_self _)


private theorem environment_primary_or_stutter (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (before after : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (quiescent : ∀ event, ¬ before.application.AutomaticReady event)
    (reached : after ∈ (before.environmentStep ((reactiveApplication timeouts) leaks)
      command).support) :
    after.application.config = before.application.config ∨
      ∃ (event : graph.EventId) (ready : before.application.config.cut.Ready event)
        (action : graph.Action event) (native : State graph),
        native.config ∈ (before.application.config.step event ready action).support ∧
          after.application.config = native.drain.config := by
  have drainStutter (native : State graph) (same : native.config = before.application.config) :
      native.drain.config = before.application.config := by
    rw [native.drain_eq_of_clear (fun event eligible => quiescent event (by
      simpa only [State.AutomaticReady, same] using eligible)), same]
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst after
      exact Or.inl rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact Or.inl rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst after
      cases found : before.network.lookup id with
      | none =>
          left
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
      | some message =>
          cases accepted :
              ((reactiveApplication timeouts) leaks).handle before.application message with
          | none =>
              left
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, accepted, Option.getD_none]
          | some state =>
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
              obtain ⟨event, _, ready, action, moved⟩ :=
                handle_config_mem_step timeouts before.application native _ handled
              refine Or.inr ⟨event, ready, action, native, moved, ?_⟩
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, accepted, Option.getD_some]
              rw [drained]
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep timeouts before.application operation).map
        State.drain).support at changed
      obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
      cases operation with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff] at moved
          subst native
          exact Or.inl (drainStutter _ rfl)
      | executeSample event =>
          rcases (environmentStep_executeSample_config_activated timeouts before.application
            native event moved).2 with ⟨same, _⟩ | ⟨ready, action, sampled, _⟩
          · exact Or.inl (drainStutter native same)
          · exact Or.inr ⟨event, ready, action, native, sampled, rfl⟩
      | expire event =>
          rcases environmentStep_expire_config_eq_or_mem_step timeouts before.application native
            event moved with same | ⟨ready, action, expired⟩
          · exact Or.inl (drainStutter native same)
          · exact Or.inr ⟨event, ready, action, native, expired, rfl⟩

private theorem round_primary_or_stutter (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (before after : ((reactiveApplication timeouts) leaks).Execution)
    (quiescent : ∀ event, ¬ before.application.AutomaticReady event)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).round scheduler players
      before).support) :
    after.application.config = before.application.config ∨
      ∃ (event : graph.EventId) (ready : before.application.config.cut.Ready event)
        (action : graph.Action event) (native : State graph),
        native.config ∈ (before.application.config.step event ready action).support ∧
          after.application.config = native.drain.config := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨middle, moved, resumed⟩ := (PMF.mem_support_bind_iff _ _ _).mp dispatched
  have configEq : after.application.config = middle.application.config := by
    cases actor : command.actor? app with
    | none =>
        change after ∈ (app.resume players (command.actor? app) middle).support at resumed
        simp only [actor, ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
        cases resumed
        rfl
    | some who =>
        change after ∈ (app.resume players (command.actor? app) middle).support at resumed
        rw [actor] at resumed
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
        exact (reactive_respond_application timeouts leaks middle who response).1
  rw [configEq]
  exact environment_primary_or_stutter timeouts leaks before middle command quiescent moved

/-- At a unique ready event of a quiescent state, a completed stopped run is one
supported primary graph step followed by native automatic completion. Arbitrary
earlier rounds may stutter without changing the starting graph configuration. -/
theorem runUntil_completed_primary_drain (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (count : Nat)
    (before after : ((reactiveApplication timeouts) leaks).Execution)
    (ready : before.application.config.cut.Ready event)
    (unique : ∀ query, before.application.config.cut.Ready query → query = event)
    (quiescent : ∀ query, ¬ before.application.AutomaticReady query)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun current => event ∈ current.application.config.cut.completed) count before).support)
    (completed : event ∈ after.application.config.cut.completed) :
    ∃ (action : graph.Action event) (native : State graph),
      native.config ∈ (before.application.config.step event ready action).support ∧
        after.application.config = native.drain.config := by
  induction count generalizing before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (ready.1 completed).elim
  | succ count ih =>
      simp only [ReactiveApplication.runUntil, ready.1, ite_false] at reached
      obtain ⟨middle, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      by_cases done : event ∈ middle.application.config.cut.completed
      · rw [((reactiveApplication timeouts) leaks).runUntil_of_stop scheduler players _ count
          middle done, PMF.mem_support_pure_iff] at rest
        subst after
        rcases round_primary_or_stutter timeouts leaks scheduler players before middle quiescent
          moved with same | ⟨query, queryReady, action, native, primary, drained⟩
        · exact (ready.1 (same ▸ done)).elim
        · cases unique query queryReady
          exact ⟨action, native, primary, drained⟩
      · have same := reactive_round_config_eq_of_pending timeouts leaks scheduler players event
          before middle unique done moved
        obtain ⟨action, native, primary, drained⟩ := ih middle (same ▸ ready)
          (by simpa only [same] using unique)
          (by simpa only [State.AutomaticReady, same] using quiescent) rest
        refine ⟨action, native, ?_, drained⟩
        simpa only [same] using primary

/-- A fixed whole-continuation law determines the actual primary decision of
every completed stopped run; automatic completion may extend its endpoint. -/
theorem runUntil_fixed_primary_drain
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (count : Nat)
    (before : ((reactiveApplication timeouts) leaks).Execution)
    (ready : before.application.config.cut.Ready event)
    (unique : ∀ query, before.application.config.cut.Ready query → query = event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (active : owner ∉ before.application.config.defaulted)
    (quiescent : ∀ query, ¬before.application.AutomaticReady query)
    (action : graph.Action event) (plan : graph.EventPlan)
    (law : (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count before).bind
        (fun final => graph.runPlan plan final.application.config.remaining
          final.application.config) =
      (before.application.config.step event ready action).bind
        (fun config => graph.runPlan plan config.remaining config))
    (completed : ∀ final ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count before).support,
      event ∈ final.application.config.cut.completed) :
    ∀ final ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count before).support,
      ∃ native : State graph,
        native.config ∈ (before.application.config.step event ready action).support ∧
          final.application.config = native.drain.config := by
  let app := (reactiveApplication timeouts) leaks
  let read := fun config : graph.Config =>
    config.history.find? (fun record => decide (record.event = event))
  let phase := app.runUntil scheduler players
    (fun final => event ∈ final.application.config.cut.completed) count before
  have findBefore : read before.application.config = none := by
    cases selected : before.application.config.history.find?
        (fun record => decide (record.event = event)) with
    | none => exact selected
    | some record =>
        have member := List.mem_of_find?_eq_some selected
        have matching : record.event = event := by
          simpa only [decide_eq_true_eq] using List.find?_some selected
        have present : event ∈ before.application.config.history.map EventCompletion.event :=
          List.mem_map.mpr ⟨record, member, matching⟩
        exact (ready.1 ((before.application.config.history_exact event).mp present)).elim
  have kernel (config : graph.Config) (done : event ∈ config.cut.completed) :
      (graph.runPlan plan config.remaining config).map read = PMF.pure (read config) := by
    calc
      _ = (graph.runPlan plan config.remaining config).map (fun _ => read config) := by
        apply map_congr_on_support _
        intro after reached
        exact runPlan_completed_record plan config.remaining config after event done reached
      _ = _ := pmf_map_fun_const _ _
  obtain ⟨target, targetLaw⟩ := before.application.config.step_eq_pure_of_actor event ready action
    owner owned
  have targetSupport : target ∈ (before.application.config.step event ready action).support := by
    rw [targetLaw]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨output, _outputEq, history⟩ := before.application.config.step_completion event ready
    action target targetSupport
  rw [before.application.config.actualDecision_of_active event owner owned active action] at history
  let expected := EventGraph.completion graph event (some action) output
  have targetFind : read target = some expected := by
    dsimp only [read]
    rw [history, List.find?_append]
    have absent := findBefore
    dsimp only [read] at absent
    rw [absent]
    simp [expected, EventGraph.completion]
  have targetDone : event ∈ target.cut.completed := by
    rw [before.application.config.step_cut event ready action target targetSupport,
      EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have project : phase.bind (fun final =>
      (graph.runPlan plan final.application.config.remaining final.application.config).map read) =
      phase.map (fun final => read final.application.config) := by
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro final reached
    exact kernel _ (completed final reached)
  have mapped := congrArg (PMF.map read) law
  simp only [PMF.map_bind] at mapped
  rw [targetLaw, PMF.pure_bind] at mapped
  change phase.bind (fun final =>
      (graph.runPlan plan final.application.config.remaining final.application.config).map read) =
    (graph.runPlan plan target.remaining target).map read at mapped
  rw [project, kernel target targetDone, targetFind] at mapped
  intro final reached
  have seen : read final.application.config ∈
      (phase.map (fun final => read final.application.config)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
  rw [mapped, PMF.mem_support_pure_iff] at seen
  obtain ⟨actualAction, native, primary, drained⟩ := runUntil_completed_primary_drain timeouts
    leaks scheduler players event count before final ready unique quiescent reached
      (completed final reached)
  obtain ⟨actualValue, _actualOutput, nativeHistory⟩ := before.application.config.step_completion
    event ready actualAction native.config primary
  have nativeFind : read native.config = some (EventGraph.completion graph event
      (before.application.config.actualDecision event actualAction) actualValue) := by
    dsimp only [read]
    have absent := findBefore
    dsimp only [read] at absent
    rw [nativeHistory, List.find?_append, absent]
    simp [EventGraph.completion]
  obtain ⟨extra, historyGrowth⟩ := Config.Step.path_history_prefix native.drain_graph_steps
  have finalFind : read final.application.config = some (EventGraph.completion graph event
      (before.application.config.actualDecision event actualAction) actualValue) := by
    dsimp only [read]
    rw [drained, ← historyGrowth, List.find?_append]
    have found := nativeFind
    dsimp only [read] at found
    rw [found]
    rfl
  have recordEq := Option.some.inj (finalFind.symm.trans seen)
  have packed := congrArg (fun record : graph.Completion =>
    (⟨record.event, record.decision⟩ : Σ event, Option (graph.Action event))) recordEq
  have decisionEq := eq_of_heq (Sigma.mk.inj packed).2
  change before.application.config.actualDecision event actualAction = some action at decisionEq
  rw [before.application.config.actualDecision_of_active event owner owned active actualAction]
    at decisionEq
  have sameAction := Option.some.inj decisionEq
  rw [sameAction] at primary
  exact ⟨native, primary, drained⟩

/-- A quiescent native protocol transition retains its graph configuration or
performs one supported primary completion followed by automatic service. -/
theorem reactive_protocol_primary_or_stutter (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (before after : ((reactiveApplication timeouts) leaks).Control)
    (joint : Player → Option ((reactiveApplication timeouts) leaks).Action)
    (quiescent : ∀ event, ¬ before.execution.application.AutomaticReady event)
    (supported : some after ∈ (((reactiveApplication timeouts) leaks).transition
      initial horizon scheduler (some before) joint).support) :
    after.execution.application.config = before.execution.application.config ∨
      ∃ (event : graph.EventId) (ready : before.execution.application.config.cut.Ready event)
        (action : graph.Action event) (native : State graph),
        native.config ∈ (before.execution.application.config.step event ready action).support ∧
          after.execution.application.config = native.drain.config := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
      exact Or.inl ((reactive_respond_application timeouts) leaks execution who _).1
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
          exact Or.inl rfl
      | succ remaining =>
          obtain ⟨command, _selected, moved⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
          obtain ⟨next, reached, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          exact environment_primary_or_stutter timeouts leaks execution next command
            quiescent reached

private theorem handle_binding_clear
    {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
    (state next : EventGraphRuntime.State graph) (message : Message Player (Payload graph))
    (clear : state.config.defaulted = ∅)
    (bindings : ∀ event, state.config.cut.Ready event →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (accepted : handle timeouts state message = some next) :
    next.config.defaulted = ∅ ∧ ∃ (event : graph.EventId) (ready : state.config.cut.Ready event),
      next.config.cut = state.config.cut.complete event ready := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      obtain ⟨_active, ready, _timely, owner, payload, outputEq, codeEq, _view, _sender,
        _handleOwner, _vacant, _unused, nextEq⟩ :=
        (handle_commitment_iff timeouts state next id event candidate).mp accepted
      rw [nextEq]
      refine ⟨?_, event, ready, rfl⟩
      change (state.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (some (state.bindingResult candidate payload)))
        (cast (congrArg EventField.Value outputEq.symm)
          (state.bindingResult candidate payload))).defaults.defaulted = ∅
      rw [EventGraph.Config.complete_defaults, state.config.completion_bind_some_defaultEvent
        event owner payload outputEq codeEq, DefaultHistory.defaulted_record_none]
      exact clear
  | opening event candidate raw =>
      obtain ⟨_active, ready, _timely, owner, payload, binding, checks, outputEq, _codeEq,
        _value, _result, _view, _sender, _handleOwner, _associated, _rawEq, _verified,
        _stored, _resolved, _nextEq⟩ :=
        (handle_opening_iff timeouts state next id event candidate raw).mp accepted
      obtain ⟨other, ty, kind⟩ := bindings event ready
      cases kind.symm.trans outputEq

private theorem environment_binding_stutters
    {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
    (state next : EventGraphRuntime.State graph) (command : EnvironmentCommand graph)
    (bindings : ∀ event, state.config.cut.Ready event →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (timely : ∀ event, state.config.cut.Ready event → state.WithinDeadline timeouts event)
    (reached : next ∈ (environmentStep timeouts state command).support) :
    next.config = state.config := by
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | executeSample event =>
      by_cases ready : state.config.cut.Ready event
      · obtain ⟨owner, payload, outputEq⟩ := bindings event ready
        rw [environmentStep_executeSample_of_nonsample timeouts state event ready] at reached
        · cases (PMF.mem_support_pure_iff _ _).mp reached
          rfl
        · intro ty law kind _code _node
          cases outputEq.symm.trans kind
      · rw [environmentStep_executeSample_of_not_ready timeouts state event ready] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        rfl
  | expire event =>
      by_cases ready : state.config.cut.Ready event
      · have within := timely event ready
        have unchanged : expire timeouts state event = state := by
          unfold expire
          rw [dite_eq_left ready]
          cases activated : state.activatedAt event with
          | none => rfl
          | some entered =>
              have early : state.clock - entered < timeouts.duration event := by
                simpa only [State.WithinDeadline, activated] using within
              simp only [Nat.not_le.mpr early, ↓reduceDIte]
        change next ∈ (PMF.pure (expire timeouts state event)).support at reached
        rw [unchanged, PMF.mem_support_pure_iff] at reached
        subst next
        rfl
      · rw [environmentStep_expire_of_not_ready timeouts state event ready] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        rfl

private theorem reactive_environment_bindings_clear
    {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (clear : execution.application.config.defaulted = ∅)
    (bindings : ∀ event, execution.application.config.cut.Ready event →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (timely : ∀ event, execution.application.config.cut.Ready event →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈ (execution.environmentStep ((reactiveApplication timeouts) leaks)
      command).support) : next.application.config.defaulted = ∅ := by
  let app := (reactiveApplication timeouts) leaks
  apply app.environmentStep_cases execution next command reached
    (predicate := fun _ next => next.application.config.defaulted = ∅)
  · exact clear
  · exact fun _ _ _ => clear
  · intro id
    change (execution.includePending app id).application.config.defaulted = ∅
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases found : execution.network.lookup id with
    | none => exact clear
    | some message =>
        change (Option.getD (app.handle execution.application message)
          execution.application).config.defaulted = ∅
        cases accepted : app.handle execution.application message with
        | none => exact clear
        | some state =>
            obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
            have nativeClear := (handle_binding_clear timeouts execution.application native
              ⟨message.id, message.payload.call⟩ clear bindings handled).1
            rw [← drained, native.drain_eq_of_empty nativeClear]
            exact nativeClear
  · intro operation state changed
    change state ∈ ((environmentStep timeouts execution.application operation).map
      EventGraphRuntime.State.drain).support at changed
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
    have same := environment_binding_stutters timeouts execution.application native operation
      bindings timely moved
    have nativeClear : native.config.defaulted = ∅ := by rw [same]; exact clear
    rw [native.drain_eq_of_empty nativeClear]
    exact nativeClear

/-- If every currently ready event is a binding within its deadline, one native round
creates no public default and performs at most one graph completion. -/
theorem reactive_round_bindings_clear
    {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (clear : execution.application.config.defaulted = ∅)
    (bindings : ∀ event, execution.application.config.cut.Ready event →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (timely : ∀ event, execution.application.config.cut.Ready event →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈ (((reactiveApplication timeouts) leaks).round scheduler players
      execution).support) :
    next.application.config.defaulted = ∅ ∧
      (next.application.config = execution.application.config ∨
        ∃ (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
          (action : graph.Action event), next.application.config ∈
            (execution.application.config.step event ready action).support) := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have middleClear := reactive_environment_bindings_clear timeouts leaks execution middle command
    clear bindings timely moved
  have primary := reactive_environmentStep_config_eq_or_step timeouts leaks execution middle
    command moved middleClear
  cases actor : command.actor? app with
  | none =>
      rw [show app.resume players (command.actor? app) middle = PMF.pure middle by
        rw [actor]; rfl, PMF.mem_support_pure_iff] at resumed
      subst next
      exact ⟨middleClear, primary⟩
  | some owner =>
      change next ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor] at resumed
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      have same := (reactive_respond_application timeouts leaks middle owner response).1
      rw [same]
      exact ⟨middleClear, primary⟩


/-- A round ending clear has no automatic tail and changes at most one graph event. -/
theorem reactive_round_config_eq_or_step_of_clear
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (before after : ((reactiveApplication timeouts) leaks).Execution)
    (reached : after ∈ (((reactiveApplication timeouts) leaks).round scheduler players
      before).support) (clear : after.application.config.defaulted = ∅) :
    after.application.config = before.application.config ∨
      ∃ (event : graph.EventId) (ready : before.application.config.cut.Ready event)
        (action : graph.Action event), after.application.config ∈
          (before.application.config.step event ready action).support := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have same : after.application.config = middle.application.config := by
    cases actor : command.actor? app with
    | none =>
        rw [show app.resume players (command.actor? app) middle = PMF.pure middle by
          rw [actor]; rfl, PMF.mem_support_pure_iff] at resumed
        subst after
        rfl
    | some who =>
        change after ∈ (app.resume players (command.actor? app) middle).support at resumed
        rw [actor] at resumed
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
        exact (reactive_respond_application timeouts leaks middle who response).1
  have middleClear : middle.application.config.defaulted = ∅ := by rw [← same]; exact clear
  have primary := reactive_environmentStep_config_eq_or_step timeouts leaks before middle command
    moved middleClear
  rwa [← same] at primary

/-- A stopped block run ending clear remains within its source interval.
No restriction is placed on the raw native policies. -/
theorem blockRun_within_of_clear
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (stop : ((reactiveApplication timeouts) leaks).Execution → Prop) [DecidablePred stop]
    {start finish : Nat} (shaped : BlockShaped (graph := graph) start finish)
    (completed : ∀ current, BlockDone finish current.application.config → stop current) :
    ∀ count (origin final : ((reactiveApplication timeouts) leaks).Execution),
      origin.application.config.cut.Within start finish →
      final ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
        stop count origin).support →
      final.application.config.defaulted = ∅ →
      final.application.config.cut.Within start finish := by
  classical
  let app := (reactiveApplication timeouts) leaks
  intro count
  induction count with
  | zero =>
      intro origin final within reached _
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact within
  | succ count ih =>
      intro origin final within reached clear
      by_cases halted : stop origin
      · rw [app.runUntil_of_stop scheduler players stop _ origin halted,
          PMF.mem_support_pure_iff] at reached
        subst final
        exact within
      · change final ∈ (if stop origin then PMF.pure origin else
          (app.round scheduler players origin).bind
            (app.runUntil scheduler players stop count)).support at reached
        rw [ite_eq_right halted] at reached
        obtain ⟨middle, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
        have tailPath := reactive_runUntil_graph_steps timeouts leaks scheduler players stop
          count middle final rest
        have middleClear : middle.application.config.defaulted = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro owner member
          have later := Config.Step.path_defaulted_mono tailPath member
          simp only [clear, Finset.notMem_empty] at later
        have inside : InBlock start finish origin.application.config :=
          ⟨within.1, fun event late completed => Nat.not_lt.mpr late (within.2 event completed)⟩
        have primary := reactive_round_config_eq_or_step_of_clear timeouts leaks scheduler players
          origin middle moved middleClear
        have nextWithin : middle.application.config.cut.Within start finish := by
          rcases primary with same | ⟨event, ready, action, selected⟩
          · rw [same]
            exact within
          · rw [origin.application.config.step_cut event ready action middle.application.config
              selected]
            exact within.complete event ready
              (shaped _ inside (fun done => halted (completed origin done)) event ready).2
        exact ih middle final nextWithin rest clear

/-- Stopping at a clear target completion leaves every dependent event unfinished. -/
theorem reactive_runUntil_dependent_pending_of_clear
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (target later : graph.EventId) (dependent : target ∈ graph.order.predecessors later) :
    ∀ (count : Nat) (origin final : ((reactiveApplication timeouts) leaks).Execution),
      target ∉ origin.application.config.cut.completed →
      final ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun current => target ∈ current.application.config.cut.completed) count origin).support →
      final.application.config.defaulted = ∅ →
      later ∉ final.application.config.cut.completed := by
  classical
  let app := (reactiveApplication timeouts) leaks
  have future {config : graph.Config} (pending : target ∉ config.cut.completed) :
      later ∉ config.cut.completed :=
    fun done => pending (config.cut.predecessor_closed done dependent)
  intro count
  induction count with
  | zero =>
      intro origin final pending reached _clear
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact future pending
  | succ count ih =>
      intro origin final pending reached clear
      simp only [ReactiveApplication.runUntil, pending, ite_false] at reached
      obtain ⟨middle, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      by_cases stopped : target ∈ middle.application.config.cut.completed
      · rw [app.runUntil_of_stop scheduler players _ count middle stopped,
          PMF.mem_support_pure_iff] at rest
        subst final
        rcases reactive_round_config_eq_or_step_of_clear timeouts leaks scheduler players origin
          middle moved clear with same | ⟨event, ready, action, stepped⟩
        · exact future (same ▸ pending)
        · have cuts := origin.application.config.step_cut event ready action
            middle.application.config stepped
          have sameEvent : target = event := by
            rw [cuts, EventOrder.Cut.mem_complete] at stopped
            exact stopped.resolve_right pending
          have different : later ≠ event := by
            intro equal
            have smaller := graph.order.predecessor_lt dependent
            rw [sameEvent, equal] at smaller
            exact (lt_irrefl _ smaller)
          rw [cuts, EventOrder.Cut.mem_complete]
          exact not_or.mpr ⟨different, future pending⟩
      · exact ih middle final stopped rest clear


private theorem environment_binding_defaulted_subset
    (timeouts : EventTimeouts graph) (state next : State graph)
    (command : EnvironmentCommand graph) (focal : Player)
    (clear : state.config.defaulted = ∅)
    (bindings : ∀ event, state.config.cut.Ready event →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (timely : ∀ event owner, state.config.cut.Ready event → graph.actor? event = some owner →
      owner ≠ focal → state.WithinDeadline timeouts event)
    (reached : next ∈ (environmentStep timeouts state command).support) :
    next.config.defaulted ⊆ {focal} := by
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rw [clear]
      exact Finset.empty_subset _
  | executeSample event =>
      by_cases ready : state.config.cut.Ready event
      · obtain ⟨owner, payload, outputEq⟩ := bindings event ready
        rw [environmentStep_executeSample_of_nonsample timeouts state event ready] at reached
        · cases (PMF.mem_support_pure_iff _ _).mp reached
          rw [clear]
          exact Finset.empty_subset _
        · intro ty law kind _code _node
          cases outputEq.symm.trans kind
      · rw [environmentStep_executeSample_of_not_ready timeouts state event ready,
          PMF.mem_support_pure_iff] at reached
        cases reached
        rw [clear]
        exact Finset.empty_subset _
  | expire event =>
      rcases environmentStep_expire_config_eq_or_mem_step timeouts state next event reached with
        unchanged | ⟨ready, action, stepped⟩
      · rw [unchanged, clear]
        exact Finset.empty_subset _
      obtain ⟨owner, payload, binding⟩ := bindings event ready
      have owned : graph.actor? event = some owner :=
        EventCode.actor_eq_of_binding (graph.nodes event) binding
      by_cases same : owner = focal
      · intro other inactive
        have active : other ∉ state.config.defaulted := by rw [clear]; simp
        have actor := state.config.step_new_default_actor next.config event ready action stepped
          other active inactive
        have equal : other = owner := Option.some.inj (actor.symm.trans owned)
        simp only [Finset.mem_singleton]
        exact equal.trans same
      · have within := timely event owner ready owned same
        unfold State.WithinDeadline at within
        cases activated : state.activatedAt event with
        | none => rw [activated] at within; exact within.elim
        | some entered =>
            rw [activated] at within
            rw [environmentStep_expire_of_not_due timeouts state event ready entered activated
              (by omega), PMF.mem_support_pure_iff] at reached
            cases reached
            rw [clear]
            exact Finset.empty_subset _

private theorem reactive_environment_bindings_defaulted_subset
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command) (focal : Player)
    (clear : execution.application.config.defaulted = ∅)
    (bindings : ∀ event, execution.application.config.cut.Ready event →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ≠ focal →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈ (execution.environmentStep ((reactiveApplication timeouts) leaks)
      command).support) : next.application.config.defaulted ⊆ {focal} := by
  let app := (reactiveApplication timeouts) leaks
  apply app.environmentStep_cases execution next command reached
    (predicate := fun _ next => next.application.config.defaulted ⊆ {focal})
  · rw [clear]; exact Finset.empty_subset _
  · intro _ _ _; rw [clear]; exact Finset.empty_subset _
  · intro id
    change (execution.includePending app id).application.config.defaulted ⊆ {focal}
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases found : execution.network.lookup id with
    | none => rw [clear]; exact Finset.empty_subset _
    | some message =>
        change (Option.getD (app.handle execution.application message)
          execution.application).config.defaulted ⊆ {focal}
        cases accepted : app.handle execution.application message with
        | none =>
            change execution.application.config.defaulted ⊆ {focal}
            rw [clear]
            exact Finset.empty_subset _
        | some state =>
            change state.config.defaulted ⊆ {focal}
            obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
            have nativeClear := (handle_binding_clear timeouts execution.application native
              ⟨message.id, message.payload.call⟩ clear bindings handled).1
            rw [← drained, native.drain_defaulted, nativeClear]
            exact Finset.empty_subset _
  · intro operation state changed
    change state ∈ ((environmentStep timeouts execution.application operation).map
      State.drain).support at changed
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
    rw [native.drain_defaulted]
    exact environment_binding_defaulted_subset timeouts execution.application native operation
      focal clear bindings timely moved

/-- Protected foreign bindings leave only the focal owner exposed to default in a round. -/
theorem reactive_round_bindings_clear_or_focal_default
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (execution next : ((reactiveApplication timeouts) leaks).Execution) (focal : Player)
    (clear : execution.application.config.defaulted = ∅)
    (bindings : ∀ event, execution.application.config.cut.Ready event →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (timely : ∀ event owner, execution.application.config.cut.Ready event →
      graph.actor? event = some owner → owner ≠ focal →
      execution.application.WithinDeadline timeouts event)
    (reached : next ∈ (((reactiveApplication timeouts) leaks).round scheduler players
      execution).support) :
    focal ∈ next.application.config.defaulted ∨
      (next.application.config.defaulted = ∅ ∧
        (next.application.config = execution.application.config ∨
          ∃ (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
            (action : graph.Action event), next.application.config ∈
              (execution.application.config.step event ready action).support)) := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have middleSubset := reactive_environment_bindings_defaulted_subset timeouts leaks execution
    middle command focal clear bindings timely moved
  have same : next.application.config = middle.application.config := by
    cases actor : command.actor? app with
    | none =>
        rw [show app.resume players (command.actor? app) middle = PMF.pure middle by
          rw [actor]; rfl, PMF.mem_support_pure_iff] at resumed
        subst next
        rfl
    | some owner =>
        change next ∈ (app.resume players (command.actor? app) middle).support at resumed
        rw [actor] at resumed
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
        exact (reactive_respond_application timeouts leaks middle owner response).1
  by_cases failed : focal ∈ next.application.config.defaulted
  · exact Or.inl failed
  have nextClear : next.application.config.defaulted = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro other inactive
    rw [same] at inactive
    have equal := Finset.mem_singleton.mp (middleSubset inactive)
    subst other
    exact failed (same ▸ inactive)
  exact Or.inr ⟨nextClear, reactive_round_config_eq_or_step_of_clear timeouts leaks scheduler
    players execution next reached nextClear⟩

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveInvariant
import Interaction.ReactiveStopping
import Vegas.Pending.ReactiveRuntime

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
theorem reactive_respond_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    (execution.respond (runtime.reactiveApplication leaks) who action).application.config =
        execution.application.config ∧
      (execution.respond (runtime.reactiveApplication leaks) who action).application.publicView =
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
theorem environmentStep_graph_steps (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (supported : next ∈ (environmentStep runtime state command).support) :
    Relation.ReflTransGen EventGraph.Config.Step state.config next.config := by
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at supported
      subst next
      exact .refl
  | executeSample event =>
      rcases (environmentStep_executeSample_config_activated runtime state next event
        supported).2 with same | ⟨ready, action, moved, _⟩
      · rw [same.1]
      · exact .single ⟨event, ready, action, moved⟩
  | expire event =>
      rcases (environmentStep_expire_config_activated runtime state next event supported).2
        with same | ⟨ready, action, moved, _⟩
      · rw [same.1]
      · exact .single ⟨event, ready, action, moved⟩

/-- All application operations follow finite paths of the sole graph executor. -/
theorem reactiveApplication_graphSteps (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).StepRelation (fun before after =>
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
      handle_config_mem_step runtime state native ⟨message.id, message.payload.call⟩ handled
    exact (Relation.ReflTransGen.single ⟨event, ready, action, moved⟩).trans
      native.drain_graph_steps
  environment state command next supported := by
    change next ∈ ((environmentStep runtime state command).map State.drain).support at supported
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ supported
    exact (environmentStep_graph_steps runtime state native command moved).trans
      native.drain_graph_steps

/-- A scheduler round follows a finite path of the graph executor, including
all automatic completions triggered by its command. -/
theorem reactive_round_graph_steps (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (before after : (runtime.reactiveApplication leaks).Execution)
    (reached : after ∈ ((runtime.reactiveApplication leaks).round scheduler players
      before).support) :
    Relation.ReflTransGen Config.Step before.application.config after.application.config := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have path := (runtime.reactiveApplication_graphSteps leaks).environmentStep
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
        ((runtime.reactiveApplication_graphSteps leaks).respond middle who response)

/-- A round cannot change the graph configuration before its unique ready
event completes, even when the command may perform automatic completion. -/
theorem reactive_round_config_eq_of_pending (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (event : graph.EventId) (before after : (runtime.reactiveApplication leaks).Execution)
    (unique : ∀ other, before.application.config.cut.Ready other → other = event)
    (pending : event ∉ after.application.config.cut.completed)
    (reached : after ∈ ((runtime.reactiveApplication leaks).round scheduler players
      before).support) : after.application.config = before.application.config :=
  Config.Step.path_eq_of_ready_of_not_completed event unique pending
    (reactive_round_graph_steps runtime leaks scheduler players before after reached)

/-- Every stopped native execution follows a finite supported graph path.
The path may contain several automatic completions in one scheduler round. -/
theorem reactive_runUntil_graph_steps (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (stop : (runtime.reactiveApplication leaks).Execution → Prop) [DecidablePred stop]
    (count : Nat) (before after : (runtime.reactiveApplication leaks).Execution)
    (reached : after ∈ ((runtime.reactiveApplication leaks).runUntil scheduler players
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
        exact (reactive_round_graph_steps runtime leaks scheduler players before middle moved).trans
          (ih middle rest)

/-- A native command ending before any public default stutters or performs
one supported graph step. Automatic tails are empty in this internally clear region. -/
theorem reactive_environmentStep_config_eq_or_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
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
              (runtime.reactiveApplication leaks).handle execution.application message with
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
                handle_config_mem_step runtime execution.application native _ handled
              refine Or.inr ⟨event, ready, action, ?_⟩
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
                found, accepted, Option.getD_some]
              rw [← drained, undrained native state drained empty]
              exact moved
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep runtime execution.application operation).map
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
          rcases (environmentStep_executeSample_config_activated runtime execution.application
            native event moved).2 with ⟨same, _⟩ | ⟨ready, action, sampled, _⟩
          · exact Or.inl same
          · exact Or.inr ⟨event, ready, action, sampled⟩
      | expire event =>
          rcases environmentStep_expire_config_eq_or_mem_step runtime execution.application native
            event moved with same | ⟨ready, action, expired⟩
          · exact Or.inl same
          · exact Or.inr ⟨event, ready, action, expired⟩

/-- Arbitrary raw responses and scheduler choices refine finite supported graph paths. -/
theorem reactive_protocol_graph_steps (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (before after : (runtime.reactiveApplication leaks).Control)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (supported : some after ∈ ((runtime.reactiveApplication leaks).transition
      initial horizon scheduler (some before) joint).support) :
    Relation.ReflTransGen EventGraph.Config.Step before.execution.application.config
      after.execution.application.config :=
  (reactiveApplication_graphSteps runtime leaks).transition
    initial horizon scheduler before after joint supported

/-- A native protocol transition ending with no public defaults either stutters
or performs one supported graph step. Automatic tails are empty in this region. -/
theorem reactive_protocol_config_eq_or_step_of_clear (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (before after : (runtime.reactiveApplication leaks).Control)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (supported : some after ∈ ((runtime.reactiveApplication leaks).transition
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
      exact Or.inl (runtime.reactive_respond_application leaks execution who _).1
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
          exact reactive_environmentStep_config_eq_or_step runtime leaks execution next command
            reached clear

/-- No physical transition can restore a publicly defaulted player. -/
theorem reactive_protocol_defaulted_mono (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (before after : (runtime.reactiveApplication leaks).Control)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (supported : some after ∈ ((runtime.reactiveApplication leaks).transition
      initial horizon scheduler (some before) joint).support) :
    before.execution.application.config.defaulted ⊆ after.execution.application.config.defaulted :=
  EventGraph.Config.Step.path_defaulted_mono
    (reactive_protocol_graph_steps runtime leaks initial horizon scheduler before after joint
      supported)

/-- An accepted authentic opening records true, even when its publication fails.
Automatic completion preserves that authoritative record. -/
theorem reactiveHandle_opening_decision
    (runtime : EventGraphRuntime graph)
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
    (accepted : (runtime.reactiveApplication leaks).handle state
      ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩ = some next) :
    ∃ defaultEvent, (⟨event,
        some (cast (congrArg EventField.Action outputEq.symm) true), defaultEvent⟩ :
        graph.Completion) ∈ next.config.history := by
  obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
  obtain ⟨active, ready, timely, owner', payload', binding', checks', outputEq', codeEq',
    value, result, actualNode, sender, owned, associated, rawEq, fixed, stored, resolved,
    nativeEq⟩ := (handle_opening_iff runtime state native id event candidate raw).mp handled
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


end Vegas.EventGraphRuntime

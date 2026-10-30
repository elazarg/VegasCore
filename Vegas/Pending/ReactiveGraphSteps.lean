/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveInvariant
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

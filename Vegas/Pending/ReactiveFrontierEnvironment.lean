/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFrontier
import Vegas.EventGraph.Information

/-! # Reactive sampled frontiers through chance, clocks and activation -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A common supported chance draw advances the actual contract and retained
semantic frontier without adding an owned intention or changing own recall. -/
theorem ReactiveFrontier.chance_complete (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (event : graph.EventId) (physicalReady : execution.application.config.cut.Ready event)
    (frontierReady : frontier.cut.Ready event) (chance : graph.actor? event = none)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (physicalSupported : execution.application.config.complete event physicalReady action value ∈
      (execution.application.config.step event physicalReady action).support)
    (frontierSupported : frontier.complete event frontierReady action value ∈
      (frontier.step event frontierReady action).support)
    (entries : List (runtime.reactiveApplication leaks).EnvironmentEntry) :
    runtime.ReactiveFrontier leaks
      { execution with
        application := execution.application.complete event physicalReady action value
        environmentRecall := entries }
      memories (frontier.complete event frontierReady action value) := by
  let next : (runtime.reactiveApplication leaks).Execution :=
    { execution with
      application := execution.application.complete event physicalReady action value
      environmentRecall := entries }
  have history : (runtime.originalConfig leaks next memories).history =
      (runtime.originalConfig leaks execution memories).history ++ [⟨event, action⟩] := by
    change (execution.application.config.history ++ [(⟨event, action⟩ : graph.Completion)]).map
      (runtime.originalCompletion leaks next memories) = _
    rw [List.map_append, List.map_singleton]
    have restored : runtime.originalCompletion leaks next memories ⟨event, action⟩ =
        ⟨event, action⟩ := by
      simp only [originalCompletion, chance]
    rw [restored]
    rfl
  have own (owner : Player) :
      graph.ownCompletions owner (frontier.complete event frontierReady action value).history =
        graph.ownCompletions owner frontier.history := by
    apply graph.ownCompletions_complete_of_not_actor
    simp only [chance, ne_eq, reduceCtorEq, not_false_eq_true]
  constructor
  · exact related.reachable.step event frontierReady action _ frontierSupported
  · exact related.inputs
  · intro query
    change query ∈ insert event frontier.cut.completed ↔
      query ∈ insert event execution.application.config.cut.completed ∨ _
    simp only [Finset.mem_insert, related.domain query]
    tauto
  · apply Config.CompletedOutputAgreement.physical_step _ _ _
      (related.settled.frontier_step _ _ _ event frontierReady action frontierSupported)
      event physicalReady action physicalSupported
    simp
  · intro owner
    rw [own owner]
    exact related.intentions owner
  · intro owner
    change (graph.ownCompletions owner
      (runtime.originalConfig leaks next memories).history).IsPrefix _
    rw [history, own owner]
    simpa only [ownCompletions, List.filter_append, List.filter_cons, List.filter_nil,
      chance, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil] using
      related.recalled owner

/-- The genuine reactive chance command and its semantic frontier step share
one draw and preserve the full sampled-frontier relation on their joint support. -/
theorem ReactiveFrontier.sample_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (event : graph.EventId) (physicalReady : execution.application.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq) :
    ∃ ready : frontier.cut.Ready event,
      ∃ joint : PMF ((runtime.reactiveApplication leaks).Execution × graph.Config),
        joint.map Prod.fst = execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.executeSample event)) ∧
        joint.map Prod.snd = frontier.step event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) ∧
        ∀ pair ∈ joint.support, runtime.ReactiveFrontier leaks pair.1 memories pair.2 := by
  let app := runtime.reactiveApplication leaks
  let action : graph.Action event := cast (congrArg EventField.Action outputEq.symm) PUnit.unit
  have chance : graph.actor? event = none := by
    change (graph.nodes event).actor = none
    rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
    rfl
  have frontierReady : frontier.cut.Ready event := by
    constructor
    · intro completed
      rcases (related.domain event).mp completed with physical | ⟨owner, remembered, kept, named⟩
      · exact physicalReady.1 physical
      · have owned := runtime.prescribedReactivePosterior_owned leaks owner (profile owner)
          (consistent owner) (memories owner) (supportedMemory owner) remembered kept
        rw [named, chance] at owned
        cases owned
    · exact fun predecessor dependency =>
        related.settled.completed_subset _ _ (physicalReady.2 dependency)
  obtain ⟨draw, evaluates⟩ := Option.isSome_iff_exists.mp
    (EventCode.eval?_isSome_of_reads (graph.nodes event) action execution.application.config.store
      (fun _ read => execution.application.config.read_available physicalReady read))
  have frontierEval : (graph.nodes event).eval? action frontier.store = some draw :=
    (related.settled.ready_eval _ _ related.inputs.symm event physicalReady action).symm.trans
      evaluates
  let next (value : (graph.outputLayout event).Value) : app.Execution :=
    { execution with
      application := execution.application.complete event physicalReady action value
      environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .application (.executeSample event)⟩] }
  have actual : execution.environmentStep app (.application (.executeSample event)) =
      draw.map next := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change (environmentStep runtime execution.application (.executeSample event)).map _ = _
    rw [environmentStep_executeSample_eq runtime execution.application event physicalReady
      payload law outputEq codeEq node,
      execution.application.config.step_eq_map_of_eval event physicalReady action draw evaluates]
    simp only [PMF.map_comp]
    rfl
  refine ⟨frontierReady, draw.map (fun value =>
    (next value, frontier.complete event frontierReady action value)), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact actual.symm
  · rw [PMF.map_comp, frontier.step_eq_map_of_eval event frontierReady action draw frontierEval]
    rfl
  · intro pair supported
    obtain ⟨value, positive, rfl⟩ := PMF.support_map .. ▸ supported
    have physicalSupport : execution.application.config.complete event physicalReady action value ∈
        (execution.application.config.step event physicalReady action).support := by
      rw [execution.application.config.step_eq_map_of_eval
          event physicalReady action draw evaluates,
        PMF.support_map]
      exact ⟨value, positive, rfl⟩
    have frontierSupport : frontier.complete event frontierReady action value ∈
        (frontier.step event frontierReady action).support := by
      rw [frontier.step_eq_map_of_eval event frontierReady action draw frontierEval,
        PMF.support_map]
      exact ⟨value, positive, rfl⟩
    exact ReactiveFrontier.chance_complete runtime leaks execution memories frontier related event
      physicalReady frontierReady chance action value physicalSupport frontierSupport
      (next value).environmentRecall

/-- Only the actual graph configuration, own recall and receipts determine
the physical side of a retained semantic frontier. -/
theorem ReactiveFrontier.congr_execution (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (first second : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks first memories frontier)
    (config : first.application.config = second.application.config)
    (recall : first.recall = second.recall) (receipts : first.receipts = second.receipts) :
    runtime.ReactiveFrontier leaks second memories frontier := by
  have history : (runtime.originalConfig leaks first memories).history =
      (runtime.originalConfig leaks second memories).history := by
    simp only [originalConfig, config]
    apply List.map_congr_left
    intro completion _
    unfold originalCompletion
    rw [recall, receipts]
  constructor
  · rw [← config]
    exact related.reachable
  · rw [← config]
    exact related.inputs
  · intro event
    rw [← config]
    exact related.domain event
  · rw [← config]
    exact related.settled
  · exact related.intentions
  · intro owner
    rw [← history]
    exact related.recalled owner

/-- A genuine raw wait records the scheduler command and leaves the sampled
frontier fixed. -/
theorem ReactiveFrontier.wait (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (supported : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) .wait).support) :
    runtime.ReactiveFrontier leaks next memories frontier := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff] at supported
  subst next
  exact related.congr_execution runtime leaks _ _ memories frontier rfl rfl rfl

/-- Learning pending packets at an actual activation changes network knowledge
without resampling an original event or changing a retained frontier. -/
theorem ReactiveFrontier.activate (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier) (who : Player)
    (supported : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) (.activate who)).support) :
    runtime.ReactiveFrontier leaks next memories frontier := by
  rw [ReactiveApplication.Execution.environmentStep, PMF.support_map] at supported
  obtain ⟨updated, supported, rfl⟩ := supported
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
  exact related.congr_execution runtime leaks _ _ memories frontier rfl rfl rfl

/-- An actual clock tick changes only contract timing and scheduler recall. -/
theorem ReactiveFrontier.advanceClock (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (supported : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application .advanceClock)).support) :
    runtime.ReactiveFrontier leaks next memories frontier := by
  simp only [ReactiveApplication.Execution.environmentStep, reactiveApplication,
    environmentStep, PMF.pure_map, PMF.mem_support_pure_iff] at supported
  subst next
  exact related.congr_execution runtime leaks _ _ memories frontier rfl rfl rfl

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveIntentionRecall
import Vegas.EventGraph.SchedulerErasure

/-! # Original-action configurations for reactive proof coupling -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Recover the owner-specific original intention for one physical completion.
Chance completions retain their physical unit action. -/
def originalCompletion (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (completion : graph.Completion) :
    graph.Completion :=
  match graph.actor? completion.event with
  | none => completion
  | some who => runtime.reactiveOriginal leaks who (execution.recall who) (memories who)
      execution.receipts completion

theorem originalCompletion_event (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (completion : graph.Completion) :
    (runtime.originalCompletion leaks execution memories completion).event = completion.event := by
  unfold originalCompletion
  split
  · rfl
  · exact runtime.reactiveOriginal_event ..

/-- A proof configuration retains the actual typed store and cut and restores
original own actions. Its structural coherence follows without a reachability
or desired-law assumption; semantic reachability requires operational induction. -/
def originalConfig (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) : graph.Config where
  inputs := execution.application.config.inputs
  cut := execution.application.config.cut
  outputs := execution.application.config.outputs
  output_available := execution.application.config.output_available
  history := execution.application.config.history.map
    (runtime.originalCompletion leaks execution memories)
  history_nodup := by
    have events : (execution.application.config.history.map
        (runtime.originalCompletion leaks execution memories)).map Completion.event =
        execution.application.config.history.map Completion.event := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro completion _
      exact runtime.originalCompletion_event leaks execution memories completion
    rw [events]
    exact execution.application.config.history_nodup
  history_exact := by
    intro event
    have events : (execution.application.config.history.map
        (runtime.originalCompletion leaks execution memories)).map Completion.event =
        execution.application.config.history.map Completion.event := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro completion _
      exact runtime.originalCompletion_event leaks execution memories completion
    rw [events]
    exact execution.application.config.history_exact event

/-- The shadow own-action list is exactly the full list used by the actual
sampler, retaining private completions and original failed disclosure choices. -/
theorem originalConfig_ownCompletions (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (who : Player) :
    graph.ownCompletions who (runtime.originalConfig leaks execution memories).history =
      (graph.ownCompletions who execution.application.config.history).map
        (runtime.reactiveOriginal leaks who (execution.recall who) (memories who)
          execution.receipts) := by
  change graph.ownCompletions who (execution.application.config.history.map
    (runtime.originalCompletion leaks execution memories)) = _
  induction execution.application.config.history with
  | nil => rfl
  | cons completion rest ih =>
      simp only [ownCompletions, List.map_cons, List.filter_cons]
      rw [runtime.originalCompletion_event]
      by_cases owned : graph.actor? completion.event = some who
      · simp only [owned, decide_true, ↓reduceIte, List.map_cons]
        have first : runtime.originalCompletion leaks execution memories completion =
            runtime.reactiveOriginal leaks who (execution.recall who) (memories who)
              execution.receipts completion := by
          simp only [originalCompletion, owned]
        rw [first]
        exact congrArg (List.cons _) ih
      · simp only [owned, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- The proof configuration realizes the actual sampler's complete original
observation, with the same visible store and completion order. -/
theorem originalConfig_playerObserve (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (who : Player) :
    graph.playerObserve who (runtime.originalConfig leaks execution memories) =
      { graph.playerObserve who execution.application.config with
        ownActions := (graph.ownCompletions who execution.application.config.history).map
          (runtime.reactiveOriginal leaks who (execution.recall who) (memories who)
            execution.receipts) } := by
  apply PlayerObservation.ext
  · change (execution.application.config.history.map
        (runtime.originalCompletion leaks execution memories)).map Completion.event =
        execution.application.config.history.map Completion.event
    simp only [List.map_map]
    apply List.map_congr_left
    intro completion _
    exact runtime.originalCompletion_event leaks execution memories completion
  · rfl
  · exact runtime.originalConfig_ownCompletions leaks execution memories who

/-- A fresh actual prescribed response samples the normalized graph policy at
its original-action proof configuration. Packet emission stays physical; the
retained intention records exactly the sampled graph action. -/
theorem prescribedReactiveResponse_originalConfig (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (who : Player)
    (policy : graph.BehavioralPolicy who) (event : graph.EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fresh : runtime.reactiveAlreadySubmitted leaks (execution.recall who) event = false)
    (undecided : runtime.reactiveAlreadyDecided leaks who (execution.recall who)
      (memories who) event = false)
    (actor : graph.actor? event = some who) :
    runtime.prescribedReactiveResponse leaks who policy (execution.recall who) (memories who)
        (execution.observe (runtime.reactiveApplication leaks) who) =
      (graph.normalizePolicy who policy event actor
        (graph.playerObserve who (runtime.originalConfig leaks execution memories))).map
          (fun action => (runtime.reactiveDecision leaks who event action
            (execution.observe (runtime.reactiveApplication leaks) who).application,
            some (⟨event, action⟩ : graph.Completion))) := by
  have ready := (execution.application.publicView.ownTurn?_spec who event turn).1
  rw [runtime.originalConfig_playerObserve]
  simp only [prescribedReactiveResponse, ReactiveApplication.Execution.observe,
    reactiveApplication, State.playerView, turn, fresh, undecided, Bool.false_or, ↓reduceIte,
    ready, actor, Bool.false_eq_true, dite_eq_left True.intro]
  rfl

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosureStability
import Vegas.Pending.ReactiveOriginalConfig
import Vegas.EventGraph.ForeignCompletionEvaluation

/-! # Causal agreement between sampled frontier outputs and physical settlements -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every fixed action at a ready event retains its exact evaluator through
arbitrary native continuations after the actual response. The proof uses the
immutable original private/public read footprint. -/
theorem reactive_ready_evaluation_continuation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution later : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (physical : (runtime.reactiveApplication leaks).Action)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : later ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) who physical)).support)
    (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
    (action : graph.Action event) :
    (graph.nodes event).eval? action later.application.config.store =
      (graph.nodes event).eval? action execution.application.config.store := by
  have available : ∀ field ∈ (graph.nodes event).readFields,
      (execution.application.config.store field).isSome = true :=
    fun _ member => execution.application.config.read_available ready member
  have response := runtime.reactive_respond_application leaks execution who physical
  have initial : ∀ field ∈ (graph.nodes event).readFields,
      (execution.respond (runtime.reactiveApplication leaks) who physical).application.config.store
          field = execution.application.config.store field ∧
        (execution.respond (runtime.reactiveApplication leaks) who physical).application.accepted
          field = execution.application.accepted field := by
    intro field _
    exact ⟨congrArg (fun config : graph.Config => config.store field) response.1,
      congrFun (congrArg PublicView.accepted response.2) field⟩
  have frame := (ReactiveApplication.Invariant.policyInvariant _
    (runtime.reactiveReadFrameInvariant leaks execution.application
      (graph.nodes event).readFields available) players).runRounds
        scheduler rounds (execution.respond (runtime.reactiveApplication leaks) who physical)
        later initial reached
  exact EventCode.eval?_congr (graph.nodes event) action _ _
    (fun field member => (frame field member).1)

/-- A sampled owned frontier step and its later authentic semantic settlement
write the same typed output. Pending foreign completions and intervening native
play may change other outputs and private histories. -/
theorem sampled_owned_output_eq_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution later : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (who : Player) (physical : (runtime.reactiveApplication leaks).Action)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : later ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) who physical)).support)
    (event : graph.EventId) (readyBefore : execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some who) (action : graph.Action event)
    (frontier sampled : graph.Config)
    (pending : graph.ForeignCompletionSequence who
      (runtime.originalConfig leaks execution memories) frontier)
    (frontierReady : frontier.cut.Ready event)
    (sampledStep : sampled ∈ (frontier.step event frontierReady action).support)
    (settled : graph.Config) (readyLater : later.application.config.cut.Ready event)
    (settledStep : settled ∈ (later.application.config.step event readyLater action).support) :
    sampled.outputs event = settled.outputs event := by
  have originalReady : (runtime.originalConfig leaks execution memories).cut.Ready event :=
    readyBefore
  have frontierEval := (pending.eval_eq event originalReady actor action).2
  have laterEval := runtime.reactive_ready_evaluation_continuation leaks execution later who
    physical scheduler players rounds reached event readyBefore action
  have same : (graph.nodes event).eval? action later.application.config.store =
      (graph.nodes event).eval? action frontier.store := laterEval.trans frontierEval.symm
  exact Config.owned_step_output_eq_of_eval_eq frontier later.application.config sampled settled
    event frontierReady readyLater who actor action same sampledStep settledStep

end Vegas.EventGraphRuntime

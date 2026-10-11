/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOriginalConfig
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveReceipts
import Vegas.EventGraph.ConfigRestriction
import Vegas.Pending.ReactiveSampledFrontierOwnership

/-! # Original-action configurations across raw unilateral callbacks -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A focal player with no prescribed intention memory retains its actual
physical completions across every raw response. Foreign memories remain fixed;
no prescribed-response support is required from the focal player. -/
theorem originalConfig_respond_of_empty_memory (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (who : Player)
    (empty : memories who = []) (action : (runtime.reactiveApplication leaks).Action) :
    runtime.originalConfig leaks
      (execution.respond (runtime.reactiveApplication leaks) who action) memories =
        runtime.originalConfig leaks execution memories := by
  have configEq := (runtime.reactive_respond_application leaks execution who action).1
  apply Config.eq_of_fields
  · change (execution.respond
      (runtime.reactiveApplication leaks) who action).application.config.inputs =
      execution.application.config.inputs
    exact congrArg Config.inputs configEq
  · change (execution.respond
      (runtime.reactiveApplication leaks) who action).application.config.cut =
      execution.application.config.cut
    exact congrArg Config.cut configEq
  · change (execution.respond
      (runtime.reactiveApplication leaks) who action).application.config.outputs =
      execution.application.config.outputs
    exact congrArg Config.outputs configEq
  · change ((execution.respond
      (runtime.reactiveApplication leaks) who action).application.config.history.map
        (runtime.originalCompletion leaks _ memories)) = _
    rw [configEq]
    apply List.map_congr_left
    intro completion _
    unfold originalCompletion
    cases actor : graph.actor? completion.event with
    | none => rfl
    | some owner =>
        dsimp only
        by_cases same : owner = who
        · subst owner
          rw [empty]
          cases node : nodeView graph completion.event <;> simp [reactiveOriginal, node]
        · rw [(runtime.reactiveApplication leaks).respond_recall_other
            execution who owner same action,
            (runtime.reactiveApplication leaks).respond_receipts]

/-- A physically ready focal event is absent from every foreign player's
supported intention memory, hence remains ready in the retained frontier. -/
theorem unilateralFrontier_ready (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (frontier : graph.Config)
    (domain : ∀ event, event ∈ frontier.cut.completed ↔
      event ∈ execution.application.config.cut.completed ∨
        ∃ owner, owner ≠ focal ∧ ∃ remembered,
          some remembered ∈ memories owner ∧ remembered.event = event)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (ready : execution.application.config.cut.Ready event) :
    frontier.cut.Ready event := by
  constructor
  · intro completed
    rcases (domain event).mp completed with physically | ⟨owner, foreign, remembered, member, named⟩
    · exact ready.1 physically
    · have owns := runtime.prescribedReactivePosterior_owned leaks owner (profile owner)
        (consistent owner foreign) (memories owner) (supported owner foreign) remembered member
      rw [named, actor, Option.some.injEq] at owns
      exact foreign owns.symm
  · intro predecessor dependency
    exact (domain predecessor).mpr (Or.inl (ready.2 dependency))

/-- A ready focal graph step, including an expiry failure action, couples with
the same graph evaluator in a frontier containing only foreign sampled intentions.
Native handler identification is separate. The focal policy is arbitrary. -/
theorem unilateralFrontier_coupled_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (frontier : graph.Config)
    (domain : ∀ event, event ∈ frontier.cut.completed ↔
      event ∈ execution.application.config.cut.completed ∨
        ∃ owner, owner ≠ focal ∧ ∃ remembered,
          some remembered ∈ memories owner ∧ remembered.event = event)
    (agreement : execution.application.config.CompletedOutputAgreement frontier)
    (inputs : execution.application.config.inputs = frontier.inputs)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (ready : execution.application.config.cut.Ready event) (action : graph.Action event) :
    ∃ frontierReady : frontier.cut.Ready event, ∃ joint : PMF (graph.Config × graph.Config),
      joint.map Prod.fst = execution.application.config.step event ready action ∧
      joint.map Prod.snd = frontier.step event frontierReady action ∧
      ∀ pair ∈ joint.support, pair.1.CompletedOutputAgreement pair.2 ∧
        pair.1.inputs = pair.2.inputs := by
  have frontierReady := runtime.unilateralFrontier_ready leaks profile execution focal memories
    consistent supported frontier domain event actor ready
  exact ⟨frontierReady, Config.CompletedOutputAgreement.coupled_step execution.application.config
    frontier agreement inputs event ready frontierReady action⟩

/-- A mixed frontier differs from the reconstructed actual configuration only
by foreign completions. The replay is derived from its reachable graph cut and
genuine foreign memory ownership, rather than assuming a source/noise law. -/
theorem unilateralFrontier_foreign_sequence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (frontier : graph.Config)
    (reachable : frontier.Reachable execution.application.config.inputs)
    (domain : ∀ event, event ∈ frontier.cut.completed ↔
      event ∈ execution.application.config.cut.completed ∨
        ∃ owner, owner ≠ focal ∧ ∃ remembered,
          some remembered ∈ memories owner ∧ remembered.event = event)
    (agreement : execution.application.config.CompletedOutputAgreement frontier)
    (inputs : execution.application.config.inputs = frontier.inputs)
    (recalls : ∀ owner, graph.ownCompletions owner
      (runtime.originalConfig leaks execution memories).history <+:
        graph.ownCompletions owner frontier.history) :
    ∃ final, graph.ForeignCompletionSequence focal
      (runtime.originalConfig leaks execution memories) final ∧
        graph.semanticKey frontier = graph.semanticKey final := by
  have foreignOwners : ∀ event ∈ frontier.cut.completed,
      event ∉ execution.application.config.cut.completed →
        ∃ owner, graph.actor? event = some owner ∧ owner ≠ focal := by
    intro event completed unfinished
    rcases (domain event).mp completed with physically | ⟨owner, foreign, remembered, member, named⟩
    · exact (unfinished physically).elim
    · exact ⟨owner, named ▸ runtime.prescribedReactivePosterior_owned leaks owner (profile owner)
        (consistent owner foreign) (memories owner) (supported owner foreign) remembered member,
          foreign⟩
  obtain ⟨last, sequence, same⟩ := reachable.foreign_factor execution.application.config.cut
    ordered focal foreignOwners
  let original := runtime.originalConfig leaks execution memories
  have originalAgreement : original.CompletedOutputAgreement frontier := agreement
  have originalInputs : original.inputs = frontier.inputs := inputs
  have restricted : graph.semanticKey (frontier.restrict execution.application.config.cut) =
      graph.semanticKey original :=
    originalAgreement.restrict_semanticKey_of_prefix original frontier originalInputs recalls
  obtain ⟨final, replayed, resultSame⟩ := sequence.congr_start original restricted
  exact ⟨final, replayed, same.trans resultSame⟩

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperUsablePreparation
import Vegas.Examples.CommitSeedSignallingSubmissionShape
import Interaction.ReactiveRoundTrace

/-! # Actual usable declarations through the short helper inclusion window -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- An arbitrary usable counted declaration at the first eligible slot
installs its actual Bool value in a genuine clear publication-only entry.
The three original commands and the private preparation are retained literally. -/
theorem helper_clock_two_usable_publication (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = false)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (identified : marker.id = (bob, 0)) (permitted : PhaseCount.permits [] marker = true)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (value : Bool) (usable : (material.call.opening.bind fun raw => raw.as? .bool) = some value)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players 3
      (execution.respond app alice ⟨some material⟩)).support) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining - 3, none, next⟩)) ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.native.config.store (.inr (bindingEvent alice)) =
        some (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
          (PublicationResult.success value : PublicationResult (simpleExpr.Val .bool))) ∧
      next.application.current.excluded = ∅ ∧
      ∀ entry ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests entry.beforeView.application.2 alice coordinate := by
  have currentRequest : execution.application.SeedRequest alice
      ⟨execution.application.attempt, bindingEvent alice⟩ := by
    simpa only [request.1.symm, originalCoordinate] using request
  obtain ⟨serial, opening, evidence, shape, _bounded, fresh⟩ :=
    counted_submission_binding_shape (family seed) remaining execution alice fixed
      (bindingEvent alice) .bool (bindingEvent_layout alice) currentRequest material offered
  have call : material.call.packet =
      .commitment (bindingEvent alice) (alice, .prepared serial) := by rw [shape]
  have interpreted : (opening.bind fun raw => raw.as? .bool) = some value := by
    simpa only [shape] using usable
  obtain ⟨before, native, message, _prior, ⟨beforeTrace⟩, _ready, _bobAccepted, _position,
      recorded, emitted, _timed, _included, handled, _accepted, nativeEq, suffix, clear,
      unserved⟩ :=
    helper_clock_two_submitted_publication seed remaining execution mixed fixed bit request
      clock quiet marker input sender identified permitted material offered
        (alice, .prepared serial) call players covered next reached
  let entry := originalResponseEntry execution alice (⟨some material⟩ : app.Action)
  have declared : entry.action =
      ⟨some ⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), opening⟩, evidence⟩⟩ :=
    congrArg (fun submission => (⟨some submission⟩ : app.Action)) shape
  obtain ⟨actual, actualEmitted, _sender, packetCall⟩ := PhaseCount.recalled_submission_emitted
    runtime leaks initial horizon (family seed)
      (countedMenu.toRawTrace initial horizon (family seed) beforeTrace) alice entry recorded
        material rfl
  have same : actual = message := Option.some.inj (actualEmitted.symm.trans emitted)
  subst actual
  have actualCall : message.payload.packet.call =
      .commitment (bindingEvent alice) (alice, .prepared serial) := packetCall.trans call
  have output := helper_usable_packet_native_output (family seed)
    ⟨remaining - 2, none, before⟩ beforeTrace entry recorded serial opening evidence declared fresh
      value interpreted message actualCall native handled
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining execution
    alice ⟨some material⟩ fixed offered
  have enough := family_requested_remaining seed ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) fixed) (originalCoordinate alice) alice
      request
  change 9 < remaining at enough
  have budget : remaining = (remaining - 3) + 3 := by omega
  have beforeWindow : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 3) + 3, none, execution.respond app alice ⟨some material⟩⟩) := by
    rw [← budget]
    exact responded
  obtain ⟨nextTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (remaining - 3) 3 (execution.respond app alice ⟨some material⟩) next beforeWindow reached
  refine ⟨⟨nextTrace⟩, suffix, ?_, clear, unserved⟩
  change next.application.current.native.config.outputs (bindingEvent alice) = _
  rw [nativeEq]
  exact output

/-- At the other eligible slot the arbitrary usable current declaration is
admitted in the next actual round. Its native value and fresh slot survive
normalization into the genuine publication-only entry. -/
theorem helper_clock_three_usable_publication (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (position : execution.environmentRecall.length = 10)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (value : Bool) (usable : (material.call.opening.bind fun raw => raw.as? .bool) = some value)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (next : app.Execution)
    (reached : next ∈ (app.round (family seed) players
      (execution.respond app alice ⟨some material⟩)).support) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining - 1, none, next⟩)) ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.native.config.store (.inr (bindingEvent alice)) =
        some (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
          (PublicationResult.success value : PublicationResult (simpleExpr.Val .bool))) ∧
      next.application.current.excluded = ∅ ∧
      ∀ entry ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests entry.beforeView.application.2 alice coordinate := by
  have currentRequest : execution.application.SeedRequest alice
      ⟨execution.application.attempt, bindingEvent alice⟩ := by
    simpa only [request.1.symm, originalCoordinate] using request
  obtain ⟨serial, opening, evidence, shape, _bounded, fresh⟩ :=
    counted_submission_binding_shape (family seed) remaining execution alice fixed
      (bindingEvent alice) .bool (bindingEvent_layout alice) currentRequest material offered
  have call : material.call.packet =
      .commitment (bindingEvent alice) (alice, .prepared serial) := by rw [shape]
  have interpreted : (opening.bind fun raw => raw.as? .bool) = some value := by
    simpa only [shape] using usable
  obtain ⟨native, message, emitted, handled, _accepted, nativeEq, suffix, clear, unserved⟩ :=
    helper_clock_three_submitted_publication seed remaining execution fixed bit request clock
      position bobAccepted material offered (alice, .prepared serial) call players next reached
  let after := execution.respond app alice (⟨some material⟩ : app.Action)
  let entry := originalResponseEntry execution alice (⟨some material⟩ : app.Action)
  have recorded : entry ∈ after.recall alice := by
    rw [respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining execution
    alice ⟨some material⟩ fixed offered
  obtain ⟨actual, actualEmitted, _sender, packetCall⟩ := PhaseCount.recalled_submission_emitted
    runtime leaks initial horizon (family seed)
      (countedMenu.toRawTrace initial horizon (family seed) responded) alice entry recorded
        material rfl
  have same : actual = message := Option.some.inj (actualEmitted.symm.trans emitted)
  subst actual
  have actualCall : message.payload.packet.call =
      .commitment (bindingEvent alice) (alice, .prepared serial) := packetCall.trans call
  have declared : entry.action =
      ⟨some ⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), opening⟩, evidence⟩⟩ :=
    congrArg (fun submission => (⟨some submission⟩ : app.Action)) shape
  have output := helper_usable_packet_native_output (family seed) ⟨remaining, none, after⟩
    responded entry recorded serial opening evidence declared fresh value interpreted message
      actualCall native handled
  have enough := family_requested_remaining seed ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) fixed) (originalCoordinate alice) alice
      request
  change 9 < remaining at enough
  have beforeRound : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 1) + 1, none, after⟩) := by
    rw [show remaining - 1 + 1 = remaining by omega]
    exact responded
  obtain ⟨nextTrace⟩ := countedMenu.trace_round initial horizon (family seed) players covered
    (remaining - 1) after next beforeRound reached
  refine ⟨⟨nextTrace⟩, suffix, ?_, clear, unserved⟩
  change next.application.current.native.config.outputs (bindingEvent alice) = _
  rw [nativeEq]
  exact output

end Vegas.Examples.CommitSeedSignalling

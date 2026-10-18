/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperSubmittedPublication
import Vegas.Examples.CommitSeedSignallingPublicationPayoff

/-! # Entire safe futures after the actual eligible helper declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- A proper current response at the useful clock-two slot protects Alice and
has nonnegative actual net payoff through the entire remaining native run.
The passive prefix and later publication share exactly the same player kernels. -/
theorem helper_clock_two_proper_future_outcome (seed : Seeds) (remaining : Nat)
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
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (serial : Nat)
    (declared : (⟨some material⟩ : app.Action) =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial)
    (fresh : (execution.observe app alice).application.1.candidates (.prepared serial) = .fresh)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (proper : players alice = properPolicy rule alice)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining
      (execution.respond app alice ⟨some material⟩)).support) :
    alice ∉ final.application.current.excluded ∧ 0 ≤ netPayoff (app.finished final) alice := by
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have indexed := original_first_late_input_index seed ⟨remaining, some alice, execution⟩ rawFixed
    alice rfl request.1.symm clock
  change execution.environmentRecall.length = 4 + if seedBits seed alice then 3 else 1 at indexed
  rw [bit] at indexed
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed) fixed).1
  have enough : 3 ≤ remaining := by
    change execution.environmentRecall.length + remaining = 64 at accounted
    simp only [Bool.false_eq_true, ite_false] at indexed
    omega
  have splitRun : remaining = 3 + (remaining - 3) := by omega
  rw [splitRun, app.runRounds_add, PMF.support_bind] at reached
  obtain ⟨next, prefixReached, tailReached⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨⟨nextTrace⟩, suffix, stored, clear, unserved⟩ := helper_clock_two_proper_publication seed
    remaining execution mixed fixed bit request clock quiet marker input sender identified permitted
      material offered serial declared fresh players covered next prefixReached
  have successful : next.application.current.native.config.store (.inr (bindingEvent alice)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
        (PublicationResult.success true)) := stored
  have active : alice ∉ next.application.current.excluded := by
    rw [clear]
    exact Finset.notMem_empty alice
  refine ⟨?_, ?_⟩
  · exact proper_publication_run_survives seed (remaining - 3) next nextTrace suffix alice true
      successful unserved active rule players covered proper final tailReached
  · exact proper_publication_run_netPayoff_nonnegative seed (remaining - 3) next nextTrace suffix
      alice true successful unserved active rule players covered proper final tailReached

/-- At clock three the literal earlier WAIT remains in the source execution.
A proper current response and proper publication future preserve Alice through
the same complete remaining run; no old-word consistency is required. -/
theorem helper_clock_three_proper_future_outcome (seed : Seeds) (remaining : Nat)
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
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (serial : Nat)
    (declared : (⟨some material⟩ : app.Action) =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial)
    (fresh : (execution.observe app alice).application.1.candidates (.prepared serial) = .fresh)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (proper : players alice = properPolicy rule alice)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining
      (execution.respond app alice ⟨some material⟩)).support) :
    alice ∉ final.application.current.excluded ∧ 0 ≤ netPayoff (app.finished final) alice := by
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed) fixed).1
  have enough : 1 ≤ remaining := by
    change execution.environmentRecall.length + remaining = 64 at accounted
    rw [position] at accounted
    omega
  have splitRun : remaining = 1 + (remaining - 1) := by omega
  rw [splitRun, app.runRounds_add, PMF.support_bind] at reached
  obtain ⟨next, firstReached, tailReached⟩ := Set.mem_iUnion₂.mp reached
  have moved : next ∈ (app.round (family seed) players
      (execution.respond app alice ⟨some material⟩)).support := by
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using firstReached
  obtain ⟨⟨nextTrace⟩, suffix, stored, clear, unserved⟩ :=
    helper_clock_three_proper_publication seed
      remaining execution fixed bit request clock position bobAccepted material offered serial
        declared
          fresh players covered next moved
  have successful : next.application.current.native.config.store (.inr (bindingEvent alice)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
        (PublicationResult.success true)) := stored
  have active : alice ∉ next.application.current.excluded := by
    rw [clear]
    exact Finset.notMem_empty alice
  refine ⟨?_, ?_⟩
  · exact proper_publication_run_survives seed (remaining - 1) next nextTrace suffix alice true
      successful unserved active rule players covered proper final tailReached
  · exact proper_publication_run_netPayoff_nonnegative seed (remaining - 1) next nextTrace suffix
      alice true successful unserved active rule players covered proper final tailReached
end Vegas.Examples.CommitSeedSignalling

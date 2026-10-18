/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperLatePublication
import Vegas.Examples.CommitSeedSignallingPublicationPayoff
import Interaction.ReactiveRoundTrace

/-! # Actual safe helper continuations through their original late inclusion -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- The original binding is sent at the useful slot identified by the helper
observation. Later namespaces retain the existing immediate proper service. -/
def helperTimingRule (bit : Bool) (_owner : Player) (coordinate : CommitAttemptEvent graph)
    (clocks : List Nat) : Bool :=
  if coordinate.attempt = originalAttempt then
    decide (clocks.getLastD 0 = if bit then 3 else 2)
  else true

/-- Choosing the rule uses only a seed bit already identified by the current
full information set; the future policy still reads the ordinary clock word. -/
theorem helperTimingRule_at_eligible (bit : Bool) (clocks : List Nat)
    (last : clocks.getLastD 0 = if bit then 3 else 2) :
    helperTimingRule bit alice (originalCoordinate alice) clocks = true := by
  simp only [helperTimingRule, originalCoordinate, ite_true, last, decide_true]

/-- A proper declaration at the seed-eligible original helper slot protects
Alice through the entire actual publication continuation. Both receipt and
successful value at the new suffix are derived from the real late inclusion. -/
theorem helper_eligible_round_proper_outcome
    (seed : Seeds) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - lateIncludePosition alice (seedBits seed alice), none, execution⟩))
    (position : execution.environmentRecall.length =
      lateIncludePosition alice (seedBits seed alice))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (serial : Nat) (entry : app.PlayerEntry) (retained : entry ∈ execution.recall alice)
    (declared : entry.action =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message)
    (timed : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        execution.environmentRecall (execution.observeEnvironment app)).emissions)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (next : app.Execution)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (proper : players alice = properPolicy rule alice)
    (last : next ∈ (app.round (family seed) players execution).support)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players
      (horizon - lateIncludePosition alice (seedBits seed alice) - 1) next).support) :
    alice ∉ final.application.current.excluded ∧ 0 ≤ netPayoff (app.finished final) alice := by
  obtain ⟨_native, _normalized, command, _call, _found, _handled, _accepted,
      _stored, _normalizes, _phaseHandled, _receipt⟩ :=
    proper_late_inclusion seed alice
      (horizon - lateIncludePosition alice (seedBits seed alice)) execution trace position request
        serial entry retained declared
          fresh message emitted timed
  obtain ⟨selected, selectedSupport, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ last)
  have selectedEq : selected = (.include message.id : app.Command) := by
    rw [command] at selectedSupport
    exact (PMF.mem_support_pure_iff _ _).mp selectedSupport
  subst selected
  obtain ⟨observed, included, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  simp only [ReactiveApplication.resume, ReactiveApplication.Command.actor?,
    PMF.mem_support_pure_iff] at resumed
  subst next
  obtain ⟨scheduled, tail, _accepted, stored, clear, unserved⟩ :=
    helper_proper_late_publication_entry seed execution trace position request serial entry retained
      declared fresh message emitted timed bobAccepted observed included
  have budget : horizon - lateIncludePosition alice (seedBits seed alice) =
      (horizon - lateIncludePosition alice (seedBits seed alice) - 1) + 1 := by
    cases seedBits seed alice <;> decide
  have before : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(horizon - lateIncludePosition alice (seedBits seed alice) - 1) + 1,
        none, execution⟩) := by
    rwa [← budget]
  have chosen : (.include message.id : app.Command) ∈
      (family seed execution.environmentRecall (execution.observeEnvironment app)).support := by
    rw [scheduled]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨postTrace⟩ := countedMenu.trace_environment initial horizon (family seed)
    (horizon - lateIncludePosition alice (seedBits seed alice) - 1) execution observed
      (.include message.id) before chosen included
  have physical : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - lateIncludePosition alice (seedBits seed alice) - 1, none, observed⟩) :=
    postTrace
  have ownStored : observed.application.current.native.config.store (.inr (bindingEvent alice)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
        (PublicationResult.success true)) := stored
  have active : alice ∉ observed.application.current.excluded := by
    rw [clear]
    exact Finset.notMem_empty alice
  refine ⟨?_, ?_⟩
  · exact proper_publication_run_survives seed
      (horizon - lateIncludePosition alice (seedBits seed alice) - 1) observed physical tail alice
        true ownStored unserved active rule players covered proper final reached
  · exact proper_publication_run_netPayoff_nonnegative seed
      (horizon - lateIncludePosition alice (seedBits seed alice) - 1) observed physical tail alice
        true ownStored unserved active rule players covered proper final reached

end Vegas.Examples.CommitSeedSignalling

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPublicationProper
import Vegas.Examples.CommitSeedSignallingFinishedPayoff

/-! # Actual net payoff of proper publication continuations -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- From a fresh publication suffix, proper future responses preserve the
successful owner and incur zero actual count-audit charge on every supported
outcome. Earlier own responses remain literal, including silent commitments. -/
theorem proper_publication_run_netPayoff_nonnegative
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (tail : execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (active : owner ∉ execution.application.current.excluded)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (proper : players owner = properPolicy rule owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining execution).support) :
    0 ≤ netPayoff (app.finished final) owner := by
  have survives := proper_publication_run_survives seed remaining execution sourceTrace tail
    owner value stored unserved active rule players covered proper final reached
  have source : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0 + remaining, none, execution⟩) := by
    simpa only [Nat.zero_add] using sourceTrace
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining execution final source reached
  let history : (countedMenu.protocol initial horizon (family seed)).History :=
    ⟨some ⟨0, none, final⟩, finalTrace⟩
  have zero := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    (family seed) evidenceService history owner
  change TerminalAudit.charge app.stateTraffic audit (app.finished final) owner = 0 at zero
  change 0 ≤ basePayoff (app.finished final) owner -
    TerminalAudit.charge app.stateTraffic audit (app.finished final) owner * deposit owner
  rw [zero, zero_mul, sub_zero]
  change 0 ≤ phaseExclusionBase setup .concurrentReveals runtime leaks utility excludedPayoff
    (some (⟨0, none, final⟩ : app.Control)) owner
  rw [phaseExclusionBase_eq_readout setup .concurrentReveals runtime leaks utility excludedPayoff
    ⟨0, none, final⟩ owner survives]
  cases read : phaseSourceReadout setup .concurrentReveals runtime leaks
      (some (⟨0, none, final⟩ : app.Control)) with
  | none => exact le_refl _
  | some terminal => exact (utility_mem_Icc terminal owner).1

/-- The bound concerns the actual original future law, before averaging away
any seed or foreign-policy correlation. -/
theorem proper_publication_expected_netPayoff_nonnegative
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (tail : execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (active : owner ∉ execution.application.current.excluded)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (proper : players owner = properPolicy rule owner) :
    0 ≤ expect (app.runRounds (family seed) players remaining execution)
      (fun final => netPayoff (app.finished final) owner) := by
  apply expect_nonneg
  intro final reached
  exact proper_publication_run_netPayoff_nonnegative seed remaining execution sourceTrace tail
    owner value stored unserved active rule players covered proper final reached

end Vegas.Examples.CommitSeedSignalling

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingRememberedRequest
import Vegas.Examples.CommitSeedSignallingProperPublicationRecords

/-! # Positive-age proper publications cannot end in exclusion -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- A positive-age original publication request has already had its proper
callback. The original retained own record therefore protects every measured
later endpoint, without assuming a receipt or a prescribed future opening. -/
theorem fixed_late_positive_publication_survives
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (prior : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (kept : TracePrefix prior trace)
    (owner : Player)
    (ownConsistent : (fixedLatePolicy owner).Consistent (final.execution.recall owner))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (publication : coordinate.event = revealEvent owner)
    (request : execution.application.SeedRequest owner coordinate)
    (positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (execution.observeEnvironment app)) :
    owner ∉ final.execution.application.current.excluded := by
  obtain ⟨entry, recorded, requested⟩ := positive_age_own_request seed remaining execution prior
    coordinate owner request positive
  have retained := app.reaches_recall_prefix initial horizon (family seed)
    (countedMenu.reaches_raw initial horizon (family seed) kept.reachesWithin)
      ⟨remaining, none, execution⟩ final rfl rfl owner
  exact fixed_late_recorded_publication_survives seed final trace owner ownConsistent coordinate
    retired publication entry (retained.subset recorded) requested

/-- In a literal initialized proper-policy experiment, publication age alone
derives the retained-record consistency used by the actual survival theorem. -/
theorem initialized_fixed_late_positive_publication_survives
    (players : Player → app.Policy) (seed : Seeds) (count : Nat) (final : app.Control)
    (reached : final.execution ∈
      (app.runRounds (family seed) players count initialExecution).support)
    (remaining : Nat) (execution : app.Execution)
    (prior : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (kept : TracePrefix prior trace)
    (owner : Player) (policy : players owner = fixedLatePolicy owner)
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (publication : coordinate.event = revealEvent owner)
    (request : execution.application.SeedRequest owner coordinate)
    (positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (execution.observeEnvironment app)) :
    owner ∉ final.execution.application.current.excluded := by
  have consistent := (app.consistentRecall_policyInvariant players).runRounds (family seed) count
    initialExecution final.execution (fun _ => .nil) reached
  have focal := consistent owner
  rw [policy] at focal
  exact fixed_late_positive_publication_survives seed remaining execution prior final trace kept
    owner focal coordinate retired publication request positive

end Vegas.Examples.CommitSeedSignalling

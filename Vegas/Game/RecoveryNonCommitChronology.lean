/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedSourceOrigin
import Vegas.Game.RecoveryNonCommitWindow
import Vegas.Game.CompiledRevealLayout
import Vegas.Source.CommitRecoveryNonCommitRecall
import Vegas.Source.CommitRecoverySurvivingInformation

/-! # Complete chosen source signals through actual disclosure phase advances -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem reveal_advance_window
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode nextState)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .reveal)
    (boundary : phase.high = nextState.attempt.phase)
    (point : ProtocolState setup.program)
    (lower : ProtocolState.remaining setup.program (next.residual.lift
        (ProtocolState.entry next.residual.tail next.source)) <
      ProtocolState.remaining setup.program point)
    (upper : ProtocolState.remaining setup.program point ≤
      ProtocolState.remaining setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) :
    ProtocolState.atCommit setup.program point = false := by
  let count := phase.high - phase.low
  have low : phase.low = state.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have high : phase.high = state.attempt.phase + count := by
    have nonempty := phase.nonempty
    dsimp only [count]
    omega
  have prefixed := checkpoint.compiled.revealPrefix_of_phase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations checkpoint.registry
    checkpoint.embedding checkpoint.before state.attempt.phase phase kind low count high
  have firstRank := checkpoint.remaining
    (ProtocolState.entry checkpoint.residual.tail checkpoint.source)
  have lastRank := next.remaining (ProtocolState.entry next.residual.tail next.source)
  simp only [ProtocolState.remaining_entry] at firstRank lastRank
  have firstCount := checkpoint.compiled.countEq
  have lastCount := next.compiled.countEq
  simp only [eventCount_eq_instructionCount] at firstCount lastCount
  apply checkpoint.origin.noncommit_of_reveal_window count prefixed point
  · omega
  · omega

/-- The same genuine chosen disclosure successors have equal complete source
information whenever the earlier full recalls and actual endpoint private views agree.
No intermediate public signal, path length or source counterpart is supplied. -/
theorem RecoverySourceCheckpoint.reveal_information_eq
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second firstNext secondNext :
      PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (left : RecoverySourceCheckpoint setup mode first)
    (right : RecoverySourceCheckpoint setup mode second)
    (leftNext : RecoverySourceCheckpoint setup mode firstNext)
    (rightNext : RecoverySourceCheckpoint setup mode secondNext)
    (firstPhase secondPhase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (firstRemaining secondRemaining :
      List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (firstInstalled : first.phases = firstPhase :: firstRemaining)
    (secondInstalled : second.phases = secondPhase :: secondRemaining)
    (firstKind : firstPhase.kind = .reveal) (secondKind : secondPhase.kind = .reveal)
    (firstBoundary : firstPhase.high = firstNext.attempt.phase)
    (secondBoundary : secondPhase.high = secondNext.attempt.phase)
    (firstGeneration : firstNext.generation = first.generation)
    (secondGeneration : secondNext.generation = second.generation)
    {firstFuel secondFuel : Nat}
    (firstPath : setup.commitRecoveryProtocol.ReachesWithin firstFuel
      ⟨_, left.trace⟩ ⟨_, leftNext.trace⟩)
    (secondPath : setup.commitRecoveryProtocol.ReachesWithin secondFuel
      ⟨_, right.trace⟩ ⟨_, rightNext.trace⟩)
    (who : Player) (projection : SourceViewProjection) {Observation : Type*}
    (observe : setup.ProtocolView who × (Finset Player × Nat × Nat) → Observation)
    (firstSurvives : who ∉ firstNext.entry.excluded)
    (secondSurvives : who ∉ secondNext.entry.excluded)
    (prior : setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who left.trace).1 =
        setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who right.trace).1 ∧
      setup.commitRecoveryObservedRecall who projection observe
        (setup.commitRecoverySignals.infoOf who left.trace) =
        setup.commitRecoveryObservedRecall who projection observe
          (setup.commitRecoverySignals.infoOf who right.trace))
    (observed : projection.apply who setup.program
        (ProtocolState.observe who setup.program (leftNext.residual.lift
          (ProtocolState.entry leftNext.residual.tail leftNext.source))) =
      projection.apply who setup.program
        (ProtocolState.observe who setup.program (rightNext.residual.lift
          (ProtocolState.entry rightNext.residual.tail rightNext.source)))) :
    setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who leftNext.trace).1 =
        setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who rightNext.trace).1 ∧
      setup.commitRecoveryObservedRecall who projection observe
          (setup.commitRecoverySignals.infoOf who leftNext.trace) =
        setup.commitRecoveryObservedRecall who projection observe
          (setup.commitRecoverySignals.infoOf who rightNext.trace) := by
  apply setup.commitRecovery_noncommit_signals_eq_of_rank_windows who projection observe
    _ _ _ _ left.trace right.trace leftNext.trace rightNext.trace
    firstPath.tracePrefix secondPath.tracePrefix
  · exact firstGeneration.symm
  · exact secondGeneration.symm
  · exact reveal_advance_window left leftNext firstPhase firstRemaining firstInstalled
      firstKind firstBoundary
  · exact reveal_advance_window right rightNext secondPhase secondRemaining secondInstalled
      secondKind secondBoundary
  · exact prior.1
  · exact prior.2
  · exact firstSurvives
  · exact secondSurvives
  · exact congrArg some observed

private theorem sample_advance_window
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode nextState)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .sample)
    (boundary : phase.high = nextState.attempt.phase)
    (point : ProtocolState setup.program)
    (lower : ProtocolState.remaining setup.program (next.residual.lift
        (ProtocolState.entry next.residual.tail next.source)) <
      ProtocolState.remaining setup.program point)
    (upper : ProtocolState.remaining setup.program point ≤
      ProtocolState.remaining setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) :
    ProtocolState.atCommit setup.program point = false := by
  have low : phase.low = state.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have singleton := phase.sample_singleton kind
  have firstRank := checkpoint.remaining
    (ProtocolState.entry checkpoint.residual.tail checkpoint.source)
  have lastRank := next.remaining (ProtocolState.entry next.residual.tail next.source)
  simp only [ProtocolState.remaining_entry] at firstRank lastRank
  have firstCount := checkpoint.compiled.countEq
  have lastCount := next.compiled.countEq
  simp only [eventCount_eq_instructionCount] at firstCount lastCount
  apply checkpoint.compiled.noncommit_of_sample_phase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations checkpoint.registry
    checkpoint.embedding checkpoint.before state.attempt.phase phase kind low
    checkpoint.origin point
  omega

/-- The same genuine chosen sampling successors have equal complete source
information whenever the earlier full recalls and actual endpoint private views agree.
No intermediate public signal, path length or source counterpart is supplied. -/
theorem RecoverySourceCheckpoint.sample_information_eq
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second firstNext secondNext :
      PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (left : RecoverySourceCheckpoint setup mode first)
    (right : RecoverySourceCheckpoint setup mode second)
    (leftNext : RecoverySourceCheckpoint setup mode firstNext)
    (rightNext : RecoverySourceCheckpoint setup mode secondNext)
    (firstPhase secondPhase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (firstRemaining secondRemaining :
      List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (firstInstalled : first.phases = firstPhase :: firstRemaining)
    (secondInstalled : second.phases = secondPhase :: secondRemaining)
    (firstKind : firstPhase.kind = .sample) (secondKind : secondPhase.kind = .sample)
    (firstBoundary : firstPhase.high = firstNext.attempt.phase)
    (secondBoundary : secondPhase.high = secondNext.attempt.phase)
    (firstGeneration : firstNext.generation = first.generation)
    (secondGeneration : secondNext.generation = second.generation)
    {firstFuel secondFuel : Nat}
    (firstPath : setup.commitRecoveryProtocol.ReachesWithin firstFuel
      ⟨_, left.trace⟩ ⟨_, leftNext.trace⟩)
    (secondPath : setup.commitRecoveryProtocol.ReachesWithin secondFuel
      ⟨_, right.trace⟩ ⟨_, rightNext.trace⟩)
    (who : Player) (projection : SourceViewProjection) {Observation : Type*}
    (observe : setup.ProtocolView who × (Finset Player × Nat × Nat) → Observation)
    (firstSurvives : who ∉ firstNext.entry.excluded)
    (secondSurvives : who ∉ secondNext.entry.excluded)
    (prior : setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who left.trace).1 =
        setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who right.trace).1 ∧
      setup.commitRecoveryObservedRecall who projection observe
        (setup.commitRecoverySignals.infoOf who left.trace) =
        setup.commitRecoveryObservedRecall who projection observe
          (setup.commitRecoverySignals.infoOf who right.trace))
    (observed : projection.apply who setup.program
        (ProtocolState.observe who setup.program (leftNext.residual.lift
          (ProtocolState.entry leftNext.residual.tail leftNext.source))) =
      projection.apply who setup.program
        (ProtocolState.observe who setup.program (rightNext.residual.lift
          (ProtocolState.entry rightNext.residual.tail rightNext.source)))) :
    setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who leftNext.trace).1 =
        setup.commitRecoveryObservationSignal who projection
          (setup.commitRecoverySignals.infoOf who rightNext.trace).1 ∧
      setup.commitRecoveryObservedRecall who projection observe
          (setup.commitRecoverySignals.infoOf who leftNext.trace) =
        setup.commitRecoveryObservedRecall who projection observe
          (setup.commitRecoverySignals.infoOf who rightNext.trace) := by
  apply setup.commitRecovery_noncommit_signals_eq_of_rank_windows who projection observe
    _ _ _ _ left.trace right.trace leftNext.trace rightNext.trace
    firstPath.tracePrefix secondPath.tracePrefix
  · exact firstGeneration.symm
  · exact secondGeneration.symm
  · exact sample_advance_window left leftNext firstPhase firstRemaining firstInstalled
      firstKind firstBoundary
  · exact sample_advance_window right rightNext secondPhase secondRemaining secondInstalled
      secondKind secondBoundary
  · exact prior.1
  · exact prior.2
  · exact firstSurvives
  · exact secondSurvives
  · exact congrArg some observed

end Vegas

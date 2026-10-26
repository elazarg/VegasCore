/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseAutomatic
import Vegas.Game.PhaseProposalFreshTerminal

/-! # Actual fresh phase normalization has the original source law

Only inherited excluded owners can be completed by fresh normalization.
The actual native completion provenance therefore determines the entire
original source continuation under every behavioral profile.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [Fintype Player] in
private theorem completed_below_attempt {graph : Vegas.EventGraph Player L}
    (state : PhaseRuntimeState graph) (frontier : state.Frontier)
    (event : graph.EventId) (below : event.val < state.attempt.phase) :
    event ∈ state.current.native.config.cut.completed := by
  cases phases : state.phases with
  | nil =>
      have savedPrefix := frontier.positioned
      change PhaseRuntimeState.Positioned state.phases state.entry state.current at savedPrefix
      rw [phases] at savedPrefix
      exact (savedPrefix.2 event).mpr event.isLt
  | cons phase remaining =>
      have within := frontier.positioned
      change PhaseRuntimeState.Positioned state.phases state.entry state.current at within
      rw [phases] at within
      apply within.2.1 event
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some] using below

omit [DecidableEq Player] [Fintype Player] in
private theorem fresh_saved_prefix {graph : Vegas.EventGraph Player L}
    (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frontier : (⟨phases, generation, entry, entry, retired⟩ :
      PhaseRuntimeState graph).Frontier) :
    entry.native.config.cut.IsPrefix
      (⟨phases, generation, entry, entry, retired⟩ : PhaseRuntimeState graph).attempt.phase := by
  cases phases with
  | nil => exact frontier.positioned
  | cons phase remaining => exact frontier.positioned.1

/-- A factual source path selected by actual fresh normalization has its
exact original history law under every source profile. The automatic-step
condition is derived from native completion provenance, not assumed. -/
theorem RecoverySourceCheckpoint.fresh_normalization_kernel
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    (phases : List (RuntimePhase (serviceGraph setup mode))) (generation : Nat)
    (entry : RecoveryState (serviceGraph setup mode))
    (retired : List (RetiredCommitAttempt (serviceGraph setup mode)))
    (checkpoint : RecoverySourceCheckpoint setup mode
      (⟨phases, generation, entry, entry, retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    (frontier : (⟨phases, generation, entry, entry, retired⟩ :
      PhaseRuntimeState (serviceGraph setup mode)).Frontier)
    (next : RecoverySourceCheckpoint setup mode
      (PhaseRuntimeState.settle phases generation entry entry retired))
    {fuel : Nat} (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    setup.commitRecoveryModel.runBehavioralFrom profile
        (next.trace.length - checkpoint.trace.length) ⟨_, checkpoint.trace⟩ =
      PMF.pure ⟨_, next.trace⟩ := by
  let state : PhaseRuntimeState (serviceGraph setup mode) :=
    ⟨phases, generation, entry, entry, retired⟩
  let final := PhaseRuntimeState.settle phases generation entry entry retired
  obtain ⟨generationEq, _retiredEq, excludedEq, _stored, completedOrigin⟩ :=
    phaseProposal_fresh_settle_completion_origin phases generation entry retired
  have entryExcluded : final.entry.excluded = entry.excluded :=
    (PhaseRuntimeState.settle_entry_excluded_of_same phases generation entry entry retired
      rfl).trans excludedEq
  have automatic (point : ProtocolState setup.program)
      (low : instructionCount setup.program - ProtocolState.remaining setup.program
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) ≤
        instructionCount setup.program - ProtocolState.remaining setup.program point)
      (high : instructionCount setup.program - ProtocolState.remaining setup.program point <
        instructionCount setup.program - ProtocolState.remaining setup.program
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source))) :
      ∃ owner ∈ entry.excluded, ProtocolState.actor setup.program point = some owner := by
    let event : (serviceGraph setup mode).EventId :=
      ⟨instructionCount setup.program - ProtocolState.remaining setup.program point, by
        change _ < eventCount setup.program
        rw [eventCount_eq_instructionCount]
        omega⟩
    have oldRank := checkpoint.saved_position
    have nextRank := next.saved_position
    have lower : state.attempt.phase ≤ event.val := by
      simpa only [event, oldRank] using low
    have upper : event.val < final.attempt.phase := by
      simpa only [event, nextRank] using high
    have finalFrontier : final.Frontier :=
      PhaseRuntimeState.settle_frontier phases generation entry entry retired frontier
    have completed := completed_below_attempt final finalFrontier event upper
    have absent : event ∉ entry.native.config.cut.completed := by
      intro present
      have saved := fresh_saved_prefix phases generation entry retired frontier
      have below := (saved.2 event).mp present
      change event.val < state.attempt.phase at below
      omega
    obtain ⟨owner, excluded, actor⟩ := completedOrigin event completed absent
    exact ⟨owner, excluded,
      (source_actor_at_compiled_rank setup.program mode point event rfl).trans actor⟩
  exact (setup.commitRecovery_excluded_interval_law profile path _ _ rfl rfl generationEq.symm
    entryExcluded.symm automatic).1

/-- Fresh normalization preserves the complete original terminal history law
for every source profile, while allowing any number of inherited-owner skips. -/
theorem RecoverySourceCheckpoint.fresh_normalization_terminal_kernel
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    (phases : List (RuntimePhase (serviceGraph setup mode))) (generation : Nat)
    (entry : RecoveryState (serviceGraph setup mode))
    (retired : List (RetiredCommitAttempt (serviceGraph setup mode)))
    (checkpoint : RecoverySourceCheckpoint setup mode
      (⟨phases, generation, entry, entry, retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    (frontier : (⟨phases, generation, entry, entry, retired⟩ :
      PhaseRuntimeState (serviceGraph setup mode)).Frontier)
    (next : RecoverySourceCheckpoint setup mode
      (PhaseRuntimeState.settle phases generation entry entry retired))
    {fuel : Nat} (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile ⟨_, checkpoint.trace⟩ =
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile ⟨_, next.trace⟩ := by
  rw [setup.commitRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom
    certificate profile (next.trace.length - checkpoint.trace.length),
    checkpoint.fresh_normalization_kernel mode phases generation entry retired frontier next
      path profile, PMF.pure_bind]

end Vegas

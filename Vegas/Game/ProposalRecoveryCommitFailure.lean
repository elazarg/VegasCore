/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPayoff
import Vegas.Source.ProposalRecoveryChronology
import Vegas.Game.CommitRecoveryCommitFailure
import Vegas.Game.CommitRecoveryReference
import GameTheory.Protocol.HistoryEvents
import GameTheory.Analysis.Protocol.InformationLocalization

/-! # Standing unusable declarations on actual enriched commitment prefixes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem erased_reference_window (finite : setup.program.FiniteBindingTypes)
    (first last : setup.proposalRecoveryProtocol.History)
    (kept : TracePrefix first.trace last.trace) (fuel : Nat)
    (clock : last.trace.length = first.trace.length + fuel) :
    (⟨last.state, setup.proposalRecoveryEraseTrace last.trace⟩ :
        setup.commitRecoveryProtocol.History) ∈
      (setup.commitRecoveryModel.runBehavioralFrom
        (setup.commitRecoveryReference finite).strategy fuel
        ⟨first.state, setup.proposalRecoveryEraseTrace first.trace⟩).support := by
  let before : setup.commitRecoveryProtocol.History :=
    ⟨first.state, setup.proposalRecoveryEraseTrace first.trace⟩
  let after : setup.commitRecoveryProtocol.History :=
    ⟨last.state, setup.proposalRecoveryEraseTrace last.trace⟩
  have path := (setup.proposalRecoveryEraseTrace_prefix kept).reachesWithin
  have distance : after.trace.length - before.trace.length = fuel := by
    simp only [before, after, setup.proposalRecoveryEraseTrace_length]
    omega
  change setup.commitRecoveryProtocol.ReachesWithin
    (after.trace.length - before.trace.length) before after at path
  rw [distance] at path
  obtain ⟨elapsed, bounded, supported⟩ :=
    setup.commitRecoveryModel.exists_mem_support_runBehavioralFrom_of_reachesWithin
      (setup.commitRecoveryReference finite).strategy
      (setup.commitRecoveryReference_fullSupport finite) path
  have length := (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin
    (setup.commitRecoveryReference finite).strategy elapsed before after
        supported).trace_length_le_add
  have same : elapsed = fuel := by
    dsimp only [before, after] at length
    simp only [setup.proposalRecoveryEraseTrace_length] at length
    omega
  subst elapsed
  exact supported

private theorem erased_reference_terminal (finite : setup.program.FiniteBindingTypes)
    (first last : setup.proposalRecoveryProtocol.History)
    (kept : TracePrefix first.trace last.trace)
    (terminal : setup.proposalRecoveryProtocol.terminal last.state) :
    (⟨last.state, setup.proposalRecoveryEraseTrace last.trace⟩ :
        setup.commitRecoveryProtocol.History) ∈
      (setup.commitRecoveryModel.runBehavioralTerminalFrom
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        (setup.commitRecoveryReference finite).strategy
        ⟨first.state, setup.proposalRecoveryEraseTrace first.trace⟩).support := by
  let fuel := last.trace.length - first.trace.length
  have clock : last.trace.length = first.trace.length + fuel := by
    have bound := kept.length_le
    omega
  have reached := setup.erased_reference_window finite first last kept fuel clock
  rw [InformationModel.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom
    setup.commitRecoveryModel _ _ fuel]
  refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨_, reached, ?_⟩
  change _ ∈ (setup.commitRecoveryProtocol.randomizedBackwardLaw _ _ _).support
  rw [setup.commitRecoveryProtocol.randomizedBackwardLaw_of_terminal
    (history := ⟨last.state, setup.proposalRecoveryEraseTrace last.trace⟩) terminal]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

omit [Fintype Player] in
/-- If the original commitment window closes without a new exclusion, its
actual failed declaration is checkpointed and pays the author's floor under
EVERY legal enriched terminal suffix. A reset branch is excluded explicitly;
accepted bad material is never declared an immediate permanent loss. -/
theorem proposalRecovery_failed_commit_prefix_payoff [Finite Player]
    (finite : setup.program.FiniteBindingTypes)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (fuel : Nat) (distance : fuel + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point)
    (who : Player) (stopped : setup.proposalRecoveryProtocol.History)
    (kept : TracePrefix prior stopped.trace)
    (clock : stopped.trace.length = prior.length + fuel)
    (clear : stopped.state.elim False (fun last => last.excluded = current.entryExcluded))
    (recorded : ∃ joint ∈
      (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace stopped.trace)).take fuel,
      ∃ move, joint who = some move ∧ move.action.IsFailure)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (final : setup.proposalRecoveryProtocol.History)
    (continued : TracePrefix stopped.trace final.trace)
    (terminal : setup.proposalRecoveryProtocol.terminal final.state) :
    setup.proposalRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
  classical
  let _ := Fintype.ofFinite Player
  let reference := (setup.commitRecoveryReference finite).strategy
  have atClose := setup.erased_reference_window finite ⟨some current, prior⟩ stopped kept fuel clock
  have atFinal := setup.erased_reference_terminal finite stopped final continued terminal
  exact setup.commitRecovery_failed_commit_window_payoff reference reference current
    (setup.proposalRecoveryEraseTrace prior) committing fuel distance who
    ⟨stopped.state, setup.proposalRecoveryEraseTrace stopped.trace⟩ atClose clear recorded
    utility excludedPayoff ⟨final.state, setup.proposalRecoveryEraseTrace final.trace⟩ atFinal

end Vegas.SourceProgram.Setup

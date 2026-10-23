/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalCanonicalSourceBlock
import Vegas.Source.ProposalRecoveryTraceReadback
import GameTheory.Protocol.HistoryEvents

/-! # Exact original enriched histories identified by their finite commitment word -/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- Erasing proposal labels retains the same genuine bounded source path,
including its original initial history and every recovery transition. -/
theorem proposalRecovery_reaches_semantic
    (setup : Setup (Player := Player) (L := L))
    {fuel : Nat} {first last : setup.proposalRecoveryProtocol.History}
    (reached : setup.proposalRecoveryProtocol.ReachesWithin fuel first last) :
    setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨first.state, setup.proposalRecoveryEraseTrace first.trace⟩
      ⟨last.state, setup.proposalRecoveryEraseTrace last.trace⟩ := by
  induction reached with
  | refl fuel history => exact .refl fuel _
  | step joint legal realized rest ih =>
      exact .step (proposalRecoveryJoint joint) (setup.proposalRecovery_erase_legal joint legal)
        realized ih

/-- A supported finite ordinary continuation is identified by its complete
current commitment word. Semantic determinacy is the existing commitment-window
theorem; the retained literal false proposal labels then identify the SAME
enriched History, including its original setup and all remembered old choices. -/
theorem proposalRecovery_ordinary_commit_history_injective
    (setup : Setup (Player := Player) (L := L))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift (ProtocolState.entry (block.prepend suffix) source))
    (ordinary : current.excluded = current.entryExcluded) (positive : 0 < block.length)
    (left right : setup.proposalRecoveryProtocol.History)
    (leftSupport : left ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
      block.length ⟨some current, trace⟩).support)
    (rightSupport : right ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
      block.length ⟨some current, trace⟩).support)
    (same : ((setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace left.trace)).take block.length).reverse =
        ((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace right.trace)).take block.length).reverse) :
    left = right := by
  let strategy := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  have leftReached := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin strategy
    block.length ⟨some current, trace⟩ left leftSupport
  have rightReached := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin strategy
    block.length ⟨some current, trace⟩ right rightSupport
  obtain ⟨leftSource, leftState, leftTrace, leftAttempt, leftExact, _leftPoint,
    _leftExcluded, _leftEntry, _leftGeneration, leftWord, leftLabels, _leftProper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values block suffix lift origin
      source current trace point ordinary left leftSupport
  obtain ⟨rightSource, rightState, rightTrace, rightAttempt, rightExact, _rightPoint,
    _rightExcluded, _rightEntry, _rightGeneration, rightWord, rightLabels, _rightProper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values block suffix lift origin
      source current trace point ordinary right rightSupport
  cases leftExact
  cases rightExact
  have takeLeft : ((setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace leftTrace)).take block.length).reverse =
        leftAttempt.joints := by
    rw [leftWord, ← leftAttempt.joints_length, ← List.length_reverse,
      List.take_left, List.reverse_reverse]
  have takeRight : ((setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace rightTrace)).take block.length).reverse =
        rightAttempt.joints := by
    rw [rightWord, ← rightAttempt.joints_length, ← List.length_reverse,
      List.take_left, List.reverse_reverse]
  have sameAttempt : leftAttempt.joints = rightAttempt.joints :=
    takeLeft.symm.trans (same.trans takeRight)
  have sameSemantic : setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace leftTrace) = setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace rightTrace) := by
    rw [leftWord, rightWord, sameAttempt]
  have sameLabels : setup.proposalRecoveryJointRecall leftTrace =
      setup.proposalRecoveryJointRecall rightTrace := by
    rw [leftLabels, rightLabels, sameAttempt]
  have committing : ProtocolState.atCommit setup.program current.point = true := by
    rw [point, origin.atCommit_lift]
    cases block with
    | nil => cases Nat.not_lt_zero _ positive
    | commit => rfl
  have window : block.length + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point := by
    rw [point, origin.commitEnd_lift, origin.remaining_lift]
    exact block.length_le_commit_window suffix source
  have length := leftReached.trace_length_le_add
  change leftTrace.length ≤ trace.length + block.length at length
  have within : (setup.proposalRecoveryEraseTrace leftTrace).length +
      ProtocolState.commitEnd setup.program current.point ≤
        (setup.proposalRecoveryEraseTrace trace).length +
          ProtocolState.remaining setup.program current.point := by
    simp only [setup.proposalRecoveryEraseTrace_length]
    omega
  have semantic := setup.commitRecovery_history_eq_of_commit_window current
    (setup.proposalRecoveryEraseTrace trace) committing
      (setup.proposalRecoveryEraseTrace leftTrace) (setup.proposalRecoveryEraseTrace rightTrace)
      (proposalRecovery_reaches_semantic setup leftReached)
      (proposalRecovery_reaches_semantic setup rightReached) sameSemantic within
  exact setup.proposalRecoveryHistory_eq_of_semantic_word _ _ semantic sameLabels

end Vegas

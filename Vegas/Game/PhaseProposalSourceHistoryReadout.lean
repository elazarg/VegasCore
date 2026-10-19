/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceWordReadout
import Vegas.Source.ProposalRecoveryTraceReadback
import Vegas.Source.CommitRecoveryCommitUnique
import GameTheory.Protocol.HistoryEvents

/-! # Exact original enriched histories identified by their finite commitment word -/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem proposalRecovery_reaches_semantic
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
theorem phaseProposalBindingPotentialProfile_source_history_injective
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix) (positive : 0 < block.length)
    (left right : setup.proposalRecoveryProtocol.History)
    (leftSupport : left ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
      block.length ⟨some cursor.current, cursor.trace⟩).support)
    (rightSupport : right ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
      block.length ⟨some cursor.current, cursor.trace⟩).support)
    (same : ((setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace left.trace)).take block.length).reverse =
        ((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace right.trace)).take block.length).reverse) :
    left = right := by
  let strategy := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  have leftReached := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin strategy
    block.length ⟨some cursor.current, cursor.trace⟩ left leftSupport
  have rightReached := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin strategy
    block.length ⟨some cursor.current, cursor.trace⟩ right rightSupport
  obtain ⟨joint, first, _second, related⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup mode runtime leaks plan
      initial horizon scheduler anchor anchorTrace phase values block suffix cursor
  rw [← first] at leftSupport rightSupport
  obtain ⟨leftPair, leftMember, leftEq⟩ := (PMF.mem_support_map_iff _ _ _).mp leftSupport
  obtain ⟨rightPair, rightMember, rightEq⟩ := (PMF.mem_support_map_iff _ _ _).mp rightSupport
  obtain ⟨leftSource, leftState, leftTrace, leftAttempt, leftHistory, _leftPoint, _leftExcluded,
    _leftGeneration, _leftLive, _leftAgreement, leftWord, leftLabels⟩ :=
    related leftPair leftMember
  obtain ⟨rightSource, rightState, rightTrace, rightAttempt, rightHistory, _rightPoint,
    _rightExcluded, _rightGeneration, _rightLive, _rightAgreement, rightWord, rightLabels⟩ :=
    related rightPair rightMember
  have leftExact : left = ⟨some leftState, leftTrace⟩ := leftEq.symm.trans leftHistory
  have rightExact : right = ⟨some rightState, rightTrace⟩ := rightEq.symm.trans rightHistory
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
  have committing : ProtocolState.atCommit setup.program cursor.current.point = true := by
    rw [cursor.point, cursor.origin.atCommit_lift]
    cases block with
    | nil => cases Nat.not_lt_zero _ positive
    | commit => rfl
  have window : block.length + ProtocolState.commitEnd setup.program cursor.current.point ≤
      ProtocolState.remaining setup.program cursor.current.point := by
    rw [cursor.point, cursor.origin.commitEnd_lift, cursor.origin.remaining_lift]
    exact block.length_le_commit_window suffix cursor.source
  have length := leftReached.trace_length_le_add
  change leftTrace.length ≤ cursor.trace.length + block.length at length
  have within : (setup.proposalRecoveryEraseTrace leftTrace).length +
      ProtocolState.commitEnd setup.program cursor.current.point ≤
        (setup.proposalRecoveryEraseTrace cursor.trace).length +
          ProtocolState.remaining setup.program cursor.current.point := by
    simp only [setup.proposalRecoveryEraseTrace_length]
    omega
  have semantic := setup.commitRecovery_history_eq_of_commit_window cursor.current
    (setup.proposalRecoveryEraseTrace cursor.trace) committing
      (setup.proposalRecoveryEraseTrace leftTrace) (setup.proposalRecoveryEraseTrace rightTrace)
      (proposalRecovery_reaches_semantic setup leftReached)
      (proposalRecovery_reaches_semantic setup rightReached) sameSemantic within
  exact setup.proposalRecoveryHistory_eq_of_semantic_word _ _ semantic sameLabels

end Vegas

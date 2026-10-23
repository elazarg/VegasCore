/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryOmissionWindow
import Vegas.Game.ProposalRecoveryResetContinuation
import Vegas.Game.CommitRecoveryOmissionWindow

/-! # Failed-window values depend only on actual omission words -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Conditional continuation after a stopped failed attempt uses the same
prescription on every retry. Its semantic values and current private memory
need not agree before reset. -/
theorem proposalRecovery_failed_stopped_terminal_eq
    (leftProfile rightProfile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (failed : first.NewFailure)
    (omissions :
      (setup.proposalRecoveryModel.runBehavioralUntil certificate leftProfile
        (fun history => prior.length + ProtocolState.remaining setup.program first.point ≤
          history.trace.length + ProtocolState.commitEnd setup.program first.point)
          ⟨some first, prior⟩).map setup.proposalRecoveryOmissionWord =
        (setup.proposalRecoveryModel.runBehavioralUntil certificate rightProfile
          (fun history => prior.length + ProtocolState.remaining setup.program first.point ≤
            history.trace.length + ProtocolState.commitEnd setup.program first.point)
            ⟨some first, prior⟩).map setup.proposalRecoveryOmissionWord) :
    let stopped := fun history : setup.proposalRecoveryProtocol.History =>
      prior.length + ProtocolState.remaining setup.program first.point ≤
        history.trace.length + ProtocolState.commitEnd setup.program first.point
    ((setup.proposalRecoveryModel.runBehavioralUntil certificate leftProfile stopped
        ⟨some first, prior⟩).bind fun boundary =>
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.proposalRecoveryPrescribedProfile prescription) boundary).map
          setup.proposalRecoveryErasedHistory =
      ((setup.proposalRecoveryModel.runBehavioralUntil certificate rightProfile stopped
        ⟨some first, prior⟩).bind fun boundary =>
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.proposalRecoveryPrescribedProfile prescription) boundary).map
          setup.proposalRecoveryErasedHistory := by
  intro stopped
  rw [PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ setup.proposalRecoveryOmissionWord
    setup.proposalRecoveryOmissionWord omissions
  intro left leftSupport right rightSupport sameWord
  obtain ⟨leftKept, leftBoundary⟩ := setup.proposalRecovery_stopped_window_boundary
    leftProfile certificate first prior committing left leftSupport
  obtain ⟨rightKept, _rightBoundary⟩ := setup.proposalRecovery_stopped_window_boundary
    rightProfile certificate first prior committing right rightSupport
  have excluded := setup.prefix_excluded (setup.proposalRecoveryEraseTrace prior)
    (setup.proposalRecoveryEraseTrace left.trace)
    (setup.proposalRecoveryEraseTrace_prefix leftKept)
  have laterFailure : left.state.elim False
      (fun current => (current.excluded \ first.entryExcluded).Nonempty) := by
    obtain ⟨owner, admitted⟩ := failed
    have old := (Finset.mem_sdiff.mp admitted).1
    have new := excluded old
    have notEntry := (Finset.mem_sdiff.mp admitted).2
    cases state : left.state with
    | none => simp only [state, commitRecoveryPublic, Finset.notMem_empty] at new
    | some current =>
        have member : owner ∈ current.excluded := by
          simpa only [state, commitRecoveryPublic] using new
        exact ⟨owner, Finset.mem_sdiff.mpr ⟨member, notEntry⟩⟩
  exact setup.proposalRecovery_failed_attempt_terminal_eq prescription certificate observer first
    prior committing left.trace right.trace leftKept rightKept sameWord leftBoundary laterFailure

end Vegas.SourceProgram.Setup

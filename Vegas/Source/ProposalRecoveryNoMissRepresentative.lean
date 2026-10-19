/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryPrefixLift
import Vegas.Source.ProposalRecoveryCommitWindow
import Vegas.Source.ProposalRecoveryProjection

/-! # Genuine archive-preserving representatives of normalized queries -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The original no-new-miss replay lifts from the SAME actual labeled entry.
Its commitment-only suffix adds no proposals, so the full observed archive
is preserved without a supplied archive or information-genuineness premise. -/
theorem proposalRecovery_query_ordinary_of_history (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (survives : who ∉ current.excluded) :
    ∃ replay : CommitRecoveryState setup.program,
      ∃ replayTrace : setup.proposalRecoveryProtocol.Trace (some replay),
        replay.excluded = replay.entryExcluded ∧
        (setup.commitRecoveryErasedInformation who
            (setup.proposalRecoveryEraseInfo who
              (setup.proposalRecoveryModel.infoOf who replayTrace)),
          setup.proposalRecoveryArchive who
            (setup.proposalRecoveryModel.infoOf who replayTrace)) =
          setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace) := by
  obtain ⟨replay, oldReplay, excluded, entryExcluded, _saved, _gen, _views,
      info, prior, retained, replayRetained, lengths, rank⟩ :=
    setup.commitRecoveryNoMissInformation_genuine who current
      (setup.proposalRecoveryEraseTrace trace) committing survives
  obtain ⟨labeledPrior, labeledRetained, projectedPrior⟩ :=
    setup.proposalRecoveryEraseTrace_prefix_inverse trace prior retained
  obtain ⟨labeledReplay, labeledReplayRetained, projectedReplay⟩ :=
    setup.proposalRecovery_lift_suffix (fun _ _ => false) prior oldReplay replayRetained
      labeledPrior projectedPrior
  have priorLength : labeledPrior.length = prior.length := by
    rw [← setup.proposalRecoveryEraseTrace_length labeledPrior, projectedPrior]
  have replayLength : labeledReplay.length = trace.length := by
    rw [← setup.proposalRecoveryEraseTrace_length labeledReplay, projectedReplay, lengths,
      setup.proposalRecoveryEraseTrace_length]
  have frontier := setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace trace)
  have savedCommit : ProtocolState.atCommit setup.program current.saved = true := by
    rcases frontier with ⟨saved, _live, _ending⟩ | same
    · exact saved
    · rwa [same]
  have ending : ProtocolState.commitEnd setup.program current.point =
      ProtocolState.commitEnd setup.program current.saved := by
    rcases frontier with ⟨_saved, _live, ending⟩ | same
    · exact ending
    · rw [same]
  have positive := ProtocolState.commitEnd_lt_remaining setup.program current.point committing
  have within : trace.length + ProtocolState.commitEnd setup.program current.saved ≤
      labeledPrior.length + ProtocolState.remaining setup.program current.saved := by
    rw [setup.proposalRecoveryEraseTrace_length] at rank
    omega
  have originalArchive := setup.proposalRecoveryArchive_eq_of_commit_window who
    (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation)
    labeledPrior savedCommit trace labeledRetained within
  have replayArchive := setup.proposalRecoveryArchive_eq_of_commit_window who
    (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation)
    labeledPrior savedCommit labeledReplay labeledReplayRetained (by
      change labeledReplay.length + ProtocolState.commitEnd setup.program current.saved ≤
        labeledPrior.length + ProtocolState.remaining setup.program current.saved
      simpa only [replayLength] using within)
  refine ⟨replay, labeledReplay, excluded.trans entryExcluded.symm, ?_⟩
  apply Prod.ext
  · change setup.commitRecoveryErasedInformation who
        (setup.proposalRecoveryEraseInfo who
          (setup.proposalRecoveryModel.infoOf who labeledReplay)) = _
    rw [setup.proposalRecoveryEraseInfo_observed, projectedReplay, info]
    change _ = setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who
        (setup.proposalRecoveryEraseInfo who
          (setup.proposalRecoveryModel.infoOf who trace)))
    rw [setup.proposalRecoveryEraseInfo_observed]
  · exact replayArchive.trans originalArchive.symm

end Vegas.SourceProgram.Setup

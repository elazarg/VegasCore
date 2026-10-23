/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryCommitWindow
import Vegas.Source.CommitRecoveryNoMissFixed

/-! # The actual ordinary class and failed remainder of enriched query fibers -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A normalized fiber contains the ordinary full erased-information/archive
class and histories with an actual new exclusion. The classification is
inherited from the original recovery controls, with the archive kept exactly. -/
theorem proposalRecovery_query_fiber_cases (who : Player)
    (first second : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some first))
    (right : setup.proposalRecoveryProtocol.Trace (some second))
    (firstUnchanged : first.excluded = first.entryExcluded)
    (same : setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who left) =
      setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who right)) :
    (setup.commitRecoveryErasedInformation who
        (setup.proposalRecoveryEraseInfo who (setup.proposalRecoveryModel.infoOf who left)) =
      setup.commitRecoveryErasedInformation who
        (setup.proposalRecoveryEraseInfo who (setup.proposalRecoveryModel.infoOf who right)) ∧
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who left) =
        setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right)) ∨
      second.NewFailure := by
  have semantic := congrArg Prod.fst same
  change setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who (setup.proposalRecoveryEraseInfo who
        (setup.proposalRecoveryModel.infoOf who left))) =
    setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who (setup.proposalRecoveryEraseInfo who
        (setup.proposalRecoveryModel.infoOf who right))) at semantic
  rw [setup.proposalRecoveryEraseInfo_observed,
    setup.proposalRecoveryEraseInfo_observed] at semantic
  rcases setup.commitRecovery_query_fiber_cases who first second
      (setup.proposalRecoveryEraseTrace left) (setup.proposalRecoveryEraseTrace right)
      firstUnchanged semantic with ordinary | failed
  · apply Or.inl
    constructor
    · rwa [setup.proposalRecoveryEraseInfo_observed,
        setup.proposalRecoveryEraseInfo_observed]
    · exact congrArg Prod.snd same
  · exact Or.inr failed

end Vegas.SourceProgram.Setup

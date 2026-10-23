/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReplayPath
import Vegas.Source.ProposalRecoveryInformation
import Vegas.Source.ProposalRecoveryLift

/-! # Canonical archive increments of the actual annotated source history -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- This is the existing proposal delta decoder folded over actual source
steps. No value or native membership is supplied by the fold. -/
def replayProposalArchive (setup : Setup (Player := Player) (L := L))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (events : List setup.commitRecoveryProtocol.StepEvent) : Finset (ProposalRecoveryProposal L) :=
  (events.flatMap fun event => (setup.proposalRecoveryProposalOf event.source
    (setup.proposalRecoveryLiftJoint labels event)).toList).toFinset

theorem mem_replayProposalArchive (setup : Setup (Player := Player) (L := L))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (events : List setup.commitRecoveryProtocol.StepEvent) (proposal : ProposalRecoveryProposal L) :
    proposal ∈ replayProposalArchive setup labels events ↔
      ∃ event ∈ events, setup.proposalRecoveryProposalOf event.source
        (setup.proposalRecoveryLiftJoint labels event) = some proposal := by
  simp only [replayProposalArchive, List.mem_toFinset, List.mem_flatMap, Option.mem_toList]

theorem proposalLabeledWord_eq_sourceSteps (setup : Setup (Player := Player) (L := L))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.proposalRecoveryLabeledWord labels trace =
      (proposalSourceSteps setup trace).flatMap fun event =>
        (setup.proposalRecoveryProposalOf event.source
          (setup.proposalRecoveryLiftJoint labels event)).toList := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      simp only [Setup.proposalRecoveryLabeledWord, proposalSourceSteps_extend,
        List.flatMap_append, List.flatMap_singleton, ih]

/-- An actual source trace extension adds exactly the deltas of its newly
appended steps; all earlier proposal labels are retained literally. -/
theorem proposalLift_archive_extension
    (setup : Setup (Player := Player) (L := L))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) (who : Player)
    {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (trace : setup.commitRecoveryProtocol.Trace after)
    (events : List setup.commitRecoveryProtocol.StepEvent)
    (steps : proposalSourceSteps setup trace = proposalSourceSteps setup prior ++ events) :
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace labels trace)) =
      setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace labels prior)) ∪
      replayProposalArchive setup labels events := by
  rw [setup.proposalRecoveryArchive_lift, setup.proposalRecoveryArchive_lift,
    proposalLabeledWord_eq_sourceSteps, proposalLabeledWord_eq_sourceSteps, steps,
    List.flatMap_append, List.toFinset_append]
  rfl

end Vegas

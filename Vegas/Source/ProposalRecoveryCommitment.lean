/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryArchiveLookup

/-! # Commitment replay preserves the complete proposal archive -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem ProtocolState.recoveryProposal_eq_none_of_atCommit :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      atCommit program point = true → ∀ joint, recoveryProposal program point joint = none
  | _, _, .ret _, _, committing, _ => by cases committing
  | _, _, .sample _ _ _ next, point, committing, joint => by
      cases point with
      | inl _ => cases committing
      | inr point =>
          simpa only [recoveryProposal, Sum.elim_inr, Option.map_none] using
            congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
              (recoveryProposal_eq_none_of_atCommit next point committing joint)
  | _, _, .commit _ _ _ _ next, point, committing, joint => by
      cases point with
      | inl _ => rfl
      | inr point =>
          simpa only [recoveryProposal, Sum.elim_inr, Option.map_none] using
            congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
              (recoveryProposal_eq_none_of_atCommit next point committing joint)
  | _, _, .reveal _ _ _ _ _ _ next, point, committing, joint => by
      cases point with
      | inl _ => cases committing
      | inr point =>
          simpa only [recoveryProposal, Sum.elim_inr, Option.map_none] using
            congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
              (recoveryProposal_eq_none_of_atCommit next point committing joint)

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryProposalOf_eq_none_of_atCommit
    (current : CommitRecoveryState setup.program)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf (some current) joint = none := by
  have absent := ProtocolState.recoveryProposal_eq_none_of_atCommit setup.program current.point
    committing (fun who => if who ∈ current.excluded then none else joint who)
  simp only [proposalRecoveryProposalOf, Option.bind_some, absent, Option.map_none]

theorem proposalRecoveryArchive_eq_of_silent_prefix (who : Player)
    {first last : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace first)
    (trace : setup.proposalRecoveryProtocol.Trace last) (kept : TracePrefix prior trace)
    (silent : ∀ {before after : setup.proposalRecoveryProtocol.State}
      (middle : setup.proposalRecoveryProtocol.Trace before)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before joint)
      (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support),
      TracePrefix prior middle → TracePrefix (middle.extend joint legal supported) trace →
        setup.proposalRecoveryProposalOf before joint = none) :
    setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who trace) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who prior) := by
  induction kept with
  | refl => rfl
  | @extend before after middle kept joint legal supported ih =>
      rw [setup.proposalRecoveryArchive_extend, silent middle joint legal supported kept .refl,
        Option.toList_none, List.toFinset_nil, Finset.union_empty]
      apply ih
      intro source target earlier selected allowed reached fromFirst toMiddle
      exact silent earlier selected allowed reached fromFirst
        (toMiddle.extend joint legal supported)

end Setup
end Vegas.SourceProgram

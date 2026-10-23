/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryObservation
import Vegas.Source.CommitRecoveryErasedStep

/-! # Truthful proposal labels under source-memory erasure -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- A proposal is read from the live typed store, never from a retired word. -/
theorem recoveryProposal_withHistory :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (past : History Player L) (joint : Player → Option (ProposalRecoveryMove Player L)),
      recoveryProposal program (withHistory program point past) joint =
        recoveryProposal program point joint
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, past, joint => by
      cases point with
      | inl _ => rfl
      | inr point =>
          exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
            (recoveryProposal_withHistory next point past joint)
  | _, _, .commit _ _ _ _ next, point, past, joint => by
      cases point with
      | inl _ => rfl
      | inr point =>
          exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
            (recoveryProposal_withHistory next point past joint)
  | _, _, .reveal _ _ _ _ _ _ next, point, past, joint => by
      cases point with
      | inl _ => rfl
      | inr point =>
          exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
            (recoveryProposal_withHistory next point past joint)

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryProposalOf_eraseHistory
    (state : setup.proposalRecoveryProtocol.State)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf (state.map CommitRecoveryState.eraseHistory) joint =
      setup.proposalRecoveryProposalOf state joint := by
  cases state with
  | none => rfl
  | some current =>
      simp only [Option.map_some, proposalRecoveryProposalOf, Option.bind_some,
        CommitRecoveryState.eraseHistory, ProtocolState.recoveryProposal_withHistory]

theorem proposalRecoveryProposalOf_eq_of_erased
    {first second : setup.proposalRecoveryProtocol.State}
    (same : first.map CommitRecoveryState.eraseHistory =
      second.map CommitRecoveryState.eraseHistory)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf first joint =
      setup.proposalRecoveryProposalOf second joint := by
  rw [← setup.proposalRecoveryProposalOf_eraseHistory first joint, same,
    setup.proposalRecoveryProposalOf_eraseHistory second joint]

/-- Both the actual semantic transition and its extra public proposal delta
agree after erasure. Failed delivery and failed guards remain visible. -/
theorem proposalRecovery_step_erased_eq
    {first second : setup.proposalRecoveryProtocol.State}
    (same : first.map CommitRecoveryState.eraseHistory =
      second.map CommitRecoveryState.eraseHistory)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (firstLegal : setup.proposalRecoveryProtocol.Legal first joint)
    (secondLegal : setup.proposalRecoveryProtocol.Legal second joint) :
    (setup.proposalRecoveryProtocol.step first ⟨joint, firstLegal⟩).map
        (fun target => (target.map CommitRecoveryState.eraseHistory,
          setup.proposalRecoveryProposalOf first joint)) =
      (setup.proposalRecoveryProtocol.step second ⟨joint, secondLegal⟩).map
        (fun target => (target.map CommitRecoveryState.eraseHistory,
          setup.proposalRecoveryProposalOf second joint)) := by
  have delta := setup.proposalRecoveryProposalOf_eq_of_erased same joint
  rw [setup.proposalRecovery_step, setup.proposalRecovery_step, delta]
  suffices erased :
      (setup.commitRecoveryProtocol.step first
        ⟨proposalRecoveryJoint joint, setup.proposalRecovery_erase_legal joint firstLegal⟩).map
          (Option.map CommitRecoveryState.eraseHistory) =
      (setup.commitRecoveryProtocol.step second
        ⟨proposalRecoveryJoint joint, setup.proposalRecovery_erase_legal joint secondLegal⟩).map
          (Option.map CommitRecoveryState.eraseHistory) by
    have transported := congrArg
      (PMF.map fun target => (target, setup.proposalRecoveryProposalOf second joint)) erased
    rw [PMF.map_comp, PMF.map_comp] at transported
    exact transported
  cases first with
  | none => cases second <;> cases same; rfl
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have states := Option.some.inj same
          simp only [commitRecoveryProtocol, PMF.map_comp]
          change (first.step (proposalRecoveryJoint joint)).map
              (some ∘ CommitRecoveryState.eraseHistory) =
            (second.step (proposalRecoveryJoint joint)).map
              (some ∘ CommitRecoveryState.eraseHistory)
          rw [← PMF.map_comp, ← PMF.map_comp, ← first.step_eraseHistory,
            ← second.step_eraseHistory, states]

end Setup
end Vegas.SourceProgram

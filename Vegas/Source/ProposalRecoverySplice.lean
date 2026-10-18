/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryObservation
import Vegas.Source.CommitRecoveryClosedSplice

/-! # Actual proposal readout under owner substitution -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- The actual proposal belongs to the current actor's live binding. Under
owner substitution it follows that owner's original state and action. -/
theorem recoveryProposal_splice (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      MetadataEq program mine others →
      ∀ (left right : Player → Option (ProposalRecoveryMove Player L)),
      recoveryProposal program (splice focal program mine others)
          (Function.update right focal (left focal)) =
        if actor program others = some focal then recoveryProposal program mine left
        else recoveryProposal program others right
  | _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, mine, others, same, left, right => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · simp only [splice, recoveryProposal, Sum.elim_inr, actor]
        rw [recoveryProposal_splice focal next _ _ same left right]
        split <;> rfl
  | _, _, .commit _ _ _ _ next, mine, others, same, left, right => by
      cases mine <;> cases others
      · simp only [splice, recoveryProposal, Sum.elim_inl, actor, ite_self]
      · cases same
      · cases same
      · simp only [splice, recoveryProposal, Sum.elim_inr, actor]
        rw [recoveryProposal_splice focal next _ _ same left right]
        split <;> rfl
  | _, _, .reveal _ owner _ _ _ _ next, mine, others, same, left, right => by
      cases mine <;> cases others
      · by_cases own : owner = focal
        · subst owner
          simp only [splice, recoveryProposal, Sum.elim_inl, actor, Function.update_self,
            Config.splice, ite_true]
          simp only [Env.get, SourceProgram.splice, CellTy.hiddenOwner?, ite_true]
        · simp only [splice, recoveryProposal, Sum.elim_inl, actor,
            Function.update_of_ne own, Config.splice, Option.some.injEq, own, ite_false]
          simp only [Env.get, SourceProgram.splice, CellTy.hiddenOwner?,
            Option.some.injEq, own, ite_false]
      · cases same
      · cases same
      · simp only [splice, recoveryProposal, Sum.elim_inr, actor]
        rw [recoveryProposal_splice focal next _ _ same left right]
        split <;> rfl

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryProposalOf_splice (focal : Player)
    (mine others : CommitRecoveryState setup.program) (same : mine.MetadataEq others)
    (left right : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf (some (CommitRecoveryState.splice focal mine others))
        (Function.update right focal (left focal)) =
      if ProtocolState.actor setup.program others.point = some focal then
        setup.proposalRecoveryProposalOf (some mine) left
      else setup.proposalRecoveryProposalOf (some others) right := by
  let leftMasked := fun who => if who ∈ mine.excluded then none else left who
  let rightMasked := fun who => if who ∈ others.excluded then none else right who
  have masked :
      (fun who => if who ∈ others.excluded then none
        else Function.update right focal (left focal) who) =
      Function.update rightMasked focal (leftMasked focal) := by
    funext who
    by_cases own : who = focal
    · subst who
      simp only [Function.update_self, leftMasked, same.2.2.1]
    · simp only [Function.update_of_ne own, rightMasked]
  simp only [proposalRecoveryProposalOf, Option.bind_some, CommitRecoveryState.splice]
  rw [masked, ProtocolState.recoveryProposal_splice focal setup.program
    mine.point others.point same.1 leftMasked rightMasked]
  split
  · rw [same.2.2.2.2]
  · rfl

/-- The true public proposal word is preserved by the original owner
substitution whenever the two actual public deltas agree. -/
theorem proposalRecoveryProposalOf_splice_eq (focal : Player)
    (mine others : CommitRecoveryState setup.program) (same : mine.MetadataEq others)
    (left right : Player → Option (ProposalRecoveryMove Player L))
    (delta : setup.proposalRecoveryProposalOf (some mine) left =
      setup.proposalRecoveryProposalOf (some others) right) :
    setup.proposalRecoveryProposalOf (some (CommitRecoveryState.splice focal mine others))
        (Function.update right focal (left focal)) =
      setup.proposalRecoveryProposalOf (some others) right := by
  rw [setup.proposalRecoveryProposalOf_splice focal mine others same left right, delta]
  split <;> rfl

end Setup
end Vegas.SourceProgram

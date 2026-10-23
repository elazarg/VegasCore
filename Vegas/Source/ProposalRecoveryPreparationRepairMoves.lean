/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryPreparationRepairLabels
import Vegas.Source.ProposalRecoveryInformation

/-! # Generated source failures and the repaired owner's literal moves -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProposalRecoveryMove

/-- A generated preparation failure is a nonmissing failed COMMIT. It is
neither a withholding action nor an automatic or inherited failed cell. -/
def GeneratedPreparationFailure (choice : Option (ProposalRecoveryMove Player L)) : Prop :=
  choice.elim False fun move => move.semantic.missing = false ∧
    match move.semantic.action with
    | .commit _ _ _ .failure => True
    | _ => False

end ProposalRecoveryMove

namespace ProtocolState

/-- Every designated response in the actual repaired word is free of a
generated unusable preparation. Literal omissions remain permitted. -/
theorem repairPreparationJoint_prepared (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (ProposalRecoveryMove Player L)),
      IsLegalJoint (CommitRecoveryState.atPoint point excluded 0).Active
        (CommitRecoveryState.atPoint point excluded 0).available
        (Setup.proposalRecoveryJoint joint) →
      ¬ ProposalRecoveryMove.GeneratedPreparationFailure
        (repairPreparationJoint who program point joint who) := by
  intro Γ O program
  induction program with
  | ret payoff =>
      intro point excluded joint legal
      have offered := legal who
      cases chosen : joint who with
      | none => simp [repairPreparationJoint, chosen,
          ProposalRecoveryMove.GeneratedPreparationFailure]
      | some move =>
          simp only [Setup.proposalRecoveryJoint, chosen, Option.map_some] at offered
          cases offered.1.1
  | sample name fresh law next ih =>
      intro point excluded joint legal
      cases point with
      | inr point => exact ih point excluded joint legal
      | inl config =>
          have offered := legal who
          cases chosen : joint who with
          | none => simp [repairPreparationJoint, chosen,
              ProposalRecoveryMove.GeneratedPreparationFailure]
          | some move =>
              simp only [Setup.proposalRecoveryJoint, chosen, Option.map_some] at offered
              cases offered.1.1
  | @commit Γ O name owner payload fresh guard next ih =>
      intro point excluded joint legal
      cases point with
      | inr point => exact ih point excluded joint legal
      | inl config =>
          have offered := legal who
          cases chosen : joint who with
          | none =>
              simp only [repairPreparationJoint, Sum.elim_inl]
              split
              · rename_i own
                subst owner
                simp [chosen, ProposalRecoveryMove.GeneratedPreparationFailure]
              · simp [chosen, ProposalRecoveryMove.GeneratedPreparationFailure]
          | some move =>
              simp only [Setup.proposalRecoveryJoint, chosen, Option.map_some] at offered
              have own : owner = who := Option.some.inj offered.1.1
              subst owner
              obtain ⟨atom, semantic⟩ := CommitRecoveryMove.exists_bindingAtom_of_available
                who name payload fresh guard next (config.view who) move.semantic offered.2
              cases move with | mk original proposed =>
                dsimp only at semantic
                subst original
                cases atom with
                | inl value =>
                    simp [repairPreparationJoint, chosen, CommitRecoveryMove.bindingAtom,
                      OwnAction.binding_commit, ProposalRecoveryMove.GeneratedPreparationFailure]
                | inr marker => cases marker <;>
                    simp [repairPreparationJoint, chosen, CommitRecoveryMove.bindingAtom,
                      OwnAction.binding_commit, ProposalRecoveryMove.GeneratedPreparationFailure]
  | reveal published owner name fresh source unresolved next ih =>
      intro point excluded joint legal
      cases point with
      | inr point => exact ih point excluded joint legal
      | inl config =>
          have offered := legal who
          cases chosen : joint who with
          | none =>
              simp only [repairPreparationJoint, Sum.elim_inl]
              split
              · rename_i own
                subst owner
                cases bound : config.state.get source <;>
                  simp [chosen, ProposalRecoveryMove.GeneratedPreparationFailure]
              · simp [chosen, ProposalRecoveryMove.GeneratedPreparationFailure]
          | some move =>
              simp only [Setup.proposalRecoveryJoint, chosen, Option.map_some] at offered
              have own : owner = who := Option.some.inj offered.1.1
              subst owner
              obtain ⟨⟨bit, semantic⟩, marker⟩ := offered.2
              cases move with | mk original proposed =>
                cases original with | mk action missing =>
                  dsimp only at semantic marker
                  cases semantic
                  cases marker
                  cases bound : config.state.get source <;>
                    simp [repairPreparationJoint, chosen, bound,
                      ProposalRecoveryMove.GeneratedPreparationFailure]

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- This predicate reads only actual owned COMMIT actions in the enriched
source history, rather than inspecting inherited or automatic semantic cells. -/
def GeneratedPreparationHistory (owner : Player)
    (history : setup.proposalRecoveryProtocol.History) : Prop :=
  ∃ record ∈ setup.proposalRecoveryModel.ownPlay owner history.trace,
    ProposalRecoveryMove.GeneratedPreparationFailure (some record.2)

end Setup
end Vegas.SourceProgram

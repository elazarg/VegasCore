/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryProjection
import Vegas.Source.ProposalRecoveryLift
import GameTheory.Math.Probability.UniformTremble

/-! # Externally chosen recovery flags and domain floors -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProposalRecoveryMove

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem label_reconstruct (move : ProposalRecoveryMove Player L) (valid : move.Valid) :
    label move.semantic move.proposed = move := by
  rcases move with ⟨⟨action, missing⟩, proposed⟩
  cases proposed with
  | false =>
      cases action with
      | commit => rfl
      | reveal _ _ disclose => cases disclose <;> rfl
  | true =>
      obtain ⟨owner, name, same⟩ := valid rfl
      change action = .reveal owner name false at same
      subst action
      rfl

end ProposalRecoveryMove

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryMenu_semantic (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (choice : Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryMenu who information choice ↔
      setup.commitRecoveryMenu who (setup.proposalRecoveryEraseInfo who information)
        (choice.map (·.semantic)) ∧ choice.elim True ProposalRecoveryMove.Valid := by
  cases choice with
  | none =>
      simp only [proposalRecoveryMenu, commitRecoveryMenu, Option.map_none, Option.elim_none,
        proposalRecoveryActive, proposalRecoveryEraseInfo, proposalRecoveryEraseBaseInfo,
        proposalRecoveryEraseSignal, and_true]
  | some move =>
      cases current : information.1.1.1 with
      | none =>
          simp only [proposalRecoveryMenu, commitRecoveryMenu, Option.map_some, Option.elim_some,
            proposalRecoveryActive, proposalRecoveryEraseInfo, proposalRecoveryEraseBaseInfo,
            proposalRecoveryEraseSignal, current, Option.elim_none, and_false, false_and]
      | some view =>
          simp only [proposalRecoveryMenu, commitRecoveryMenu, Option.map_some, Option.elim_some,
            proposalRecoveryActive, proposalRecoveryEraseInfo, proposalRecoveryEraseBaseInfo,
            proposalRecoveryEraseSignal, current, and_assoc]

def proposalRecoverySemanticChoice (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who information) :
    setup.commitRecoveryModel.Choice who (setup.proposalRecoveryEraseInfo who information) :=
  ⟨choice.1.map (·.semantic), by
    change setup.commitRecoveryMenu who (setup.proposalRecoveryEraseInfo who information) _
    exact ((setup.proposalRecoveryMenu_semantic who information choice.1).mp choice.2).1⟩

def proposalRecoveryLabelChoice (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) (requested : Bool)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.proposalRecoveryEraseInfo who information)) :
    setup.proposalRecoveryModel.Choice who information := by
  refine ⟨choice.1.map (fun move => ProposalRecoveryMove.label move requested), ?_⟩
  apply (setup.proposalRecoveryMenu_semantic who information _).mpr
  constructor
  · have allowed := choice.2
    change setup.commitRecoveryMenu who (setup.proposalRecoveryEraseInfo who information) _
      at allowed
    simp only [Option.map_map, Function.comp_def, ProposalRecoveryMove.label_semantic]
    change setup.commitRecoveryMenu who (setup.proposalRecoveryEraseInfo who information)
      (choice.1.map id)
    rw [Option.map_id]
    exact allowed
  · cases selected : choice.1 with
    | none => trivial
    | some move => exact ProposalRecoveryMove.label_valid move requested

end Setup
end Vegas.SourceProgram

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryProjection
import Vegas.Source.ProposalRecoveryLift
import Vegas.Source.ProposalRecoveryFiniteness
import Vegas.Source.CommitRecoveryValueTremble
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

def proposalRecoveryChoiceFlag (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who information) : Bool :=
  (choice.1.map (·.proposed)).getD false

theorem proposalRecoveryLabelChoice_reconstruct (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who information) :
    setup.proposalRecoveryLabelChoice who information
      (setup.proposalRecoveryChoiceFlag who information choice)
      (setup.proposalRecoverySemanticChoice who information choice) = choice := by
  apply Subtype.ext
  change (choice.1.map (·.semantic)).map
    (fun move => ProposalRecoveryMove.label move ((choice.1.map (·.proposed)).getD false)) =
      choice.1
  have valid := ((setup.proposalRecoveryMenu_semantic who information choice.1).mp choice.2).2
  cases selected : choice.1 with
  | none => rfl
  | some move =>
      simp only [selected, Option.elim_some] at valid
      simp only [Option.map_some, Option.getD_some,
        ProposalRecoveryMove.label_reconstruct move valid]

/-- All rates are caller supplied. Ordinary semantic values remain a separate
optimization variable; a proposal label is sampled independently afterward. -/
def proposalRecoveryTrembledLaw (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information))) :
    PMF (setup.proposalRecoveryModel.Choice who information) :=
  (setup.commitRecoveryValueTremble who (setup.proposalRecoveryEraseInfo who information)
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded values).bind
      fun choice =>
        (mix delivery deliveryNonnegative deliveryBounded (PMF.pure true) (PMF.pure false)).map
          (fun requested => setup.proposalRecoveryLabelChoice who information requested choice)

theorem proposalRecoveryTrembledLaw_fullSupport (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (delivery : ℝ) (deliveryPositive : 0 < delivery) (deliverySmall : delivery < 1)
    (values : PMF (setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information))) (full : FullSupport values) :
    FullSupport (setup.proposalRecoveryTrembledLaw who information
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
      delivery deliveryPositive.le deliverySmall.le values) := by
  intro choice
  refine (PMF.mem_support_bind_iff _ _ _).mpr
    ⟨setup.proposalRecoverySemanticChoice who information choice, ?_, ?_⟩
  · exact setup.commitRecoveryValueTremble_fullSupport who _ omission omissionPositive
      omissionSmall bad badPositive badSmall values full _
  · refine (PMF.mem_support_map_iff _ _ _).mpr
      ⟨setup.proposalRecoveryChoiceFlag who information choice, ?_,
        setup.proposalRecoveryLabelChoice_reconstruct who information choice⟩
    cases setup.proposalRecoveryChoiceFlag who information choice with
    | false =>
        exact mem_support_mix_right _ _ _ deliverySmall
          ((PMF.mem_support_pure_iff _ _).mpr rfl)
    | true =>
        exact mem_support_mix_left _ _ _ deliveryPositive
          ((PMF.mem_support_pure_iff _ _).mpr rfl)

/-- This floor is fixed independently of the optimized ordinary distribution
and before the separate bad-preparation rate is chosen. -/
def proposalRecoveryDomainLaw (finite : setup.program.FiniteBindingTypes) (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information))) :=
  let := setup.commitRecoveryValueChoice_finite finite who
    (setup.proposalRecoveryEraseInfo who information)
  let := Fintype.ofFinite (setup.CommitRecoveryValueChoice who
    (setup.proposalRecoveryEraseInfo who information))
  let := setup.commitRecoveryValueChoice_nonempty who
    (setup.proposalRecoveryEraseInfo who information)
  mix floor nonnegative bounded (PMF.uniformOfFintype _) values

theorem proposalRecoveryDomainLaw_lower (finite : setup.program.FiniteBindingTypes)
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)))
    (value : setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)) :
    floor / Nat.card (setup.CommitRecoveryValueChoice who
        (setup.proposalRecoveryEraseInfo who information)) ≤
      (setup.proposalRecoveryDomainLaw finite who information
        floor nonnegative bounded values value).toReal := by
  let := setup.commitRecoveryValueChoice_finite finite who
    (setup.proposalRecoveryEraseInfo who information)
  let := Fintype.ofFinite (setup.CommitRecoveryValueChoice who
    (setup.proposalRecoveryEraseInfo who information))
  let := setup.commitRecoveryValueChoice_nonempty who
    (setup.proposalRecoveryEraseInfo who information)
  simpa only [proposalRecoveryDomainLaw, Nat.card_eq_fintype_card] using
    div_card_le_mix_uniform_apply floor nonnegative bounded values value

end Setup
end Vegas.SourceProgram

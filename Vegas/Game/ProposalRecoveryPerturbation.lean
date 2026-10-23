/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPrescription
import Vegas.Game.CommitRecoveryPooledCompletion
import Vegas.Game.CommitRecoveryOmissionKernel

/-! # Caller-selected neutral failure rates on enriched source coordinates -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoveryComponentSemanticChoice (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (choice : setup.ProposalRecoveryComponentChoice who key) :
    setup.commitRecoveryModel.Choice who key.1 :=
  ⟨choice.1.map (fun move : ProposalRecoveryMove Player L => move.semantic), choice.2.1⟩

def proposalRecoveryComponentLabelChoice (who : Player)
    (key : setup.ProposalRecoveryComponent who) (requested : Bool)
    (choice : setup.commitRecoveryModel.Choice who key.1) :
    setup.ProposalRecoveryComponentChoice who key := by
  refine ⟨choice.1.map (fun move => ProposalRecoveryMove.label move requested), ?_, ?_⟩
  · simp only [Option.map_map, Function.comp_def, ProposalRecoveryMove.label_semantic]
    change setup.commitRecoveryModel.menu who key.1 (choice.1.map id)
    rw [Option.map_id]
    exact choice.2
  · cases selected : choice.1 with
    | none => trivial
    | some move => exact ProposalRecoveryMove.label_valid move requested

theorem proposalRecoveryComponentLabelChoice_semantic (who : Player)
    (key : setup.ProposalRecoveryComponent who) (requested : Bool)
    (choice : setup.commitRecoveryModel.Choice who key.1) :
    setup.proposalRecoveryComponentSemanticChoice who key
      (setup.proposalRecoveryComponentLabelChoice who key requested choice) = choice := by
  apply Subtype.ext
  change (choice.1.map (fun move => ProposalRecoveryMove.label move requested)).map
    (·.semantic) = choice.1
  simp only [Option.map_map, Function.comp_def, ProposalRecoveryMove.label_semantic]
  change choice.1.map id = choice.1
  rw [Option.map_id]
  rfl

private theorem label_reconstruct (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (choice : setup.ProposalRecoveryComponentChoice who key) :
    setup.proposalRecoveryComponentLabelChoice who key
      ((choice.1.map (·.proposed)).getD false)
      (setup.proposalRecoveryComponentSemanticChoice who key choice) = choice := by
  apply Subtype.ext
  change (choice.1.map (·.semantic)).map
    (fun move => ProposalRecoveryMove.label move ((choice.1.map (·.proposed)).getD false)) =
      choice.1
  have valid := choice.2.2
  cases selected : choice.1 with
  | none => rfl
  | some move =>
      simp only [selected, Option.elim_some] at valid
      simp only [Option.map_some, Option.getD_some,
        ProposalRecoveryMove.label_reconstruct move valid]

/-- Omission and bad-preparation rates do not depend on the optimized values
or hidden source data. The delivery label is a conditional flag sampled only
after the semantic choice, rather than an unconditional failure probability. -/
def proposalRecoveryComponentTrembledLaw (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1)) :
    PMF (setup.ProposalRecoveryComponentChoice who key) :=
  (setup.commitRecoveryValueTremble who key.1 omission omissionNonnegative omissionBounded
    bad badNonnegative badBounded values).bind fun choice =>
      (mix delivery deliveryNonnegative deliveryBounded (PMF.pure true) (PMF.pure false)).map
        (fun requested => setup.proposalRecoveryComponentLabelChoice who key requested choice)

theorem proposalRecoveryComponentTrembledLaw_fullSupport (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (delivery : ℝ) (deliveryPositive : 0 < delivery) (deliverySmall : delivery < 1)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1)) (full : FullSupport values) :
    FullSupport (setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
      delivery deliveryPositive.le deliverySmall.le values) := by
  intro choice
  refine (PMF.mem_support_bind_iff _ _ _).mpr
    ⟨setup.proposalRecoveryComponentSemanticChoice who key choice, ?_, ?_⟩
  · exact setup.commitRecoveryValueTremble_fullSupport who _ omission omissionPositive
      omissionSmall bad badPositive badSmall values full _
  · refine (PMF.mem_support_map_iff _ _ _).mpr
      ⟨((choice.1.map (·.proposed)).getD false), ?_, setup.label_reconstruct who key choice⟩
    cases ((choice.1.map (·.proposed)).getD false) with
    | false =>
        exact mem_support_mix_right _ _ _ deliverySmall
          ((PMF.mem_support_pure_iff _ _).mpr rfl)
    | true =>
        exact mem_support_mix_left _ _ _ deliveryPositive
          ((PMF.mem_support_pure_iff _ _).mpr rfl)

theorem proposalRecoveryComponentTrembledLaw_semantic (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1)) :
    (setup.proposalRecoveryComponentTrembledLaw who key omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded values).map
          (setup.proposalRecoveryComponentSemanticChoice who key) =
      setup.commitRecoveryValueTremble who key.1 omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values := by
  simp only [proposalRecoveryComponentTrembledLaw, PMF.map_bind, PMF.map_comp, Function.comp_def,
    setup.proposalRecoveryComponentLabelChoice_semantic]
  change ((setup.commitRecoveryValueTremble who key.1 omission omissionNonnegative omissionBounded
    bad badNonnegative badBounded values).bind fun choice =>
      (mix delivery deliveryNonnegative deliveryBounded (PMF.pure true) (PMF.pure false)).map
        (Function.const _ choice)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem proposalRecoveryComponentTrembledLaw_bind (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    {Part : Type} (weights : PMF Part)
    (values : Part → PMF (setup.CommitRecoveryValueChoice who key.1)) :
    weights.bind (fun part => setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded (values part)) =
      setup.proposalRecoveryComponentTrembledLaw who key
        omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded
        (weights.bind values) := by
  unfold proposalRecoveryComponentTrembledLaw
  rw [← PMF.bind_bind, setup.commitRecoveryValueTremble_bind]

/-- The ordinary value law can read the enriched archive; neutral flags retain
exactly the original semantic marginal on each common source coordinate. -/
def proposalRecoveryNormalizedTrembledProfile
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1)) :
    ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who :=
  setup.proposalRecoveryPrescribedProfile fun who key =>
    setup.proposalRecoveryComponentTrembledLaw who key omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded (values who key)

/-- A one-site semantic marginal is the existing normalized flag law with
the current archive held fixed as a parameter. This is not a projection of
whole enriched play to a forgetful source strategy or source posterior. -/
theorem proposalRecoveryNormalizedTrembledProfile_semantic
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who) :
    (setup.proposalRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded values
        who information).map (fun choice => choice.1.map (·.semantic)) =
      (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded
        (fun owner old => values owner (old, setup.proposalRecoveryArchive who information))
        who (setup.proposalRecoveryEraseInfo who information)).map Subtype.val := by
  let key := setup.proposalRecoveryQuery who information
  have prescribed := setup.proposalRecoveryPrescribedProfile_raw
    (fun owner coordinate => setup.proposalRecoveryComponentTrembledLaw owner coordinate
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded (values owner coordinate)) who information
  have raw := congrArg (PMF.map fun move : Option (ProposalRecoveryMove Player L) =>
    move.map (·.semantic)) prescribed
  rw [PMF.map_comp, PMF.map_comp] at raw
  have semantic := congrArg (PMF.map Subtype.val)
    (setup.proposalRecoveryComponentTrembledLaw_semantic who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded (values who key))
  simp only [PMF.map_comp, Function.comp_def, proposalRecoveryComponentSemanticChoice]
    at semantic
  change (setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded (values who key)).map
        (fun choice => choice.1.map (fun move : ProposalRecoveryMove Player L => move.semantic)) =
    (setup.commitRecoveryValueTremble who key.1 omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values who key)).map Subtype.val at semantic
  have current : (setup.proposalRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded values who information).map
        (fun choice => choice.1.map (·.semantic)) =
      (setup.commitRecoveryValueTremble who key.1 omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded (values who key)).map Subtype.val := by
    exact raw.trans (by
      exact semantic)
  rw [current, commitRecoveryNormalizedTrembledProfile, setup.commitRecoveryNoMissErasedProfile_raw]
  rfl

open Classical in
/-- The actual enriched full-information policy inherits the old neutral
omission coin without identifying its archive-dependent continuation law. -/
theorem proposalRecoveryNormalizedTrembledProfile_missed_law
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (committing : information.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    (setup.proposalRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded values
        who information).map
          (fun choice => CommitRecoveryMove.missed (choice.1.map (·.semantic))) =
      if setup.proposalRecoveryActive who information.1.1 then
        mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false)
      else PMF.pure false := by
  have semantic := setup.proposalRecoveryNormalizedTrembledProfile_semantic
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded values who information
  have raw := congrArg (PMF.map CommitRecoveryMove.missed) semantic
  have old := setup.commitRecoveryNormalizedTrembledProfile_missed_law
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    (fun owner old => values owner (old, setup.proposalRecoveryArchive who information))
    who (setup.proposalRecoveryEraseInfo who information) committing
  simp only [PMF.map_comp, Function.comp_def] at raw
  exact raw.trans old

end Vegas.SourceProgram.Setup

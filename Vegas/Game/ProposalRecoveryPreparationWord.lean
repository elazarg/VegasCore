/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPreparationBadMass
import Vegas.Game.ProposalRecoveryPreparationChance
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Actual source response-word upper and lower bounds -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

local notation "E" => Setup.proposalRecoveryProtocol setup
local notation "N" => Setup.proposalRecoveryModel setup

variable (omission bad delivery : Set.Icc (0 : ℝ) 1)
  (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
    PMF (setup.CommitRecoveryValueChoice who key.1))

omit [Fintype Player] [Fintype setup.proposalRecoveryProtocol.History] in
/-- A recorded action came from an ACTUAL running prefix, which is exactly
the scope of the common source witness's normalized prescription. -/
theorem proposalRecovery_recorded_preparation_atom
    (profile : ∀ who, (N).BehavioralPolicy who)
    (prescribed : ∀ who (history : (E).History) (_running : ¬ (E).terminal history.state),
      profile who ((N).infoOf who history.trace) =
          (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
        delivery.property.1 delivery.property.2 values) who ((N).infoOf who history.trace))
    (owner : Player) (history : (E).History)
    (record : (N).InfoState owner × (E).Action owner)
    (member : record ∈ (N).ownPlay owner history.trace) :
    ∃ (prior : (E).History) (choice : (N).Choice owner ((N).infoOf owner prior.trace)),
      ¬ (E).terminal prior.state ∧ choice.val = some record.2 ∧
      (N).infoOf owner prior.trace = record.1 ∧
      (((profile owner record.1).map Subtype.val) (some record.2)).toReal =
        ((setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
        delivery.property.1 delivery.property.2 values) owner ((N).infoOf owner prior.trace)
            choice).toReal := by
  obtain ⟨prior, joint, legal, next, reached, _fuel, observed, chosen, _path⟩ :=
    (N).ownPlay_prefix owner history.trace member
  have permitted := (E).legalOption_of_legal legal owner
  rw [chosen] at permitted
  let choice : (N).Choice owner ((N).infoOf owner prior.trace) :=
    ⟨some record.2, ((N).menu_adequate owner prior.trace (some record.2)).mpr permitted⟩
  refine ⟨prior, choice, legal.1, rfl, observed, ?_⟩
  rw [← observed, prescribed owner prior legal.1]
  exact congrArg ENNReal.toReal (pmf_map_apply_of_injective
    ((setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
        delivery.property.1 delivery.property.2 values) owner ((N).infoOf owner prior.trace))
            Subtype.val_injective choice)

omit [Fintype Player] [Fintype setup.proposalRecoveryProtocol.History] in
/-- A prepared complete word has the product of the uniform response floor.
No atom belonging to another owner is given a lower bound. -/
theorem proposalRecoveryPrepared_word_lower
    (profile : ∀ who, (N).BehavioralPolicy who)
    (prescribed : ∀ who (history : (E).History) (_running : ¬ (E).terminal history.state),
      profile who ((N).infoOf who history.trace) =
          (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
        delivery.property.1 delivery.property.2 values) who ((N).infoOf who history.trace))
    (lower : ℝ) (lowerPositive : 0 < lower) (lowerBounded : lower ≤ 1)
    (lowerAt : ∀ (who : Player) (history : (E).History)
      (choice : (N).Choice who ((N).infoOf who history.trace)),
      ¬ ProposalRecoveryMove.GeneratedPreparationFailure choice.val →
        lower ≤ ((setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
        delivery.property.1 delivery.property.2 values) who ((N).infoOf who history.trace)
            choice).toReal)
    (length : Nat) (lengthBound : ∀ (history : (E).History) (who : Player),
      ((N).ownPlay who history.trace).length ≤ length)
    (owner : Player) (history : (E).History)
    (prepared : ∀ record ∈ (N).ownPlay owner history.trace,
      ¬ ProposalRecoveryMove.GeneratedPreparationFailure (some record.2)) :
    lower ^ length ≤ (N).ownPlayReachProbability (profile owner)
      ((N).ownPlay owner history.trace) := by
  let word := (N).ownPlay owner history.trace
  have atoms (record : (N).InfoState owner × (E).Action owner) (member : record ∈ word) :
      lower ≤ (((profile owner record.1).map Subtype.val) (some record.2)).toReal := by
    obtain ⟨prior, choice, _running, selected, _observed, atom⟩ :=
      setup.proposalRecovery_recorded_preparation_atom omission bad delivery values profile
          prescribed
        owner history record member
    rw [atom]
    apply lowerAt owner prior choice
    rw [selected]
    exact prepared record member
  have product := (N).ownPlayReachProbability_ofFn owner (profile owner) word.get
  rw [List.ofFn_get] at product
  have floorWord : lower ^ word.length ≤ (N).ownPlayReachProbability (profile owner) word := by
    rw [product]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => lower)
        (fun _ _ => lowerPositive.le)
        (fun index _ => atoms (word.get index) (List.get_mem _ _))
  exact (pow_le_pow_of_le_one lowerPositive.le lowerBounded (lengthBound history owner)).trans
    floorWord

omit [Fintype Player] [Fintype setup.proposalRecoveryProtocol.History] in
/-- One designated generated bad response bounds the entire original word;
all its other recorded atoms are at most one. -/
theorem proposalRecoveryGenerated_word_upper
    (profile : ∀ who, (N).BehavioralPolicy who)
    (prescribed : ∀ who (history : (E).History) (_running : ¬ (E).terminal history.state),
      profile who ((N).infoOf who history.trace) =
          (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
        delivery.property.1 delivery.property.2 values) who ((N).infoOf who history.trace))
    (owner : Player) (history : (E).History)
    (generated : setup.GeneratedPreparationHistory owner history) :
    (N).ownPlayReachProbability (profile owner) ((N).ownPlay owner history.trace) ≤ bad.val := by
  classical
  obtain ⟨record, member, badRecord⟩ := generated
  obtain ⟨prior, choice, _running, selected, _observed, atom⟩ :=
    setup.proposalRecovery_recorded_preparation_atom omission bad delivery values profile prescribed
      owner history record member
  have badChoice : ProposalRecoveryMove.GeneratedPreparationFailure choice.val := by
    rw [selected]
    exact badRecord
  have upper := setup.proposalRecoveryNormalizedTrembledProfile_generated_atom_le omission bad
    delivery values owner ((N).infoOf owner prior.trace) choice badChoice
  rw [← atom] at upper
  let word := (N).ownPlay owner history.trace
  obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
  change word.get index = record at equal
  let probability := fun index : Fin word.length =>
    (((profile owner (word.get index).1).map Subtype.val) (some (word.get index).2)).toReal
  have product := (N).ownPlayReachProbability_ofFn owner (profile owner) word.get
  rw [List.ofFn_get] at product
  rw [product]
  change (∏ index : Fin word.length, probability index) ≤ bad.val
  have rest : ∏ current ∈ Finset.univ.erase index, probability current ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => pmf_toReal_apply_le_one _ _)
  rw [← Finset.mul_prod_erase Finset.univ probability (Finset.mem_univ index)]
  have current : probability index ≤ bad.val := by
    dsimp only [probability]
    rw [equal]
    exact upper
  exact (mul_le_mul_of_nonneg_left rest ENNReal.toReal_nonneg).trans
    (by simpa only [mul_one] using current)

end Vegas.SourceProgram.Setup

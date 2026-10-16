/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryHonestPrescription
import GameTheory.Analysis.Protocol.RestrictionDomination
import GameTheory.Analysis.Protocol.RestrictionBeliefs

/-! # Original honest likelihood retained by the actual normalized source law

All source perturbation scales are fixed before completion. The constructed
honest pins leave a common positive fraction of each original honest action,
independently of the completion weights and of any off-honest continuation.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- At every genuine honest query the ACTUAL source perturbation retains the
same fixed fraction of every original raw honest action. This includes the
full original setup and chance history; no reach likelihood is an input. -/
theorem commitRecovery_normalized_honest_raw_lower
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (who : Player) (history : setup.intendedProtocol.History)
    (running : ¬ setup.intendedProtocol.terminal history.state)
    (action : Option (CommitRecoveryMove Player L)) :
    ((1 - omission) * (1 - bad) * (1 - floor)) *
      (((source who (setup.intendedModel.infoOf who history.trace)).map
        (fun choice => CommitRecoveryMove.lift choice.val)) action).toReal ≤
      ((((setup.commitRecoveryNormalizedTrembledProfile
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
            (setup.commitRecoveryHonestPoolPins finite wellFormed source) weights)) who
            (setup.commitRecoveryInformation wellFormed who
              (setup.intendedModel.infoOf who history.trace))).map Subtype.val) action).toReal := by
  classical
  let info := setup.commitRecoveryInformation wellFormed who
    (setup.intendedModel.infoOf who history.trace)
  let query := setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryNoMissInformation who info)
  have genuine : query ∈ setup.commitRecoveryDomainSites finite who := by
    let original := setup.commitRecoveryLiftHistory wellFormed history
    have stillRunning : ¬ setup.commitRecoveryProtocol.terminal original.state :=
      fun stopped => running
        ((setup.commitRecoveryLiftHistory_terminal wellFormed history).mp stopped)
    obtain ⟨replay, observed, staysRunning⟩ :=
      setup.commitRecoveryNoMissInformation_genuine_history who original
    have present := setup.commitRecoveryDomainSites_current finite who replay
      (staysRunning stillRunning)
    rw [setup.commitRecoveryErasedModel_infoOf, observed,
      setup.commitRecoveryInformation_observed] at present
    exact present
  let pool : setup.CommitRecoveryValuePool finite := ⟨who, ⟨query, genuine⟩⟩
  let values := setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
    (setup.commitRecoveryHonestPoolPins finite wellFormed source) weights who query
  let honest := (source who (setup.intendedModel.infoOf who history.trace)).map
    (fun choice => CommitRecoveryMove.lift choice.val)
  let ordinary : PMF (Option (CommitRecoveryMove Player L)) :=
    values.map (fun choice => choice.val.val)
  have law := setup.commitRecoveryPooledDomainLaw_honest_raw finite wellFormed source
    floor floorNonnegative floorBounded weights pool history rfl
  change ordinary = mix floor floorNonnegative floorBounded
    ((setup.commitRecoveryValueReference finite who query).map (fun choice => choice.val.val))
      honest at law
  have regular : (1 - floor) * (honest action).toReal ≤ (ordinary action).toReal := by
    rw [law, mix_apply_toReal]
    exact le_add_of_nonneg_left (mul_nonneg floorNonnegative ENNReal.toReal_nonneg)
  rw [commitRecoveryNormalizedTrembledProfile, setup.commitRecoveryNoMissErasedProfile_raw]
  change _ ≤ ((setup.commitRecoveryValueTremble who query omission omissionNonnegative
    omissionBounded bad badNonnegative badBounded values).map Subtype.val action).toReal
  let missed := (((PMF.pure (setup.commitRecoveryFailureChoice who query true)).map
    Subtype.val) action).toReal
  let failed := (((PMF.pure (setup.commitRecoveryFailureChoice who query false)).map
    Subtype.val) action).toReal
  have scaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left regular (sub_nonneg.mpr badBounded))
      (sub_nonneg.mpr omissionBounded)
  by_cases committing : query.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true
  · simp only [commitRecoveryValueTremble, committing, ↓reduceIte, mix_map, PMF.map_comp,
      Function.comp_def, mix_apply_toReal]
    change ((1 - omission) * (1 - bad) * (1 - floor)) * (honest action).toReal ≤
      omission * missed + (1 - omission) *
        (bad * failed + (1 - bad) * (ordinary action).toReal)
    calc
      _ = (1 - omission) * ((1 - bad) * ((1 - floor) * (honest action).toReal)) := by ring
      _ ≤ (1 - omission) * ((1 - bad) * (ordinary action).toReal) := scaled
      _ ≤ (1 - omission) * (bad * failed + (1 - bad) * (ordinary action).toReal) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (mul_nonneg badNonnegative ENNReal.toReal_nonneg))
          (sub_nonneg.mpr omissionBounded)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg omissionNonnegative ENNReal.toReal_nonneg)
  · have notCommit : query.1.1.1.elim false (ProtocolView.atCommit who setup.program) = false :=
      Bool.eq_false_iff.mpr committing
    simp only [commitRecoveryValueTremble, notCommit, Bool.false_eq_true, ↓reduceIte,
      mix_map, PMF.map_comp, Function.comp_def, mix_apply_toReal]
    change ((1 - omission) * (1 - bad) * (1 - floor)) * (honest action).toReal ≤
      omission * missed + (1 - omission) * (ordinary action).toReal
    calc
      _ = (1 - omission) * ((1 - bad) * ((1 - floor) * (honest action).toReal)) := by ring
      _ ≤ (1 - omission) * ((1 - bad) * (ordinary action).toReal) := scaled
      _ ≤ (1 - omission) * (ordinary action).toReal :=
        mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_left ENNReal.toReal_nonneg (sub_le_self 1 badNonnegative))
          (sub_nonneg.mpr omissionBounded)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg omissionNonnegative ENNReal.toReal_nonneg)


open Classical in
private theorem honest_choice_lower
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (choice : setup.commitRecoveryModel.Choice who
      ((setup.commitRecoveryRestriction wellFormed).information who site.1)) :
    ((1 - omission) * (1 - bad) * (1 - floor)) *
      (((source who site.1).map ((setup.commitRecoveryRestriction wellFormed).choice who site.1))
        choice).toReal ≤
      ((setup.commitRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.commitRecoveryHonestPoolPins finite wellFormed source) weights)) who
        ((setup.commitRecoveryRestriction wellFormed).information who site.1) choice).toReal := by
  classical
  obtain ⟨history, running, _⟩ := site.property
  have raw := setup.commitRecovery_normalized_honest_raw_lower finite wellFormed source
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded weights who history.1 running choice.val
  rw [history.property] at raw
  have read : ((source who site.1).map
        ((setup.commitRecoveryRestriction wellFormed).choice who site.1)).map Subtype.val =
      (source who site.1).map (fun choice => CommitRecoveryMove.lift choice.val) := by
    rw [PMF.map_comp]
    rfl
  rw [← read, pmf_map_apply_of_injective _ Subtype.val_injective,
    pmf_map_apply_of_injective _ Subtype.val_injective] at raw
  exact raw

open Classical in
private theorem honest_reference
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (omissionPositive : 0 < omission) :
    let fraction := (1 - omission) * (1 - bad) * (1 - floor)
    ∃ (reference : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
      (nonnegative : 0 ≤ 1 - fraction) (bounded : 1 - fraction ≤ 1),
      (setup.commitRecoveryRestriction wellFormed).PerturbsProfile source reference
        (setup.commitRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.commitRecoveryHonestPoolPins finite wellFormed source) weights))
        (1 - fraction) nonnegative bounded := by
  classical
  intro fraction
  let restriction := setup.commitRecoveryRestriction wellFormed
  let target := setup.commitRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.commitRecoveryHonestPoolPins finite wellFormed source) weights)
  have fractionNonnegative : 0 ≤ fraction := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr omissionBounded) (sub_nonneg.mpr badBounded))
    (sub_nonneg.mpr floorBounded)
  have atMost : fraction ≤ 1 - omission := by
    calc
      _ ≤ ((1 - omission) * 1) * (1 - floor) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self 1 badNonnegative)
            (sub_nonneg.mpr omissionBounded)) (sub_nonneg.mpr floorBounded)
      _ ≤ 1 - omission := by
        simpa only [mul_one] using
          mul_le_of_le_one_right (sub_nonneg.mpr omissionBounded)
            (sub_le_self 1 floorNonnegative)
  have fractionSmall : fraction < 1 := atMost.trans_lt (sub_lt_self 1 omissionPositive)
  have residualLaw (who : Player) (info : setup.commitRecoveryModel.InfoState who)
      (retained : restriction.Retained who info) :
      ∃ residual : PMF (setup.commitRecoveryModel.Choice who info),
        mix fraction fractionNonnegative fractionSmall.le
          (restriction.retainedLaw source who info retained) residual = target who info := by
    apply exists_mix_eq_of_le _ _ fraction fractionNonnegative fractionSmall
    intro choice
    obtain ⟨site, rfl⟩ := retained
    rw [restriction.retainedLaw_at]
    exact setup.honest_choice_lower finite wellFormed source
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded weights who site choice
  let reference : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who := fun who info =>
    if retained : restriction.Retained who info then (residualLaw who info retained).choose
    else target who info
  refine ⟨reference, sub_nonneg.mpr fractionSmall.le,
    sub_le_self 1 fractionNonnegative, ?_⟩
  intro who site
  have retained := restriction.retained_site who site
  have recipe := (residualLaw who (restriction.information who site.1) retained).choose_spec
  generalize chosen :
    (residualLaw who (restriction.information who site.1) retained).choose = residual at recipe
  rw [restriction.retainedLaw_at] at recipe
  have selected : reference who (restriction.information who site.1) =
      (residualLaw who (restriction.information who site.1) retained).choose := by
    dsimp only [reference]
    rw [dite_eq_left retained]
  rw [selected, chosen]
  exact recipe.symm.trans (mix_swap fraction fractionNonnegative fractionSmall.le _ _).symm

open Classical in
/-- The SAME initialized original source run retains a uniform fraction of
EVERY embedded honest history, including the original setup and all Nature
draws. The residual profile is constructed from the actual pinned source law;
no execution-likelihood comparison is assumed. -/
theorem commitRecovery_normalized_honest_run_lower
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (omissionPositive : 0 < omission) (fuel : Nat)
    (history : setup.commitRecoveryProtocol.History) :
    ((1 - omission) * (1 - bad) * (1 - floor)) ^
        (Fintype.card Player * fuel) *
      (((setup.intendedModel.runBehavioral source fuel).map
        (setup.commitRecoveryRestriction wellFormed).history) history).toReal ≤
      ((setup.commitRecoveryModel.runBehavioral
        (setup.commitRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.commitRecoveryHonestPoolPins finite wellFormed source) weights)) fuel)
          history).toReal := by
  classical
  obtain ⟨reference, nonnegative, bounded, perturbs⟩ :=
    setup.honest_reference finite wellFormed source
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded weights omissionPositive
  have lower := (setup.commitRecoveryRestriction wellFormed).perturbed_run_domination
    source reference _ _ nonnegative bounded perturbs fuel history
  simpa only [sub_sub_cancel] using lower

end Vegas.SourceProgram.Setup

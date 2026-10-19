/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryHonestPins
import Vegas.Game.ProposalRecoveryRestriction
import Vegas.Source.ProposalRecoveryOrdinaryCommit
import GameTheory.Analysis.Protocol.RestrictionDomination
import GameTheory.Analysis.Protocol.RestrictionBeliefs

/-! # Selected intended likelihood under caller-controlled proposal rates -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

omit [Fintype Player] [Fintype setup.proposalRecoveryProtocol.History] in
private theorem component_raw_mixture (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1)) :
    (setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded values).map Subtype.val =
      mix delivery deliveryNonnegative deliveryBounded
        (((setup.commitRecoveryValueTremble who key.1 omission omissionNonnegative omissionBounded
          bad badNonnegative badBounded values).map Subtype.val).map
            (Option.map (fun move => ProposalRecoveryMove.label move true)))
        (((setup.commitRecoveryValueTremble who key.1 omission omissionNonnegative omissionBounded
          bad badNonnegative badBounded values).map Subtype.val).map
            (Option.map ProposalRecoveryMove.ordinary)) := by
  let semantic := setup.commitRecoveryValueTremble who key.1
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded values
  let coin := mix delivery deliveryNonnegative deliveryBounded (PMF.pure true) (PMF.pure false)
  change (semantic.bind fun choice => (coin.map fun requested =>
    setup.proposalRecoveryComponentLabelChoice who key requested choice)).map Subtype.val = _
  rw [PMF.map_bind]
  have swap : (semantic.bind fun choice => (coin.map fun requested =>
      (setup.proposalRecoveryComponentLabelChoice who key requested choice).val)) =
      coin.bind (fun requested => semantic.map fun choice =>
        (setup.proposalRecoveryComponentLabelChoice who key requested choice).val) := by
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm semantic coin _
  simp only [PMF.map_comp, Function.comp_def]
  rw [swap, mix_bind, PMF.pure_bind, PMF.pure_bind]
  congr 2
  funext choice
  change choice.val.map (fun move => ProposalRecoveryMove.label move false) =
    choice.val.map ProposalRecoveryMove.ordinary
  simp only [ProposalRecoveryMove.label_false]

open Classical in
omit [Fintype Player] in
/-- The actual selected source law retains this explicit fraction of every
intended action. It depends on caller rates, not optimized pooled reaches. -/
theorem proposalRecovery_normalized_honest_raw_lower
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (who : Player) (history : setup.intendedProtocol.History)
    (running : ¬ setup.intendedProtocol.terminal history.state)
    (action : Option (ProposalRecoveryMove Player L)) :
    ((1 - omission) * (1 - bad) * (1 - floor) * (1 - delivery)) *
      (((source who (setup.intendedModel.infoOf who history.trace)).map
        (fun choice => ProposalRecoveryMove.lift choice.val)) action).toReal ≤
      ((((setup.proposalRecoveryNormalizedTrembledProfile
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          delivery deliveryNonnegative deliveryBounded
          (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
            (setup.proposalRecoveryHonestPoolPins wellFormed source) weights)) who
            (setup.proposalRecoveryInformation wellFormed who
              (setup.intendedModel.infoOf who history.trace))).map Subtype.val) action).toReal := by
  classical
  let info := setup.proposalRecoveryInformation wellFormed who
    (setup.intendedModel.infoOf who history.trace)
  let key := setup.proposalRecoveryQuery who info
  have genuine : key ∈ setup.proposalRecoveryDomainSites who := by
    let original := setup.proposalRecoveryIntendedLift wellFormed history
    have stillRunning : ¬ setup.proposalRecoveryProtocol.terminal original.state :=
      fun stopped => running
        ((setup.commitRecoveryLiftHistory_terminal wellFormed history).mp stopped)
    have present := setup.proposalRecoveryModel.mem_playedInformation
      (who := who) (history := original) stillRunning
    rw [setup.proposalRecoveryInformation_observed] at present
    exact Finset.mem_image.mpr ⟨info, present, rfl⟩
  let pool : setup.ProposalRecoveryValuePool := ⟨who, ⟨key, genuine⟩⟩
  let values := setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
    (setup.proposalRecoveryHonestPoolPins wellFormed source) weights who key
  let honest := (source who (setup.intendedModel.infoOf who history.trace)).map
    (fun choice => CommitRecoveryMove.lift choice.val)
  let ordinary := values.map (fun choice => choice.val.val)
  let semantic := (setup.commitRecoveryValueTremble who key.1
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded values).map
      Subtype.val
  have law := setup.proposalRecoveryPooledDomainLaw_honest_raw finite wellFormed source
    floor floorNonnegative floorBounded weights pool history rfl
  change ordinary = mix floor floorNonnegative floorBounded
    ((setup.commitRecoveryValueReference finite who key.1).map (fun choice => choice.val.val))
      honest at law
  have lower (raw : Option (CommitRecoveryMove Player L)) :
      ((1 - omission) * (1 - bad) * (1 - floor)) * (honest raw).toReal ≤
        (semantic raw).toReal := by
    have regular : (1 - floor) * (honest raw).toReal ≤ (ordinary raw).toReal := by
      rw [law, mix_apply_toReal]
      exact le_add_of_nonneg_left (mul_nonneg floorNonnegative ENNReal.toReal_nonneg)
    have scaled := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left regular (sub_nonneg.mpr badBounded))
        (sub_nonneg.mpr omissionBounded)
    have omitted := mul_nonneg omissionNonnegative
      (ENNReal.toReal_nonneg (a := ((PMF.pure
        (setup.commitRecoveryFailureChoice who key.1 true)).map Subtype.val) raw))
    have failed := mul_nonneg badNonnegative
      (ENNReal.toReal_nonneg (a := ((PMF.pure
        (setup.commitRecoveryFailureChoice who key.1 false)).map Subtype.val) raw))
    dsimp only [semantic]
    by_cases committing : key.1.1.1.1.elim false
        (ProtocolView.atCommit who setup.program) = true
    · simp only [commitRecoveryValueTremble, committing, ↓reduceIte, mix_map,
        PMF.map_comp, Function.comp_def, mix_apply_toReal]
      change _ ≤ omission * _ + (1 - omission) *
        (bad * _ + (1 - bad) * (ordinary raw).toReal)
      have failedScaled := mul_nonneg (sub_nonneg.mpr omissionBounded) failed
      nlinarith
    · have notCommit : key.1.1.1.1.elim false
          (ProtocolView.atCommit who setup.program) = false := Bool.eq_false_iff.mpr committing
      simp only [commitRecoveryValueTremble, notCommit, Bool.false_eq_true, ite_false,
        mix_map, PMF.map_comp, Function.comp_def, mix_apply_toReal]
      have small := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (ENNReal.toReal_nonneg (a := ordinary raw))
          (sub_le_self 1 badNonnegative)) (sub_nonneg.mpr omissionBounded)
      change _ ≤ omission * _ + (1 - omission) * (ordinary raw).toReal
      nlinarith
  have mapped := prob_bind_ge_mul honest semantic
    ((1 - omission) * (1 - bad) * (1 - floor)) lower
      (fun raw => PMF.pure (raw.map ProposalRecoveryMove.ordinary)) action
  change ((1 - omission) * (1 - bad) * (1 - floor)) *
    ((honest.map (Option.map ProposalRecoveryMove.ordinary)) action).toReal ≤
      ((semantic.map (Option.map ProposalRecoveryMove.ordinary)) action).toReal at mapped
  have intended : honest.map (Option.map ProposalRecoveryMove.ordinary) =
      (source who (setup.intendedModel.infoOf who history.trace)).map
        (fun choice => ProposalRecoveryMove.lift choice.val) := by
    rw [PMF.map_comp]
    rfl
  rw [intended] at mapped
  rw [proposalRecoveryNormalizedTrembledProfile, setup.proposalRecoveryPrescribedProfile_raw,
    setup.component_raw_mixture, mix_apply_toReal]
  have scaled := mul_le_mul_of_nonneg_left mapped (sub_nonneg.mpr deliveryBounded)
  have extra := mul_nonneg deliveryNonnegative
    (ENNReal.toReal_nonneg (a :=
      (semantic.map (Option.map (fun move => ProposalRecoveryMove.label move true))) action))
  change _ ≤ delivery *
    ((semantic.map (Option.map (fun move => ProposalRecoveryMove.label move true))) action).toReal +
      (1 - delivery) *
    ((semantic.map (Option.map ProposalRecoveryMove.ordinary)) action).toReal
  nlinarith

open Classical in
omit [Fintype Player] in
private theorem honest_choice_lower
    (finite : setup.program.FiniteBindingTypes)
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (choice : setup.proposalRecoveryModel.Choice who
      ((setup.proposalRecoveryRestriction wellFormed).information who site.1)) :
    ((1 - omission) * (1 - bad) * (1 - floor) * (1 - delivery)) *
      (((source who site.1).map ((setup.proposalRecoveryRestriction wellFormed).choice who site.1))
        choice).toReal ≤
      ((setup.proposalRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.proposalRecoveryHonestPoolPins wellFormed source) weights)) who
        ((setup.proposalRecoveryRestriction wellFormed).information who site.1) choice).toReal := by
  classical
  obtain ⟨history, running, _⟩ := site.property
  have raw := setup.proposalRecovery_normalized_honest_raw_lower finite wellFormed source
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
    floor floorNonnegative floorBounded weights who history.1 running choice.val
  rw [history.property] at raw
  have read : ((source who site.1).map
        ((setup.proposalRecoveryRestriction wellFormed).choice who site.1)).map Subtype.val =
      (source who site.1).map (fun choice => ProposalRecoveryMove.lift choice.val) := by
    rw [PMF.map_comp]
    rfl
  rw [← read, pmf_map_apply_of_injective _ Subtype.val_injective,
    pmf_map_apply_of_injective _ Subtype.val_injective] at raw
  exact raw

open Classical in
omit [Fintype Player] in
private theorem honest_reference
    (finite : setup.program.FiniteBindingTypes)
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (omissionPositive : 0 < omission) :
    let fraction := (1 - omission) * (1 - bad) * (1 - floor) * (1 - delivery)
    ∃ (reference : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
      (nonnegative : 0 ≤ 1 - fraction) (bounded : 1 - fraction ≤ 1),
      (setup.proposalRecoveryRestriction wellFormed).PerturbsProfile source reference
        (setup.proposalRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.proposalRecoveryHonestPoolPins wellFormed source) weights))
        (1 - fraction) nonnegative bounded := by
  classical
  intro fraction
  let restriction := setup.proposalRecoveryRestriction wellFormed
  let target := setup.proposalRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.proposalRecoveryHonestPoolPins wellFormed source) weights)
  have fractionNonnegative : 0 ≤ fraction := mul_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr omissionBounded)
      (sub_nonneg.mpr badBounded)) (sub_nonneg.mpr floorBounded))
      (sub_nonneg.mpr deliveryBounded)
  have badFactor : (1 - omission) * (1 - bad) ≤ 1 - omission :=
    mul_le_of_le_one_right (sub_nonneg.mpr omissionBounded) (sub_le_self 1 badNonnegative)
  have floorFactor : (1 - omission) * (1 - bad) * (1 - floor) ≤ 1 - omission :=
    (mul_le_of_le_one_right (mul_nonneg (sub_nonneg.mpr omissionBounded)
      (sub_nonneg.mpr badBounded)) (sub_le_self 1 floorNonnegative)).trans badFactor
  have atMost : fraction ≤ 1 - omission :=
    (mul_le_of_le_one_right
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr omissionBounded)
        (sub_nonneg.mpr badBounded)) (sub_nonneg.mpr floorBounded))
      (sub_le_self 1 deliveryNonnegative)).trans floorFactor
  have fractionSmall : fraction < 1 := atMost.trans_lt (sub_lt_self 1 omissionPositive)
  have residualLaw (who : Player) (info : setup.proposalRecoveryModel.InfoState who)
      (retained : restriction.Retained who info) :
      ∃ residual : PMF (setup.proposalRecoveryModel.Choice who info),
        mix fraction fractionNonnegative fractionSmall.le
          (restriction.retainedLaw source who info retained) residual = target who info := by
    apply exists_mix_eq_of_le _ _ fraction fractionNonnegative fractionSmall
    intro choice
    obtain ⟨site, rfl⟩ := retained
    rw [restriction.retainedLaw_at]
    exact setup.honest_choice_lower finite wellFormed source
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      floor floorNonnegative floorBounded weights who site choice
  let reference : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who := fun who info =>
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
theorem proposalRecovery_normalized_honest_run_lower
    (finite : setup.program.FiniteBindingTypes)
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (omissionPositive : 0 < omission) (fuel : Nat)
    (history : setup.proposalRecoveryProtocol.History) :
    ((1 - omission) * (1 - bad) * (1 - floor) * (1 - delivery)) ^
        (Fintype.card Player * fuel) *
      (((setup.intendedModel.runBehavioral source fuel).map
        (setup.proposalRecoveryRestriction wellFormed).history) history).toReal ≤
      ((setup.proposalRecoveryModel.runBehavioral
        (setup.proposalRecoveryNormalizedTrembledProfile
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        (setup.proposalRecoveryHonestPoolPins wellFormed source) weights)) fuel)
          history).toReal := by
  classical
  obtain ⟨reference, nonnegative, bounded, perturbs⟩ :=
    setup.honest_reference finite wellFormed source
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      floor floorNonnegative floorBounded weights omissionPositive
  have lower := (setup.proposalRecoveryRestriction wellFormed).perturbed_run_domination
    source reference _ _ nonnegative bounded perturbs fuel history
  simpa only [sub_sub_cancel] using lower

end Vegas.SourceProgram.Setup

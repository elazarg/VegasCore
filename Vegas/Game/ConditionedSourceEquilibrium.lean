module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedSourceBayes
public import Vegas.Game.IntendedPreservation

@[expose] public section

/-! # Restricting consistent intended assessments to an observed initial component -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)
  (supported : value ∈ (setup.initialLaw.map signal).support)
  (inside : ∀ who (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (history : setup.intendedModel.InformationHistory who site.1),
    setup.initialComponent signal value history.1.state)

/-- The conditional and original histories in a decision view determining the
component are in bijection, including views of zero equilibrium probability. -/
def conditionInitial_historyEquiv (who : Player)
    (site : (setup.conditionInitial signal value).intendedModel.InformationSite who) :
    (setup.conditionInitial signal value).intendedModel.InformationHistory who site.1 ≃
      setup.intendedModel.InformationHistory who site.1 :=
  Equiv.ofBijective (setup.conditionInitial_informationHistory signal value supported who site.1)
    ⟨setup.conditionInitial_informationHistory_injective signal value supported who site.1,
      setup.conditionInitial_informationHistory_surjective signal value supported who site.1
        (inside who site)⟩

/-- Restriction of an assessment, retaining its beliefs even at unreached decisions. -/
def conditionInitial_assessment (A : setup.intendedModel.BehavioralAssessment) :
    (setup.conditionInitial signal value).intendedModel.BehavioralAssessment where
  strategy who := setup.conditionInitial_policy signal value who (A.strategy who)
  belief who site :=
    (A.belief who (setup.conditionInitial_informationSite signal value supported site)).map
      (setup.conditionInitial_historyEquiv signal value supported inside who site).symm

theorem conditionInitial_assessment_belief_map (A : setup.intendedModel.BehavioralAssessment)
    (who : Player)
    (site : (setup.conditionInitial signal value).intendedModel.InformationSite who) :
    ((setup.conditionInitial_assessment signal value supported inside A).belief who site).map
        (setup.conditionInitial_informationHistory signal value supported who site.1) =
      A.belief who (setup.conditionInitial_informationSite signal value supported site) := by
  let e := setup.conditionInitial_historyEquiv signal value supported inside who site
  let belief := A.belief who (setup.conditionInitial_informationSite signal value supported site)
  change (belief.map e.symm).map e = belief
  simp [PMF.map_comp, PMF.map_id]

private theorem conditionInitial_assessment_belief_apply
    (A : setup.intendedModel.BehavioralAssessment)
    (who : Player) (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (history : (setup.conditionInitial signal value).intendedModel.InformationHistory who site.1) :
    (setup.conditionInitial_assessment signal value supported inside A).belief who site history =
      A.belief who (setup.conditionInitial_informationSite signal value supported site)
        (setup.conditionInitial_informationHistory signal value supported who site.1 history) := by
  let e := setup.conditionInitial_historyEquiv signal value supported inside who site
  let belief := A.belief who (setup.conditionInitial_informationSite signal value supported site)
  change (PMF.map e.symm belief) history = belief (e history)
  simpa only [Equiv.symm_apply_apply] using
    pmf_map_apply_of_injective belief e.symm.injective (e history)

variable [Finite Player]

/-- Restricting the same fully mixed approximating sequence at all sites
preserves Kreps–Wilson consistency of the assessment. -/
theorem conditionInitial_assessment_consistent (A : setup.intendedModel.BehavioralAssessment)
    (consistent : A.IsSequentiallyConsistent setup.intended_decision_antichain) :
    (setup.conditionInitial_assessment signal value supported inside A).IsSequentiallyConsistent
      (setup.conditionInitial signal value).intended_decision_antichain := by
  classical
  obtain ⟨sequence, regular, converges⟩ := consistent.exists_sequence
  refine ⟨fun n => setup.conditionInitial_assessment signal value supported inside (sequence n),
    ?_, ?_, ?_⟩
  · intro n
    obtain ⟨mixed, bayes⟩ := regular n
    constructor
    · intro who site choice
      apply (PMF.mem_support_iff _ _).mpr
      rw [show (setup.conditionInitial_assessment signal value supported inside
        (sequence n)).strategy who site.1 choice = _ from
        setup.conditionInitial_policy_apply signal value who _ _ choice]
      exact (PMF.mem_support_iff _ _).mp (mixed who
        (setup.conditionInitial_informationSite signal value supported site) _)
    · intro who site positive
      let globalSite := setup.conditionInitial_informationSite signal value supported site
      let restricted := setup.conditionInitial_assessment signal value supported inside (sequence n)
      have mass := setup.conditionInitial_informationMass signal value supported
        (sequence n).strategy
        site (inside who site)
      have globalPositive : 0 < setup.intendedModel.informationMass (sequence n).strategy who
          globalSite := by
        apply pos_iff_ne_zero.mpr
        intro zero
        rw [show setup.intendedModel.informationMass (sequence n).strategy who
          (setup.conditionInitial_informationSite signal value supported site) = 0 from zero,
          mul_zero] at mass
        exact positive.ne' mass
      have globalBayes := (InformationModel.BehavioralAssessment.isBayesConsistentAt_iff _
        (sequence n) who globalSite _ globalPositive).mp (bayes who globalSite globalPositive)
      apply (InformationModel.BehavioralAssessment.isBayesConsistentAt_iff _
        restricted who site _ positive).mpr
      let e := setup.conditionInitial_historyEquiv signal value supported inside who site
      have forward := setup.conditionInitial_bayesBelief signal value supported
        (sequence n).strategy
        site (inside who site)
        ((setup.conditionInitial signal value).intended_decision_antichain who site)
        (setup.intended_decision_antichain who globalSite) positive globalPositive
      rw [← globalBayes] at forward
      change (PMF.map e.symm ((sequence n).belief who globalSite)) = _
      rw [← forward]
      change PMF.map e.symm (PMF.map e _) = _
      simp only [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]
      rfl
  · intro who site choice
    simp only [conditionInitial_assessment, conditionInitial_policy_apply]
    exact
      converges.1 who (setup.conditionInitial_informationSite signal value supported site)
        (setup.conditionInitial_choiceEquiv signal value who site.1 choice)
  · intro who site history
    simp only [conditionInitial_assessment_belief_apply]
    exact
      converges.2 who (setup.conditionInitial_informationSite signal value supported site)
        (setup.conditionInitial_informationHistory signal value supported who site.1 history)

end Vegas.SourceProgram.Setup

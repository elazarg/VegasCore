/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstRationality
import Interaction.ReactiveFiniteAssessment
import GameTheory.Math.Probability.Convergence
import GameTheory.Protocol.FiniteInformation

/-! # Uniformly vanishing nongenuine first late packets

The actual bounded game has finitely many first late information classes,
including every private raw submission alias. Sequential rationality makes
nongenuine packets have zero limiting probability at each such class. One
vanishing bound therefore controls all their probabilities along the actual
consistency sequence. Weighted contamination obeys the same relative bound
even when the protected-silence prefix weights vanish.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstTremble

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeAliceFirstDecision LateOpeningRuntimeAliceFirstResponse

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Actual information classes containing a first late callback after no
earlier Alice transmission. The complete private recall remains in the class. -/
def FirstOpeningSite :=
  {site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice //
    ∃ (decision : DecisionHistory weight nonnegative)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1), history.1.state = some ⟨22, some alice, decision.execution⟩}

instance finiteFirstOpeningSite : Finite (FirstOpeningSite weight nonnegative) := by
  unfold FirstOpeningSite
  infer_instance

def siteDecision (site : FirstOpeningSite weight nonnegative) :
    DecisionHistory weight nonnegative := site.2.choose

def siteRepresentative (site : FirstOpeningSite weight nonnegative) :
    (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1.1 :=
  site.2.choose_spec.choose

theorem site_current (site : FirstOpeningSite weight nonnegative) :
    (siteRepresentative weight nonnegative site).1.state =
      some ⟨22, some alice, (siteDecision weight nonnegative site).execution⟩ :=
  site.2.choose_spec.choose_spec

/-- The event does not depend on which actual representative was selected. -/
theorem permitted_of_representative (site : FirstOpeningSite weight nonnegative)
    (decision : DecisionHistory weight nonnegative)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1.1)
    (current : history.1.state = some ⟨22, some alice, decision.execution⟩)
    (response : app.Action) :
    PermittedResponse weight nonnegative (siteDecision weight nonnegative site) response ↔
      PermittedResponse weight nonnegative decision response := by
  let recovered := decisionOfInformation weight nonnegative site.1
    (siteRepresentative weight nonnegative site) (siteDecision weight nonnegative site)
      (site_current weight nonnegative site) history
  have facts := decisionOfInformation_spec weight nonnegative site.1
    (siteRepresentative weight nonnegative site) (siteDecision weight nonnegative site)
      (site_current weight nonnegative site) history
  have sameExecution : recovered.execution = decision.execution :=
    congrArg ReactiveApplication.Control.execution (Option.some.inj (facts.1.symm.trans current))
  have sameBit : recovered.bit = decision.bit := by
    have equality := recovered.bound
    rw [sameExecution, decision.bound] at equality
    simpa using equality.symm
  have transport := permitted_of_information weight nonnegative site.1
    (siteRepresentative weight nonnegative site) (siteDecision weight nonnegative site)
      (site_current weight nonnegative site) history response
  refine transport.symm.trans ?_
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      change (_ = (LateOpeningRuntimeLatePrefix.openingMessage recovered.bit).payload) ↔
        (_ = (LateOpeningRuntimeLatePrefix.openingMessage decision.bit).payload)
      rw [sameExecution, sameBit]

def nongenuineProbability
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : FirstOpeningSite weight nonnegative) : ℝ :=
  (((profile alice site.1.1).map (fun choice => choice.1.getD ⟨none⟩)).toOuterMeasure
    {response | ¬ PermittedResponse weight nonnegative
      (siteDecision weight nonnegative site) response}).toReal

theorem nongenuineProbability_of_representative
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : FirstOpeningSite weight nonnegative)
    (decision : DecisionHistory weight nonnegative)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1.1)
    (current : history.1.state = some ⟨22, some alice, decision.execution⟩) :
    nongenuineProbability weight nonnegative profile site =
      ((responseLaw weight nonnegative site.1 (profile alice site.1.1)).toOuterMeasure
        {response | ¬ PermittedResponse weight nonnegative decision response}).toReal := by
  unfold nongenuineProbability responseLaw
  congr 2
  ext response
  exact not_congr (permitted_of_representative weight nonnegative site decision history
    current response)

theorem nongenuineProbability_nonnegative
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : FirstOpeningSite weight nonnegative) :
    0 ≤ nongenuineProbability weight nonnegative profile site := ENNReal.toReal_nonneg

theorem nongenuineProbability_tendsto
    {sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    {target : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    (converges : ∀ site :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (site : FirstOpeningSite weight nonnegative) :
    Tendsto (fun n => nongenuineProbability weight nonnegative (sequence n) site) atTop
      (nhds (nongenuineProbability weight nonnegative target site)) := by
  classical
  have decoded := (converges site.1).map (fun choice => choice.1.getD ⟨none⟩)
  let event : Set app.Action := {response | ¬ PermittedResponse weight nonnegative
    (siteDecision weight nonnegative site) response}
  let indicator : app.Action → ℝ := fun response =>
    @ite ℝ (response ∈ event) (Classical.propDecidable _) 1 0
  have indicatorBound : ∀ response : app.Action, |indicator response| ≤ 1 := by
    intro response
    dsimp only [indicator]
    split_ifs <;> norm_num
  have limit := decoded.expect_of_bounded indicator indicatorBound
  unfold nongenuineProbability
  simp_rw [← expect_indicator]
  exact limit

theorem exists_uniform_nongenuine_bound
    {sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    {target : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    (converges : ∀ site :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (genuineOrSilent : ∀ site : FirstOpeningSite weight nonnegative,
      nongenuineProbability weight nonnegative target site = 0) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : FirstOpeningSite weight nonnegative),
        nongenuineProbability weight nonnegative (sequence n) site ≤ error n := by
  classical
  let _ := Fintype.ofFinite (FirstOpeningSite weight nonnegative)
  let error : ℕ → ℝ := fun n => ∑ site : FirstOpeningSite weight nonnegative,
    nongenuineProbability weight nonnegative (sequence n) site
  refine ⟨error, ?_, ?_, ?_⟩
  · intro n
    exact Finset.sum_nonneg fun site _ => nongenuineProbability_nonnegative _ _ _ _
  · have limit := tendsto_finsetSum Finset.univ
      (fun (site : FirstOpeningSite weight nonnegative) _ =>
        nongenuineProbability_tendsto weight nonnegative converges site)
    simpa only [genuineOrSilent, Finset.sum_const_zero] using limit
  · intro n site
    exact Finset.single_le_sum
      (fun other _ => nongenuineProbability_nonnegative weight nonnegative (sequence n) other)
        (Finset.mem_univ site)

/-- Nongenuine first packets remain negligible relative to their own prefix
weights; no lower bound on those weights is required. -/
theorem weighted_nongenuine_bound {Root : Type} [Fintype Root]
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : Root → FirstOpeningSite weight nonnegative) (prefixWeight : Root → ℝ)
    (prefixNonnegative : ∀ root, 0 ≤ prefixWeight root) (error : ℝ)
    (bound : ∀ root, nongenuineProbability weight nonnegative profile (site root) ≤ error) :
    ∑ root, prefixWeight root * nongenuineProbability weight nonnegative profile (site root) ≤
      error * ∑ root, prefixWeight root := by
  calc
    _ ≤ ∑ root, prefixWeight root * error := Finset.sum_le_sum fun root _ =>
      mul_le_mul_of_nonneg_left (bound root) (prefixNonnegative root)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem weighted_nongenuine_ratio_tendsto {Root : Type} [Fintype Root]
    (sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : ℕ → Root → FirstOpeningSite weight nonnegative)
    (prefixWeight : ℕ → Root → ℝ)
    (prefixNonnegative : ∀ n root, 0 ≤ prefixWeight n root)
    (prefixPositive : ∀ n, 0 < ∑ root, prefixWeight n root) (error : ℕ → ℝ)
    (vanishes : Tendsto error atTop (nhds 0))
    (bound : ∀ n (actual : FirstOpeningSite weight nonnegative),
      nongenuineProbability weight nonnegative (sequence n) actual ≤ error n) :
    Tendsto (fun n => (∑ root, prefixWeight n root *
        nongenuineProbability weight nonnegative (sequence n) (site n root)) /
      (∑ root, prefixWeight n root)) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (Finset.sum_nonneg fun root _ => mul_nonneg
      (prefixNonnegative n root) (nongenuineProbability_nonnegative _ _ _ _))
      (prefixPositive n).le
  · intro n
    apply (div_le_iff₀ (prefixPositive n)).mpr
    exact weighted_nongenuine_bound weight nonnegative (sequence n) (site n)
      (prefixWeight n) (prefixNonnegative n) (error n) (fun root => bound n (site n root))
  · exact vanishes

theorem sequentially_rational_uniform_nongenuine_bound
    (reward forfeit : ℝ) (deposit : Player → ℝ) (positive : 0 < weight)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : FirstOpeningSite weight nonnegative),
        nongenuineProbability weight nonnegative (sequence n).strategy site ≤ error n := by
  apply exists_uniform_nongenuine_bound weight nonnegative
    (fun site => converges.strategy alice site)
  intro site
  exact LateOpeningRuntimeAliceFirstRationality.sequentially_rational_nongenuine_packet_zero
    weight nonnegative site.1 (siteRepresentative weight nonnegative site)
      (siteDecision weight nonnegative site) (site_current weight nonnegative site)
        reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
          marginPositive assessment rational

theorem equilibrium_consistency_nongenuine_bound
    (reward forfeit : ℝ) (deposit : Player → ℝ) (positive : 0 < weight)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ∃ sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed ∧
        InformationModel.BehavioralAssessment.IsBayesConsistent
          (LateOpeningRuntimeNash.model weight nonnegative) (sequence n)
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment ∧
      ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
        ∀ n (site : FirstOpeningSite weight nonnegative),
          nongenuineProbability weight nonnegative (sequence n).strategy site ≤ error n := by
  obtain ⟨sequence, admissible, converges⟩ := equilibrium.2
  refine ⟨sequence, admissible, converges, ?_⟩
  exact sequentially_rational_uniform_nongenuine_bound weight nonnegative reward forfeit deposit
    positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive
      assessment equilibrium.1 sequence converges

end Vegas.Examples.LateOpeningRuntimeAliceFirstTremble

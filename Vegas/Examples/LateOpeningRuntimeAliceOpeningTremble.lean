/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality
import Interaction.ReactiveFiniteAssessment
import GameTheory.Math.Probability.Convergence
import GameTheory.Protocol.FiniteInformation

/-! # Uniformly vanishing failure to send the final genuine opening

The bounded native game has finitely many final Alice information classes
after earlier silence. Every private raw representation remains present.
Sequential rationality forces a genuine opening at each class, so one
vanishing bound controls silence and nongenuine packets along any convergent
assessment sequence. The sequence need not itself be sequentially rational.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceOpeningTremble

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeAliceEmptyDecision LateOpeningRuntimeAliceOpeningRationality

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def EmptyOpeningSite :=
  {site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice //
    ∃ (decision : DecisionHistory weight nonnegative)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1), history.1.state = some ⟨18, some alice, decision.execution⟩}

instance finiteEmptyOpeningSite : Finite (EmptyOpeningSite weight nonnegative) := by
  unfold EmptyOpeningSite
  infer_instance

def siteDecision (site : EmptyOpeningSite weight nonnegative) :
    DecisionHistory weight nonnegative := site.2.choose

def siteRepresentative (site : EmptyOpeningSite weight nonnegative) :
    (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1.1 :=
  site.2.choose_spec.choose

theorem site_current (site : EmptyOpeningSite weight nonnegative) :
    (siteRepresentative weight nonnegative site).1.state =
      some ⟨18, some alice, (siteDecision weight nonnegative site).execution⟩ :=
  site.2.choose_spec.choose_spec

theorem genuine_of_representative (site : EmptyOpeningSite weight nonnegative)
    (decision : DecisionHistory weight nonnegative)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1.1)
    (current : history.1.state = some ⟨18, some alice, decision.execution⟩)
    (response : app.Action) :
    GenuineResponse weight nonnegative (siteDecision weight nonnegative site) response ↔
      GenuineResponse weight nonnegative decision response := by
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
  have transport := genuine_of_information weight nonnegative site.1
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
    (site : EmptyOpeningSite weight nonnegative) : ℝ :=
  (((profile alice site.1.1).map (fun choice => choice.1.getD ⟨none⟩)).toOuterMeasure
    {response | ¬ GenuineResponse weight nonnegative
      (siteDecision weight nonnegative site) response}).toReal

theorem nongenuineProbability_of_representative
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : EmptyOpeningSite weight nonnegative)
    (decision : DecisionHistory weight nonnegative)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1.1)
    (current : history.1.state = some ⟨18, some alice, decision.execution⟩) :
    nongenuineProbability weight nonnegative profile site =
      ((responseLaw weight nonnegative site.1 (profile alice)).toOuterMeasure
        {response | ¬ GenuineResponse weight nonnegative decision response}).toReal := by
  unfold nongenuineProbability responseLaw
  congr 2
  ext response
  exact not_congr (genuine_of_representative weight nonnegative site decision history
    current response)

theorem nongenuineProbability_nonnegative
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : EmptyOpeningSite weight nonnegative) :
    0 ≤ nongenuineProbability weight nonnegative profile site := ENNReal.toReal_nonneg

theorem nongenuineProbability_tendsto
    {sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    {target : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    (converges : ∀ site :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (site : EmptyOpeningSite weight nonnegative) :
    Tendsto (fun n => nongenuineProbability weight nonnegative (sequence n) site) atTop
      (nhds (nongenuineProbability weight nonnegative target site)) := by
  classical
  have decoded := (converges site.1).map (fun choice => choice.1.getD ⟨none⟩)
  let event : Set app.Action := {response | ¬ GenuineResponse weight nonnegative
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
    (genuine : ∀ site : EmptyOpeningSite weight nonnegative,
      nongenuineProbability weight nonnegative target site = 0) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : EmptyOpeningSite weight nonnegative),
        nongenuineProbability weight nonnegative (sequence n) site ≤ error n := by
  classical
  let _ := Fintype.ofFinite (EmptyOpeningSite weight nonnegative)
  let error : ℕ → ℝ := fun n => ∑ site : EmptyOpeningSite weight nonnegative,
    nongenuineProbability weight nonnegative (sequence n) site
  refine ⟨error, ?_, ?_, ?_⟩
  · intro n
    exact Finset.sum_nonneg fun site _ => nongenuineProbability_nonnegative _ _ _ _
  · have limit := tendsto_finsetSum Finset.univ fun site _ =>
      nongenuineProbability_tendsto weight nonnegative converges site
    simpa only [genuine, Finset.sum_const_zero] using limit
  · intro n site
    exact Finset.single_le_sum
      (fun other _ => nongenuineProbability_nonnegative weight nonnegative (sequence n) other)
        (Finset.mem_univ site)

theorem sequentially_rational_uniform_nongenuine_bound
    (reward forfeit : ℝ) (deposit : Player → ℝ) (positive : 0 < weight)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : EmptyOpeningSite weight nonnegative),
        nongenuineProbability weight nonnegative (sequence n).strategy site ≤ error n := by
  apply exists_uniform_nongenuine_bound weight nonnegative
    (fun site => converges.strategy alice site)
  intro site
  exact sequentially_rational_nongenuine_response_zero weight nonnegative site.1
    (siteRepresentative weight nonnegative site) (siteDecision weight nonnegative site)
      (site_current weight nonnegative site) reward forfeit deposit positive rewardNonnegative
        forfeitNonnegative depositNonnegative marginPositive assessment rational

end Vegas.Examples.LateOpeningRuntimeAliceOpeningTremble

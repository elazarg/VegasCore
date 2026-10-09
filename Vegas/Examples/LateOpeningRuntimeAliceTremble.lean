/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceDecision
import Vegas.Examples.LateOpeningRuntimeAliceRationality
import Interaction.ReactiveFiniteAssessment
import GameTheory.Math.Probability.Convergence
import GameTheory.Protocol.FiniteInformation

/-! # Uniformly vanishing retries at actual pending-opening decisions

There are finitely many legal native information classes, even though their
views retain private raw submission syntax. If a limiting strategy is silent
at every class containing a genuine pending first opening, every convergent
strategy sequence has one vanishing bound on its retry probabilities there.
Weighted sums retain that bound relative to their own total prefix weight;
the prefix weights need not have a positive limit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceTremble

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeAliceDecision

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- A real native information class containing the operational pending-opening
interface. Its representative retains its complete private action history. -/
def PendingOpeningSite :=
  {site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice //
    ∃ (decision : DecisionHistory weight nonnegative)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1), history.1.state = some ⟨18, some alice, decision.execution⟩}

instance finitePendingOpeningSite : Finite (PendingOpeningSite weight nonnegative) := by
  unfold PendingOpeningSite
  infer_instance

def emissionProbability
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice) : ℝ :=
  (((profile alice site.1).map (fun choice => choice.1.getD ⟨none⟩)).toOuterMeasure
    {response | response.transmission.isSome}).toReal

theorem emissionProbability_nonnegative
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice) :
    0 ≤ emissionProbability weight nonnegative profile site := ENNReal.toReal_nonneg

theorem emissionProbability_tendsto
    {sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    {target : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    (converges : ∀ site :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice) :
    Tendsto (fun n => emissionProbability weight nonnegative (sequence n) site) atTop
      (nhds (emissionProbability weight nonnegative target site)) := by
  classical
  have decoded := (converges site).map (fun choice => choice.1.getD ⟨none⟩)
  let event : Set app.Action := {response | response.transmission.isSome}
  let indicator : app.Action → ℝ := fun response =>
    @ite ℝ (response ∈ event) (Classical.propDecidable _) 1 0
  have indicatorBound : ∀ response : app.Action,
      |indicator response| ≤ 1 := by
    intro response
    dsimp only [indicator]
    split_ifs <;> norm_num
  have limit := decoded.expect_of_bounded indicator indicatorBound
  unfold emissionProbability
  simp_rw [← expect_indicator]
  exact limit

/-- The uniform bound holds for any globally convergent strategy sequence,
including the particular sequence that witnesses sequential consistency. -/
theorem exists_uniform_retry_bound
    {sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    {target : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who}
    (converges : ∀ site :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (quiet : ∀ site : PendingOpeningSite weight nonnegative,
      emissionProbability weight nonnegative target site.1 = 0) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : PendingOpeningSite weight nonnegative),
        emissionProbability weight nonnegative (sequence n) site.1 ≤ error n := by
  classical
  let _ := Fintype.ofFinite (PendingOpeningSite weight nonnegative)
  let error : ℕ → ℝ := fun n => ∑ site : PendingOpeningSite weight nonnegative,
    emissionProbability weight nonnegative (sequence n) site.1
  refine ⟨error, ?_, ?_, ?_⟩
  · intro n
    exact Finset.sum_nonneg fun site _ => emissionProbability_nonnegative _ _ _ _
  · have limit := tendsto_finsetSum Finset.univ
      (fun (site : PendingOpeningSite weight nonnegative) _ =>
        emissionProbability_tendsto weight nonnegative converges site.1)
    simpa only [quiet, Finset.sum_const_zero] using limit
  · intro n site
    exact Finset.single_le_sum
      (fun other _ => emissionProbability_nonnegative _ _ _ _) (Finset.mem_univ site)

/-- Arbitrary nonnegative prefix weights inherit the relative retry bound.
Their total mass may tend to zero arbitrarily quickly. -/
theorem weighted_retry_bound {Root : Type} [Fintype Root]
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : Root → PendingOpeningSite weight nonnegative) (prefixWeight : Root → ℝ)
    (prefixNonnegative : ∀ root, 0 ≤ prefixWeight root) (error : ℝ)
    (bound : ∀ root, emissionProbability weight nonnegative profile (site root).1 ≤ error) :
    ∑ root, prefixWeight root *
        emissionProbability weight nonnegative profile (site root).1 ≤
      error * ∑ root, prefixWeight root := by
  calc
    _ ≤ ∑ root, prefixWeight root * error := Finset.sum_le_sum fun root _ =>
      mul_le_mul_of_nonneg_left (bound root) (prefixNonnegative root)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- The ratio estimate remains valid when both the private alias weights and
their associated native information classes vary along the sequence. -/
theorem weighted_retry_ratio_tendsto {Root : Type} [Fintype Root]
    (sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (site : ℕ → Root → PendingOpeningSite weight nonnegative)
    (prefixWeight : ℕ → Root → ℝ)
    (prefixNonnegative : ∀ n root, 0 ≤ prefixWeight n root)
    (prefixPositive : ∀ n, 0 < ∑ root, prefixWeight n root) (error : ℕ → ℝ)
    (vanishes : Tendsto error atTop (nhds 0))
    (bound : ∀ n (actual : PendingOpeningSite weight nonnegative),
      emissionProbability weight nonnegative (sequence n) actual.1 ≤ error n) :
    Tendsto (fun n => (∑ root, prefixWeight n root *
        emissionProbability weight nonnegative (sequence n) (site n root).1) /
      (∑ root, prefixWeight n root)) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (Finset.sum_nonneg fun root _ => mul_nonneg
      (prefixNonnegative n root) (emissionProbability_nonnegative _ _ _ _))
      (prefixPositive n).le
  · intro n
    apply (div_le_iff₀ (prefixPositive n)).mpr
    exact weighted_retry_bound weight nonnegative (sequence n) (site n)
      (prefixWeight n) (prefixNonnegative n) (error n) (fun root => bound n (site n root))
  · exact vanishes

/-- The native sequential-rationality theorem supplies silence at every
pending-opening class, so no local quiet law is assumed in this conclusion. -/
theorem sequentially_rational_uniform_retry_bound
    (reward forfeit : ℝ) (deposit : Player → ℝ) (positive : 0 < weight)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
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
      ∀ n (site : PendingOpeningSite weight nonnegative),
        emissionProbability weight nonnegative (sequence n).strategy site.1 ≤ error n := by
  apply exists_uniform_retry_bound weight nonnegative
    (fun site => converges.strategy alice site)
  intro site
  obtain ⟨decision, history, current⟩ := site.2
  exact LateOpeningRuntimeAliceRationality.sequentially_rational_second_packet_zero
    weight nonnegative site.1 history decision current reward forfeit deposit positive
      rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment rational

/-- A native sequential equilibrium admits a fully mixed Bayes witness with
the same uniform retry bound. This is the actual consistency sequence, not a
separately selected relative tremble rate. -/
theorem equilibrium_consistency_retry_bound
    (reward forfeit : ℝ) (deposit : Player → ℝ) (positive : 0 < weight)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
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
        ∀ n (site : PendingOpeningSite weight nonnegative),
          emissionProbability weight nonnegative (sequence n).strategy site.1 ≤ error n := by
  obtain ⟨sequence, admissible, converges⟩ := equilibrium.2
  refine ⟨sequence, admissible, converges, ?_⟩
  exact sequentially_rational_uniform_retry_bound weight nonnegative reward forfeit deposit
    positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive
      assessment equilibrium.1 sequence converges

end Vegas.Examples.LateOpeningRuntimeAliceTremble

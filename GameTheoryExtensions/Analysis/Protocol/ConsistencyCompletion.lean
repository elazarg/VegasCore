/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.Perturbation
import GameTheory.Math.Probability.Convergence
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheory.Protocol.DecisionPlan
import GameTheory.Protocol.FiniteInformation
import Mathlib.Analysis.SpecificLimits.Basic
import GameTheory.Analysis.Protocol.AssessmentCompactness

/-! # Consistent belief completions with tight laws

Countably many decision sites and uniformly tight belief laws admit one common
subsequence. Strategy convergence survives this extraction, so a completed
assessment has exactly the prescribed profile. Finite laws supply tightness
automatically. No continuation optimality or compatibility with a
prescribed belief system follows from compactness.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type} {E : ExecutionProtocol ι} {M : InformationModel E}
  [Fintype ι]

/-- A single subsequence completes the given strategy limit, simultaneously at
every site. The original sequence need not itself have convergent beliefs. -/
theorem BehavioralAssessment.exists_consistent_completion_subsequence
    [∀ who, Countable (M.InformationSite who)]
    (antichain : M.DecisionInformationAntichain)
    (profile : ∀ who, M.BehavioralPolicy who)
    (sequence : ℕ → M.BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (beliefTight : ∀ who site, UniformlyTight (fun n => (sequence n).belief who site))
    (strategies : ∀ who (site : M.InformationSite who),
      PMFConvergesPointwise (fun n => (sequence n).strategy who site.1)
        (profile who site.1)) :
    ∃ assessment : M.BehavioralAssessment, assessment.strategy = profile ∧
      ∃ index : ℕ → ℕ, StrictMono index ∧
        BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) assessment ∧
        assessment.IsSequentiallyConsistent antichain := by
  obtain ⟨beliefs, index, increasing, converges⟩ :=
    exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
      (fun n (site : Σ who, M.InformationSite who) => (sequence n).belief site.1 site.2)
      (fun site => beliefTight site.1 site.2)
  let assessment : M.BehavioralAssessment :=
    ⟨profile, fun who site => beliefs ⟨who, site⟩⟩
  have limit : BehavioralAssessmentConvergesPointwise
      (fun n => sequence (index n)) assessment :=
    ⟨fun who site => (strategies who site).subseq increasing,
      fun who site => converges ⟨who, site⟩⟩
  exact ⟨assessment, rfl, index, increasing, limit,
    ⟨fun n => sequence (index n), fun n => ⟨mixed (index n), bayes (index n)⟩, limit⟩⟩

/-- A varying sequence of fully mixed Bayes assessments has one common
subsequence converging in both strategies and beliefs. Unlike completion of a
fixed profile, this permits optimal continuation policies to be selected along
the sequence before taking the limit. Optimality itself remains a separate
obligation. -/
theorem BehavioralAssessment.exists_sequentiallyConsistent_subsequence
    [∀ who, Countable (M.InformationSite who)]
    (antichain : M.DecisionInformationAntichain)
    (sequence : ℕ → M.BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (strategyTight : ∀ who (site : M.InformationSite who),
      UniformlyTight (fun n => (sequence n).strategy who site.1))
    (beliefTight : ∀ who site, UniformlyTight (fun n => (sequence n).belief who site)) :
    ∃ assessment : M.BehavioralAssessment, ∃ index : ℕ → ℕ,
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) assessment ∧
      assessment.IsSequentiallyConsistent antichain := by
  obtain ⟨assessment, index, increasing, converges⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight
      sequence strategyTight beliefTight
  exact ⟨assessment, index, increasing, converges,
    converges.isSequentiallyConsistent antichain (fun n => mixed (index n))
      (fun n => bayes (index n))⟩

/-- Compactness retains any already established convergence of projected
Bayes beliefs. The projection law is an explicit premise: arbitrary consistent
completion alone supplies no compatibility with another game's beliefs. -/
theorem BehavioralAssessment.exists_consistent_completion_preserving
    [∀ who, Countable (M.InformationSite who)]
    (antichain : M.DecisionInformationAntichain)
    (profile : ∀ who, M.BehavioralPolicy who)
    (sequence : ℕ → M.BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (beliefTight : ∀ who site, UniformlyTight (fun n => (sequence n).belief who site))
    (strategies : ∀ who (site : M.InformationSite who),
      PMFConvergesPointwise (fun n => (sequence n).strategy who site.1)
        (profile who site.1))
    {Observation : (who : ι) → M.InformationSite who → Type*}
    (project : ∀ who site, M.InformationHistory who site.1 → Observation who site)
    (limit : ∀ who site, PMF (Observation who site))
    (projected : ∀ who site, PMFConvergesPointwise
      (fun n => ((sequence n).belief who site).map (project who site)) (limit who site)) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.strategy = profile ∧ assessment.IsSequentiallyConsistent antichain ∧
      ∀ who site, (assessment.belief who site).map (project who site) = limit who site := by
  obtain ⟨assessment, strategy, index, increasing, converges, consistent⟩ :=
    BehavioralAssessment.exists_consistent_completion_subsequence antichain profile sequence
      mixed bayes beliefTight strategies
  refine ⟨assessment, strategy, consistent, fun who site => ?_⟩
  exact ((converges.belief who site).map (project who site)).unique
    ((projected who site).subseq increasing)

/-- In a finite protocol admitting a fully mixed reference profile, every
profile has some sequentially consistent beliefs. This is consistency
existence, not equilibrium existence. -/
theorem BehavioralAssessment.exists_consistent_completion
    [∀ who, Finite (M.InformationSite who)]
    [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    (antichain : M.DecisionInformationAntichain)
    (profile : ∀ who, M.BehavioralPolicy who) :
    ∃ assessment : M.BehavioralAssessment, assessment.strategy = profile ∧
      assessment.IsSequentiallyConsistent antichain := by
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : ℕ) : 0 < weight n := by dsimp [weight]; positivity
  have atMostOne (n : ℕ) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let sequence (n : ℕ) :=
    InformationModel.bayesAssessment _ (reference.perturb profile (weight n) (positive n).le
        (atMostOne n)).strategy (reference.perturb_fullyMixed mixed profile (weight n) (positive
            n).le
        (atMostOne n) (positive n)) antichain
  obtain ⟨assessment, strategy, index, _increasing, _limit, consistent⟩ :=
    BehavioralAssessment.exists_consistent_completion_subsequence antichain profile sequence
      (fun n => InformationModel.bayesAssessment_isFullyMixed _ _ _ _)
      (fun n => InformationModel.bayesAssessment_isBayesConsistent _ _ _ _)
      (fun _ _ => uniformlyTight_of_finite _)
      (fun who site => reference.perturb_strategy_converges profile weight
        (fun n => (positive n).le) atMostOne vanishes who site.1)
  exact ⟨assessment, strategy, consistent⟩

end GameTheory.Protocol.InformationModel

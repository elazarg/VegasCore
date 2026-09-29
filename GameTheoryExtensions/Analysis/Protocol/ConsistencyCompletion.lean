/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.Perturbation
import GameTheoryExtensions.Math.Probability.Convergence
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Protocol.FiniteInformation
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Consistent belief completions in finite protocols

Extract one common subsequence of Bayes beliefs at all decision sites. Strategy
convergence survives this extraction, so the completed assessment has exactly
the prescribed profile. No continuation optimality or compatibility with a
prescribed belief system follows from compactness.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type} {E : ExecutionProtocol ι} {M : InformationModel E}
  [Fintype ι] [∀ who, Finite (M.InformationSite who)]
  [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]

/-- A single subsequence completes the given strategy limit, simultaneously at
every site. The original sequence need not itself have convergent beliefs. -/
theorem BehavioralAssessment.exists_consistent_completion_subsequence
    (antichain : M.DecisionInformationAntichain)
    (profile : ∀ who, M.BehavioralPolicy who)
    (sequence : ℕ → M.BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (strategies : ∀ who (site : M.InformationSite who),
      PMFConvergesPointwise (fun n => (sequence n).strategy who site.1)
        (profile who site.1)) :
    ∃ assessment : M.BehavioralAssessment, assessment.strategy = profile ∧
      ∃ index : ℕ → ℕ, StrictMono index ∧
        BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) assessment ∧
        assessment.IsSequentiallyConsistent antichain := by
  obtain ⟨beliefs, index, increasing, converges⟩ := exists_subseq_pmfConvergesPointwise_pi
    (fun n (site : Σ who, M.InformationSite who) => (sequence n).belief site.1 site.2)
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
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (antichain : M.DecisionInformationAntichain)
    (sequence : ℕ → M.BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain) :
    ∃ assessment : M.BehavioralAssessment, ∃ index : ℕ → ℕ,
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) assessment ∧
      assessment.IsSequentiallyConsistent antichain := by
  classical
  obtain ⟨laws, first, firstIncreasing, firstConverges⟩ :=
    exists_subseq_pmfConvergesPointwise_pi
      (fun n (entry : Σ who, M.InformationSite who) =>
        (sequence n).strategy entry.1 entry.2.1)
  let profile : ∀ who, M.BehavioralPolicy who := fun who info =>
    if decision : M.IsDecisionInfo who info then laws ⟨who, ⟨info, decision⟩⟩
    else (sequence 0).strategy who info
  have strategies (who : ι) (site : M.InformationSite who) :
      PMFConvergesPointwise (fun n => (sequence (first n)).strategy who site.1)
        (profile who site.1) := by
    dsimp only [profile]
    rw [dite_eq_left site.2]
    exact firstConverges ⟨who, site⟩
  obtain ⟨assessment, _, second, secondIncreasing, converges, consistent⟩ :=
    BehavioralAssessment.exists_consistent_completion_subsequence antichain profile
      (fun n => sequence (first n)) (fun n => mixed (first n))
      (fun n => bayes (first n)) strategies
  exact ⟨assessment, first ∘ second, firstIncreasing.comp secondIncreasing,
    converges, consistent⟩

/-- Compactness retains any already established convergence of projected
Bayes beliefs. The projection law is an explicit premise: arbitrary consistent
completion alone supplies no compatibility with another game's beliefs. -/
theorem BehavioralAssessment.exists_consistent_completion_preserving
    (antichain : M.DecisionInformationAntichain)
    (profile : ∀ who, M.BehavioralPolicy who)
    (sequence : ℕ → M.BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
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
      mixed bayes strategies
  refine ⟨assessment, strategy, consistent, fun who site => ?_⟩
  exact ((converges.belief who site).map (project who site)).unique
    ((projected who site).subseq increasing)

/-- In a finite protocol admitting a fully mixed reference profile, every
profile has some sequentially consistent beliefs. This is consistency
existence, not equilibrium existence. -/
theorem BehavioralAssessment.exists_consistent_completion
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
      (fun who site => reference.perturb_strategy_converges profile weight
        (fun n => (positive n).le) atMostOne vanishes who site.1)
  exact ⟨assessment, strategy, consistent⟩

end GameTheory.Protocol.InformationModel

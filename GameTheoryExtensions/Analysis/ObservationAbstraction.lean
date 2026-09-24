/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationErasure
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Exact abstraction of terminal decision experiments

The concrete decision maker observes the complete hidden state. The abstract
decision maker observes a deterministic summary. Utilities and retained outcome
laws concern a fixed fact about the state together with the public action.

When the summary determines that fact on the prior support, conditional averaging
preserves every concrete outcome law; lifting an abstract policy preserves its
law directly. These maps also preserve Bayesian optimality for every utility of
the retained outcome. Conversely, if the summary merges distinct facts, the
reporting utility separates every abstract optimum from every concrete optimum.

This is a complete classification for this class of terminal decision
experiments. It does not classify multi-player sequential-equilibrium abstraction.
In this class the fact itself is a coarsest safe observation on the prior
support: it is safe, and it factors through every safe observation by
`preserves_all_optima_iff_determines` and `determines_iff_decoder`.
The concrete baseline observes the full state. A runtime that also lacks the
fact requires a relative comparison of information, not this absolute criterion.
-/

noncomputable section

namespace GameTheory.DecisionExperiment

open Math.Probability

variable {State Signal Action Fact : Type*}

theorem isBayesOptimal_iff_value (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → FinDist Action) :
    IsBayesOptimal prior observe utility policy ↔
      ∀ alternative, value prior observe utility alternative ≤
        value prior observe utility policy := by
  classical
  refine ⟨fun optimal => optimal.value_le, ?_⟩
  intro maximal signal alternative
  let replaced : Signal → FinDist Action :=
    fun current => if current = signal then alternative else policy current
  have replacement : value prior observe utility replaced =
      value prior observe utility policy - localValue prior observe utility signal (policy signal) +
        localValue prior observe utility signal alternative := by
    simp only [value_eq_expect, localValue, ← FinDist.expect_sub, ← FinDist.expect_add]
    apply FinDist.expect_congr
    intro state _
    by_cases same : observe state = signal
    · simp [replaced, same]
    · simp [replaced, same]
  have inequality := maximal replaced
  rw [replacement] at inequality
  linarith

/-- The outcome retained by the abstraction: a specified fact and the public action. -/
def resultLaw (prior : FinDist State) (observe : State → Signal) (fact : State → Fact)
    (policy : Signal → FinDist Action) : FinDist (Fact × Action) :=
  (outcomeLaw prior observe policy).map fun result => (fact result.1, result.2)

theorem resultLaw_eq_bind (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → FinDist Action) :
    resultLaw prior observe fact policy =
      prior.bind fun state => (policy (observe state)).map fun action => (fact state, action) := by
  simp only [resultLaw, outcomeLaw, FinDist.map_bind, FinDist.map_comp, Function.comp_def]

theorem resultLaw_fst (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → FinDist Action) :
    (resultLaw prior observe fact policy).map Prod.fst = prior.map fact := by
  rw [resultLaw_eq_bind]
  simp only [FinDist.map_bind, FinDist.map_comp, Function.comp_def, FinDist.map_const]
  rfl

theorem value_eq_resultLaw (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) (policy : Signal → FinDist Action) :
    value prior observe (fun state => utility (fact state)) policy =
      (resultLaw prior observe fact policy).expect (fun result => utility result.1 result.2) := by
  rw [value, resultLaw, FinDist.expect_map]

variable {Summary : Type*}

theorem resultLaw_of_decoder (prior : FinDist State) (observe : State → Signal)
    (summary : State → Summary) (fact : State → Fact) (decode : Summary → Fact)
    (decodes : ∀ state ∈ prior.support, decode (summary state) = fact state)
    (policy : Signal → FinDist Action) :
    resultLaw prior observe fact policy =
      (resultLaw prior observe summary policy).map fun result => (decode result.1, result.2) := by
  simp only [resultLaw_eq_bind, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
  apply FinDist.bind_congr
  intro state supported
  rw [decodes state supported]

/-- Average a fully informed response over the hidden states compatible with
the retained observation. The default at a zero-mass observation is immaterial. -/
def averagePolicy (prior : FinDist State) (observe : State → Signal)
    (policy : State → FinDist Action) : Signal → FinDist Action := fun signal =>
  (((resultLaw prior id observe policy).condOnFibre Prod.fst signal).map Prod.snd)

theorem averagePolicy_observation_law (prior : FinDist State) (observe : State → Signal)
    (policy : State → FinDist Action) :
    resultLaw prior observe observe (averagePolicy prior observe policy) =
      resultLaw prior id observe policy := by
  have disintegration := FinDist.eq_bind_fst_conditional_snd (resultLaw prior id observe policy)
  rw [resultLaw_fst, FinDist.bind_map] at disintegration
  rw [resultLaw_eq_bind]
  exact disintegration.symm

/-- No independence premise on the concrete policy is required. Correlations
with forgotten state are averaged while retaining the entire fact/action law. -/
theorem averagePolicy_result_law (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact)
    (policy : State → FinDist Action) :
    resultLaw prior observe fact (averagePolicy prior observe policy) =
      resultLaw prior id fact policy := by
  obtain ⟨decode, decodes⟩ := (determines_iff_decoder prior observe fact).mp determines
  rw [resultLaw_of_decoder prior observe observe fact decode decodes,
    resultLaw_of_decoder prior id observe fact decode decodes,
    averagePolicy_observation_law]

theorem averagePolicy_value (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (policy : State → FinDist Action) :
    value prior observe (fun state => utility (fact state))
        (averagePolicy prior observe policy) =
      value prior id (fun state => utility (fact state)) policy := by
  rw [value_eq_resultLaw, value_eq_resultLaw,
    averagePolicy_result_law prior observe fact determines]

/-- Every abstract optimum lifts to a fully informed optimum with the same
retained law, for every utility of the retained fact and public action. -/
theorem bayesOptimal_lift (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (policy : Signal → FinDist Action)
    (optimal : IsBayesOptimal prior observe (fun state => utility (fact state)) policy) :
    IsBayesOptimal prior id (fun state => utility (fact state))
      (fun state => policy (observe state)) := by
  rw [isBayesOptimal_iff_value]
  intro alternative
  have inequality := optimal.value_le (averagePolicy prior observe alternative)
  rw [averagePolicy_value prior observe fact determines] at inequality
  exact inequality

/-- Every fully informed optimum has an abstract optimum with the same
retained law. The abstract response may randomize even when the concrete one does not. -/
theorem bayesOptimal_average (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (policy : State → FinDist Action)
    (optimal : IsBayesOptimal prior id (fun state => utility (fact state)) policy) :
    IsBayesOptimal prior observe (fun state => utility (fact state))
      (averagePolicy prior observe policy) := by
  rw [isBayesOptimal_iff_value]
  intro alternative
  rw [averagePolicy_value prior observe fact determines]
  exact optimal.value_le (fun state => alternative (observe state))

/-- The complete sets of optimal retained outcome laws coincide. This is
utility-uniform, and the policy maps themselves do not depend on the utility. -/
theorem optimal_result_law_iff (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (law : FinDist (Fact × Action)) :
    (∃ policy : Signal → FinDist Action,
      IsBayesOptimal prior observe (fun state => utility (fact state)) policy ∧
        resultLaw prior observe fact policy = law) ↔
    (∃ policy : State → FinDist Action,
      IsBayesOptimal prior id (fun state => utility (fact state)) policy ∧
        resultLaw prior id fact policy = law) := by
  constructor
  · rintro ⟨policy, optimal, lawEq⟩
    exact ⟨fun state => policy (observe state),
      bayesOptimal_lift prior observe fact determines utility policy optimal, lawEq⟩
  · rintro ⟨policy, optimal, lawEq⟩
    exact ⟨averagePolicy prior observe policy,
      bayesOptimal_average prior observe fact determines utility policy optimal,
      (averagePolicy_result_law prior observe fact determines policy).trans lawEq⟩

/-- An exact necessity-and-sufficiency theorem for the abstraction class.
Reporting actions already form a complete set of tests: preserving every
abstract optimum for every utility on fact/report pairs is equivalent to the
observation determining the fact on the prior support. Sufficiency for other
action carriers is `bayesOptimal_lift` and `optimal_result_law_iff`. -/
theorem preserves_all_optima_iff_determines [Finite Fact] [Nonempty Fact]
    (prior : FinDist State) (observe : State → Signal) (fact : State → Fact) :
    (∀ utility : Fact → Fact → ℝ, ∀ source : Signal → FinDist Fact,
      IsBayesOptimal prior observe (fun state => utility (fact state)) source →
        ∃ target : State → FinDist Fact,
          IsBayesOptimal prior id (fun state => utility (fact state)) target ∧
            resultLaw prior id fact target = resultLaw prior observe fact source) ↔
      Determines prior observe fact := by
  classical
  constructor
  · intro preserves
    by_contra notDetermines
    simp only [Determines] at notDetermines
    push Not at notDetermines
    obtain ⟨first, firstPresent, second, secondPresent, same, different⟩ := notDetermines
    obtain ⟨source, sourceOptimal⟩ := exists_bayesOptimal prior observe (reportUtility fact)
    obtain ⟨target, targetOptimal, sameLaw⟩ :=
      preserves (fun actual report => if actual = report then 1 else 0) source sourceOptimal
    exact no_optimal_report_law_match prior observe id fact
      (fun first _ second _ same => congrArg fact same)
      firstPresent secondPresent same different source target targetOptimal sameLaw
  · intro determines utility source sourceOptimal
    exact ⟨fun state => source (observe state),
      bayesOptimal_lift prior observe fact determines utility source sourceOptimal, rfl⟩

end GameTheory.DecisionExperiment

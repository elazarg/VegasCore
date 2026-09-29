/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationErasure
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

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

theorem isBayesOptimal_iff_value (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (utility : State → Action → ℝ) (policy : Signal → PMF Action) :
    IsBayesOptimal prior observe utility policy ↔
      PolicyIntegrable prior utility policy ∧
        ∀ alternative, PolicyIntegrable prior utility alternative →
          value prior observe utility alternative ≤ value prior observe utility policy := by
  classical
  refine ⟨fun optimal => ⟨optimal.1, fun alternative integrable =>
    optimal.value_le priorFinite alternative integrable⟩, ?_⟩
  rintro ⟨integrable, maximal⟩
  refine ⟨integrable, fun signal alternative alternativeIntegrable => ?_⟩
  let replaced : Signal → PMF Action :=
    fun current => if current = signal then alternative else policy current
  have replacedIntegrable : PolicyIntegrable prior utility replaced := fun current => by
    by_cases same : current = signal
    · simpa only [replaced, same, ↓reduceIte] using alternativeIntegrable
    · simpa only [replaced, same, ↓reduceIte] using integrable current
  have finiteIntegrable (g : State → ℝ) := payoffIntegrable_of_finite_support prior g priorFinite
  have replacement : value prior observe utility replaced =
      value prior observe utility policy - localValue prior observe utility signal (policy signal) +
        localValue prior observe utility signal alternative := by
    rw [value_eq_expect _ _ _ _
        (outcomeLaw_integrable prior priorFinite observe utility _ replacedIntegrable),
      value_eq_expect _ _ _ _
        (outcomeLaw_integrable prior priorFinite observe utility _ integrable)]
    simp only [localValue]
    rw [← expect_sub (finiteIntegrable _) (finiteIntegrable _),
      ← expect_add (finiteIntegrable _) (finiteIntegrable _)]
    apply expect_congr_on_support
    intro state _
    by_cases same : observe state = signal
    · simp [replaced, same]
    · simp [replaced, same]
  have inequality := maximal replaced replacedIntegrable
  rw [replacement] at inequality
  linarith

/-- The outcome retained by the abstraction: a specified fact and the public action. -/
def resultLaw (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (policy : Signal → PMF Action) : PMF (Fact × Action) :=
  (outcomeLaw prior observe policy).map fun result => (fact result.1, result.2)

theorem resultLaw_eq_bind (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → PMF Action) :
    resultLaw prior observe fact policy =
      prior.bind fun state => (policy (observe state)).map fun action => (fact state, action) := by
  simp only [resultLaw, outcomeLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem resultLaw_fst (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → PMF Action) :
    (resultLaw prior observe fact policy).map Prod.fst = prior.map fact := by
  rw [resultLaw_eq_bind]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const]
  exact pmf_bind_pure_eq_map _ _

theorem value_eq_resultLaw (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) (policy : Signal → PMF Action) :
    value prior observe (fun state => utility (fact state)) policy =
      expect (resultLaw prior observe fact policy) (fun result => utility result.1 result.2) := by
  rw [value, resultLaw, expect_map]
  rfl

variable {Summary : Type*}

theorem resultLaw_of_decoder (prior : PMF State) (observe : State → Signal)
    (summary : State → Summary) (fact : State → Fact) (decode : Summary → Fact)
    (decodes : ∀ state ∈ prior.support, decode (summary state) = fact state)
    (policy : Signal → PMF Action) :
    resultLaw prior observe fact policy =
      (resultLaw prior observe summary policy).map fun result => (decode result.1, result.2) := by
  simp only [resultLaw_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro state supported
  rw [decodes state supported]

/-- Average a fully informed response over the hidden states compatible with
the retained observation. The default at a zero-mass observation is immaterial. -/
def averagePolicy (prior : PMF State) (observe : State → Signal)
    (policy : State → PMF Action) : Signal → PMF Action := fun signal =>
  ((fiberConditional (resultLaw prior id observe policy) Prod.fst signal).map Prod.snd)

theorem averagePolicy_observation_law (prior : PMF State) (observe : State → Signal)
    (policy : State → PMF Action) :
    resultLaw prior observe observe (averagePolicy prior observe policy) =
      resultLaw prior id observe policy := by
  have disintegration := eq_bind_fst_conditional_snd (resultLaw prior id observe policy)
  rw [resultLaw_fst, PMF.bind_map] at disintegration
  rw [resultLaw_eq_bind]
  exact disintegration.symm

/-- No independence premise on the concrete policy is required. Correlations
with forgotten state are averaged while retaining the entire fact/action law. -/
theorem averagePolicy_result_law (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact)
    (policy : State → PMF Action) :
    resultLaw prior observe fact (averagePolicy prior observe policy) =
      resultLaw prior id fact policy := by
  obtain ⟨decode, decodes⟩ := (determines_iff_decoder prior observe fact).mp determines
  rw [resultLaw_of_decoder prior observe observe fact decode decodes,
    resultLaw_of_decoder prior id observe fact decode decodes,
    averagePolicy_observation_law]

/-- Averaging integrable fully informed responses gives integrable responses:
each averaged response is a conditional of a finite mixture of them. -/
theorem averagePolicy_integrable (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (utility : State → Action → ℝ) (policy : State → PMF Action)
    (integrable : PolicyIntegrable prior utility policy) :
    PolicyIntegrable prior utility (averagePolicy prior observe policy) := by
  intro signal state supported
  unfold averagePolicy
  rw [payoffIntegrable_map_iff]
  apply payoffIntegrable_fiberConditional
  rw [resultLaw_eq_bind]
  exact payoffIntegrable_bind_of_finite_support _ _ _ priorFinite fun hidden _ =>
    (payoffIntegrable_map_iff _ _ _).mpr (integrable hidden state supported)

theorem averagePolicy_value (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (policy : State → PMF Action) :
    value prior observe (fun state => utility (fact state))
        (averagePolicy prior observe policy) =
      value prior id (fun state => utility (fact state)) policy := by
  rw [value_eq_resultLaw, value_eq_resultLaw,
    averagePolicy_result_law prior observe fact determines]

/-- Every abstract optimum lifts to a fully informed optimum with the same
retained law, for every utility of the retained fact and public action. -/
theorem bayesOptimal_lift (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (policy : Signal → PMF Action)
    (optimal : IsBayesOptimal prior observe (fun state => utility (fact state)) policy) :
    IsBayesOptimal prior id (fun state => utility (fact state))
      (fun state => policy (observe state)) := by
  rw [isBayesOptimal_iff_value prior priorFinite]
  refine ⟨fun state => optimal.1 (observe state), fun alternative integrable => ?_⟩
  have inequality := optimal.value_le priorFinite (averagePolicy prior observe alternative)
    (averagePolicy_integrable prior priorFinite observe _ alternative integrable)
  rw [averagePolicy_value prior observe fact determines] at inequality
  exact inequality

/-- Every fully informed optimum has an abstract optimum with the same
retained law. The abstract response may randomize even when the concrete one does not. -/
theorem bayesOptimal_average (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (policy : State → PMF Action)
    (optimal : IsBayesOptimal prior id (fun state => utility (fact state)) policy) :
    IsBayesOptimal prior observe (fun state => utility (fact state))
      (averagePolicy prior observe policy) := by
  rw [isBayesOptimal_iff_value prior priorFinite]
  refine ⟨averagePolicy_integrable prior priorFinite observe _ policy optimal.1,
    fun alternative integrable => ?_⟩
  rw [averagePolicy_value prior observe fact determines]
  exact optimal.value_le priorFinite (fun state => alternative (observe state))
    fun state => integrable (observe state)

/-- The complete sets of optimal retained outcome laws coincide. This is
utility-uniform, and the policy maps themselves do not depend on the utility. -/
theorem optimal_result_law_iff (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (fact : State → Fact) (determines : Determines prior observe fact)
    (utility : Fact → Action → ℝ) (law : PMF (Fact × Action)) :
    (∃ policy : Signal → PMF Action,
      IsBayesOptimal prior observe (fun state => utility (fact state)) policy ∧
        resultLaw prior observe fact policy = law) ↔
    (∃ policy : State → PMF Action,
      IsBayesOptimal prior id (fun state => utility (fact state)) policy ∧
        resultLaw prior id fact policy = law) := by
  constructor
  · rintro ⟨policy, optimal, lawEq⟩
    exact ⟨fun state => policy (observe state),
      bayesOptimal_lift prior priorFinite observe fact determines utility policy optimal, lawEq⟩
  · rintro ⟨policy, optimal, lawEq⟩
    exact ⟨averagePolicy prior observe policy,
      bayesOptimal_average prior priorFinite observe fact determines utility policy optimal,
      (averagePolicy_result_law prior observe fact determines policy).trans lawEq⟩

/-- An exact necessity-and-sufficiency theorem for the abstraction class.
Reporting actions already form a complete set of tests: preserving every
abstract optimum for every utility on fact/report pairs is equivalent to the
observation determining the fact on the prior support. Sufficiency for other
action carriers is `bayesOptimal_lift` and `optimal_result_law_iff`. -/
theorem preserves_all_optima_iff_determines [Finite Fact] [Nonempty Fact]
    (prior : PMF State) (priorFinite : prior.support.Finite) (observe : State → Signal)
    (fact : State → Fact) :
    (∀ utility : Fact → Fact → ℝ, ∀ source : Signal → PMF Fact,
      IsBayesOptimal prior observe (fun state => utility (fact state)) source →
        ∃ target : State → PMF Fact,
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
    obtain ⟨source, sourceOptimal⟩ :=
      exists_bayesOptimal prior priorFinite observe (reportUtility fact)
    obtain ⟨target, targetOptimal, sameLaw⟩ :=
      preserves (fun actual report => if actual = report then 1 else 0) source sourceOptimal
    exact no_optimal_report_law_match prior priorFinite observe id fact
      (fun first _ second _ same => congrArg fact same)
      firstPresent secondPresent same different source target targetOptimal sameLaw
  · intro determines utility source sourceOptimal
    exact ⟨fun state => source (observe state),
      bayesOptimal_lift prior priorFinite observe fact determines utility source sourceOptimal,
      rfl⟩

end GameTheory.DecisionExperiment

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationAbstraction

/-! # Observation abstraction for a fixed payoff

For a terminal decision, retaining every payoff-relevant fact is sufficient but
unnecessary when the payoff function is fixed. The exact weaker requirement is
that each supported observation fiber admits an action optimal at every state
in that fiber. Equivalently, learning the full state has zero decision value.

The conclusion preserves every abstract optimum's retained fact/action law;
it does not promise that every fully informed optimum has an abstract match.
The latter can fail even for constant payoffs, because informed actions may
correlate with the retained fact. These are terminal-decision results, not a
claim that arbitrary multiplayer communication can be erased.
-/

noncomputable section

namespace GameTheory.DecisionExperiment

open Math.Probability

variable {State Signal Action Fact : Type*}

theorem localValue_id (prior : FinDist State) (utility : State → Action → ℝ)
    (state : State) (response : FinDist Action) :
    localValue prior id utility state response =
      prior.prob state * response.expect (utility state) := by
  classical
  unfold localValue
  calc
    _ = prior.expect (fun actual => if state = actual then
        response.expect (utility state) else 0) := by
      apply FinDist.expect_congr
      intro actual _
      by_cases same : state = actual
      · subst actual
        simp
      · simp [same, Ne.symm same]
    _ = _ := FinDist.expect_ite_eq prior state _

/-- Full observation requires optimality separately at every supported state. -/
theorem fullInformation_optimal_iff (prior : FinDist State)
    (utility : State → Action → ℝ) (policy : State → FinDist Action) :
    IsBayesOptimal prior id utility policy ↔
      ∀ state ∈ prior.support, ∀ action,
        utility state action ≤ (policy state).expect (utility state) := by
  constructor
  · intro optimal state supported action
    have comparison := optimal state (FinDist.pure action)
    rw [localValue_id, localValue_id, FinDist.expect_pure] at comparison
    have positive := FinDist.prob_pos_iff.mpr supported
    nlinarith
  · intro optimal state alternative
    rw [localValue_id, localValue_id]
    by_cases supported : state ∈ prior.support
    · exact mul_le_mul_of_nonneg_left
        (FinDist.expect_le_of_forall _ _ _ fun action _ => optimal state supported action)
        (le_of_lt (FinDist.prob_pos_iff.mpr supported))
    · rw [FinDist.prob_eq_zero_iff.mpr supported, zero_mul, zero_mul]

/-- Every action used with positive probability must maximize the fixed payoff.
This criterion applies separately at each supported state. -/
theorem fullInformation_optimal_iff_support
    (prior : FinDist State) (utility : State → Action → ℝ)
    (policy : State → FinDist Action) :
    IsBayesOptimal prior id utility policy ↔
      ∀ state ∈ prior.support, ∀ action ∈ (policy state).support,
        ∀ alternative, utility state alternative ≤ utility state action := by
  rw [fullInformation_optimal_iff]
  constructor
  · intro optimal state supported action used alternative
    have selected := FinDist.eq_of_expect_eq_of_le (policy state) (utility state)
      ((policy state).expect (utility state))
      (fun candidate _ => optimal state supported candidate) rfl used
    rw [selected]
    exact optimal state supported alternative
  · intro optimal state supported alternative
    calc
      utility state alternative = (policy state).expect (fun _ => utility state alternative) :=
        (FinDist.expect_const _ _).symm
      _ ≤ _ := FinDist.expect_mono fun action used =>
        optimal state supported action used alternative

/-- Each supported observation fiber has at least one common maximizing action.
An unobserved state may affect payoffs, provided it never forces a conflicting
choice. Fibers outside the prior support impose no constraint. -/
def HasCommonMaximizer (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) : Prop :=
  ∀ signal, ∃ action, ∀ state ∈ prior.support, observe state = signal →
    ∀ alternative, utility state alternative ≤ utility state action

theorem exists_optimal_lift_iff_commonMaximizer
    (prior : FinDist State) (observe : State → Signal) (utility : State → Action → ℝ) :
    (∃ policy : Signal → FinDist Action,
      IsBayesOptimal prior id utility (fun state => policy (observe state))) ↔
      HasCommonMaximizer prior observe utility := by
  classical
  constructor
  · rintro ⟨policy, optimal⟩ signal
    obtain ⟨action, used⟩ := (policy signal).support_nonempty
    refine ⟨action, ?_⟩
    intro state supported same alternative
    exact (fullInformation_optimal_iff_support prior utility _).mp optimal
      state supported action (by simpa only [same] using used) alternative
  · intro common
    choose best maximal using common
    refine ⟨fun signal => FinDist.pure (best signal), ?_⟩
    rw [fullInformation_optimal_iff]
    intro state supported action
    simpa only [FinDist.expect_pure] using maximal (observe state) state supported rfl action

/-- A matching fully informed optimum exists exactly when the original policy
itself remains optimal with full information. Equality of the retained law is
strong enough because the fixed payoff factors through that law. -/
theorem optimal_match_iff_lift (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) (source : Signal → FinDist Action) :
    (∃ target : State → FinDist Action,
      IsBayesOptimal prior id (fun state => utility (fact state)) target ∧
        resultLaw prior id fact target = resultLaw prior observe fact source) ↔
      IsBayesOptimal prior id (fun state => utility (fact state))
        (fun state => source (observe state)) := by
  constructor
  · rintro ⟨target, optimal, sameLaw⟩
    rw [isBayesOptimal_iff_value]
    intro alternative
    have comparison := optimal.value_le alternative
    rw [value_eq_resultLaw prior id fact utility target, sameLaw,
      ← value_eq_resultLaw prior observe fact utility source] at comparison
    exact comparison
  · intro optimal
    exact ⟨fun state => source (observe state), optimal, rfl⟩

/-- Exact fixed-payoff classification. It permits more observation erasure than
requiring the fact to be recoverable. Target strategies may depend on the payoff,
but whenever a match exists, the simple observation-respecting lift suffices. -/
theorem preserves_fixed_payoff_iff_commonMaximizer [Finite Action] [Nonempty Action]
    (prior : FinDist State) (observe : State → Signal) (fact : State → Fact)
    (utility : Fact → Action → ℝ) :
    (∀ source : Signal → FinDist Action,
      IsBayesOptimal prior observe (fun state => utility (fact state)) source →
        ∃ target : State → FinDist Action,
          IsBayesOptimal prior id (fun state => utility (fact state)) target ∧
            resultLaw prior id fact target = resultLaw prior observe fact source) ↔
      HasCommonMaximizer prior observe (fun state => utility (fact state)) := by
  constructor
  · intro preserves
    obtain ⟨source, optimal⟩ :=
      exists_bayesOptimal prior observe (fun state => utility (fact state))
    exact (exists_optimal_lift_iff_commonMaximizer prior observe _).mp
      ⟨source, (optimal_match_iff_lift prior observe fact utility source).mp
        (preserves source optimal)⟩
  · intro common source sourceOptimal
    obtain ⟨witness, witnessOptimal⟩ :=
      (exists_optimal_lift_iff_commonMaximizer prior observe _).mpr common
    apply (optimal_match_iff_lift prior observe fact utility source).mpr
    rw [isBayesOptimal_iff_value]
    intro alternative
    exact (witnessOptimal.value_le alternative).trans (sourceOptimal.value_le witness)

end GameTheory.DecisionExperiment

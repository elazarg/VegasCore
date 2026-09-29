/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationAbstraction
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

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

theorem localValue_id (prior : PMF State) (utility : State → Action → ℝ)
    (state : State) (response : PMF Action) :
    localValue prior id utility state response =
      (prior state).toReal * expect response (utility state) := by
  classical
  unfold localValue
  calc
    _ = expect prior (fun actual => if state = actual then
        expect response (utility state) else 0) := by
      apply expect_congr_on_support
      intro actual _
      by_cases same : state = actual
      · subst actual
        simp
      · simp [same, Ne.symm same]
    _ = _ := expect_ite_eq prior state _

/-- Full observation requires optimality separately at every supported state. -/
theorem fullInformation_optimal_iff (prior : PMF State)
    (utility : State → Action → ℝ) (policy : State → PMF Action) :
    IsBayesOptimal prior id utility policy ↔
      PolicyIntegrable prior utility policy ∧
        ∀ state ∈ prior.support, ∀ action,
          utility state action ≤ expect (policy state) (utility state) := by
  constructor
  · intro optimal
    refine ⟨optimal.1, fun state supported action => ?_⟩
    have comparison := optimal.2 state (PMF.pure action)
      (fun _ _ => payoffIntegrable_pure _ _)
    rw [localValue_id, localValue_id, expect_pure] at comparison
    have positive := pmf_toReal_pos_iff.mpr supported
    nlinarith
  · rintro ⟨integrable, optimal⟩
    refine ⟨integrable, fun state alternative alternativeIntegrable => ?_⟩
    rw [localValue_id, localValue_id]
    by_cases supported : state ∈ prior.support
    · exact mul_le_mul_of_nonneg_left
        (expect_le_const _ _ (alternativeIntegrable state supported) _ fun action _ =>
          optimal state supported action)
        (le_of_lt (pmf_toReal_pos_iff.mpr supported))
    · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, ENNReal.toReal_zero, zero_mul, zero_mul]

/-- Every action used with positive probability must maximize the fixed payoff.
This criterion applies separately at each supported state. -/
theorem fullInformation_optimal_iff_support
    (prior : PMF State) (utility : State → Action → ℝ)
    (policy : State → PMF Action) :
    IsBayesOptimal prior id utility policy ↔
      PolicyIntegrable prior utility policy ∧
        ∀ state ∈ prior.support, ∀ action ∈ (policy state).support,
          ∀ alternative, utility state alternative ≤ utility state action := by
  rw [fullInformation_optimal_iff]
  refine and_congr_right fun integrable => ?_
  constructor
  · intro optimal state supported action used alternative
    have selected := expect_eq_const_of_le_on_support (policy state) (utility state)
      (expect (policy state) (utility state)) (integrable state state supported)
      (fun candidate _ => optimal state supported candidate) rfl action used
    rw [selected]
    exact optimal state supported alternative
  · intro optimal state supported alternative
    calc
      utility state alternative = expect (policy state) (fun _ => utility state alternative) :=
        (expect_constant _ _).symm
      _ ≤ _ := expect_mono (fun action used => optimal state supported action used alternative)
        (payoffIntegrable_constant _ _) (integrable state state supported)

/-- Each supported observation fiber has at least one common maximizing action.
An unobserved state may affect payoffs, provided it never forces a conflicting
choice. Fibers outside the prior support impose no constraint. -/
def HasCommonMaximizer (prior : PMF State) (observe : State → Signal)
    (utility : State → Action → ℝ) : Prop :=
  ∀ signal, ∃ action, ∀ state ∈ prior.support, observe state = signal →
    ∀ alternative, utility state alternative ≤ utility state action

theorem exists_optimal_lift_iff_commonMaximizer
    (prior : PMF State) (observe : State → Signal) (utility : State → Action → ℝ) :
    (∃ policy : Signal → PMF Action,
      IsBayesOptimal prior id utility (fun state => policy (observe state))) ↔
      HasCommonMaximizer prior observe utility := by
  classical
  constructor
  · rintro ⟨policy, optimal⟩ signal
    obtain ⟨action, used⟩ := (policy signal).support_nonempty
    refine ⟨action, ?_⟩
    intro state supported same alternative
    exact ((fullInformation_optimal_iff_support prior utility _).mp optimal).2
      state supported action (by simpa only [same] using used) alternative
  · intro common
    choose best maximal using common
    refine ⟨fun signal => PMF.pure (best signal), ?_⟩
    rw [fullInformation_optimal_iff]
    refine ⟨fun _ _ _ => payoffIntegrable_pure _ _, fun state supported action => ?_⟩
    simpa only [expect_pure] using maximal (observe state) state supported rfl action

/-- A matching fully informed optimum exists exactly when the original policy
itself remains optimal with full information. Equality of the retained law is
strong enough because the fixed payoff factors through that law. -/
theorem optimal_match_iff_lift (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (fact : State → Fact) (utility : Fact → Action → ℝ)
    (source : Signal → PMF Action)
    (sourceIntegrable : PolicyIntegrable prior (fun state => utility (fact state)) source) :
    (∃ target : State → PMF Action,
      IsBayesOptimal prior id (fun state => utility (fact state)) target ∧
        resultLaw prior id fact target = resultLaw prior observe fact source) ↔
      IsBayesOptimal prior id (fun state => utility (fact state))
        (fun state => source (observe state)) := by
  constructor
  · rintro ⟨target, optimal, sameLaw⟩
    rw [isBayesOptimal_iff_value prior priorFinite]
    refine ⟨fun state => sourceIntegrable (observe state), fun alternative integrable => ?_⟩
    have comparison := optimal.value_le priorFinite alternative integrable
    rw [value_eq_resultLaw prior id fact utility target, sameLaw,
      ← value_eq_resultLaw prior observe fact utility source] at comparison
    exact comparison
  · intro optimal
    exact ⟨fun state => source (observe state), optimal, rfl⟩

/-- Exact fixed-payoff classification. It permits more observation erasure than
requiring the fact to be recoverable. Target strategies may depend on the payoff,
but whenever a match exists, the simple observation-respecting lift suffices. -/
theorem preserves_fixed_payoff_iff_commonMaximizer [Finite Action] [Nonempty Action]
    (prior : PMF State) (priorFinite : prior.support.Finite) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) :
    (∀ source : Signal → PMF Action,
      IsBayesOptimal prior observe (fun state => utility (fact state)) source →
        ∃ target : State → PMF Action,
          IsBayesOptimal prior id (fun state => utility (fact state)) target ∧
            resultLaw prior id fact target = resultLaw prior observe fact source) ↔
      HasCommonMaximizer prior observe (fun state => utility (fact state)) := by
  constructor
  · intro preserves
    obtain ⟨source, optimal⟩ :=
      exists_bayesOptimal prior priorFinite observe (fun state => utility (fact state))
    exact (exists_optimal_lift_iff_commonMaximizer prior observe _).mp
      ⟨source, (optimal_match_iff_lift prior priorFinite observe fact utility source
        optimal.1).mp (preserves source optimal)⟩
  · intro common source sourceOptimal
    obtain ⟨witness, witnessOptimal⟩ :=
      (exists_optimal_lift_iff_commonMaximizer prior observe _).mpr common
    apply (optimal_match_iff_lift prior priorFinite observe fact utility source
      sourceOptimal.1).mpr
    rw [isBayesOptimal_iff_value prior priorFinite]
    refine ⟨fun _ => ResponseIntegrable.of_finite prior _ _, fun alternative integrable => ?_⟩
    exact (witnessOptimal.value_le priorFinite alternative integrable).trans
      (sourceOptimal.value_le priorFinite witness
        fun _ => ResponseIntegrable.of_finite prior _ _)

end GameTheory.DecisionExperiment

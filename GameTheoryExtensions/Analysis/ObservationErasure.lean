/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Support
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Decision experiments detecting erased information

A terminal decision experiment samples a hidden state, shows one deterministic
observation, and records a public action. The permitted outcome is the pair of
hidden state and public action. Thus utilities may value a fact about the hidden
state; they do not have to value an implementation observation directly.

For the utility that rewards reporting a specified fact correctly, perfect
reporting is possible exactly when that fact is constant on the positive-prior
observation fibers. Randomization cannot recover information erased by a merge.
The characterization is local to the prior support, so merging unreachable
states does not by itself supply an obstruction.

Values are real expectations, so optimality compares only responses whose
payoff has a finite expectation at every state the prior can draw. Results that
split a value over observation fibers assume a finitely supported prior. Both
conditions hold for every finitely supported experiment.

These are decision-theoretic results. Their optimality predicate is Bayesian
optimality at every observation of a terminal decision experiment, not a new
definition of sequential equilibrium for general protocols.
-/

noncomputable section

namespace GameTheory.DecisionExperiment

open Math.Probability

variable {State Signal Action Fact : Type*}

def outcomeLaw (prior : PMF State) (observe : State → Signal)
    (policy : Signal → PMF Action) : PMF (State × Action) :=
  prior.bind fun state => (policy (observe state)).map fun action => (state, action)

def value (prior : PMF State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → PMF Action) : ℝ :=
  expect (outcomeLaw prior observe policy) fun result => utility result.1 result.2

/-- A response has a finite expected payoff at every state the prior can draw. -/
def ResponseIntegrable (prior : PMF State) (utility : State → Action → ℝ)
    (response : PMF Action) : Prop :=
  ∀ state ∈ prior.support, PayoffIntegrable response (utility state)

/-- Every response of the policy has a finite expected payoff at every prior state. -/
def PolicyIntegrable (prior : PMF State) (utility : State → Action → ℝ)
    (policy : Signal → PMF Action) : Prop :=
  ∀ signal, ResponseIntegrable prior utility (policy signal)

theorem ResponseIntegrable.of_finite [Finite Action] (prior : PMF State)
    (utility : State → Action → ℝ) (response : PMF Action) :
    ResponseIntegrable prior utility response :=
  fun _ _ => payoffIntegrable_of_finite _ _

theorem ResponseIntegrable.of_bounded {C : ℝ} (prior : PMF State)
    (utility : State → Action → ℝ) (bound : ∀ state action, |utility state action| ≤ C)
    (response : PMF Action) : ResponseIntegrable prior utility response :=
  fun state _ => payoffIntegrable_of_bounded _ _ (bound state)

theorem outcomeLaw_integrable (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (utility : State → Action → ℝ) (policy : Signal → PMF Action)
    (integrable : PolicyIntegrable prior utility policy) :
    PayoffIntegrable (outcomeLaw prior observe policy) fun result => utility result.1 result.2 :=
  payoffIntegrable_bind_of_finite_support _ _ _ priorFinite fun state supported =>
    (payoffIntegrable_map_iff _ _ _).mpr (integrable (observe state) state supported)

theorem outcomeLaw_integrable_of_bounded {C : ℝ} (prior : PMF State) (observe : State → Signal)
    (utility : State → Action → ℝ) (bound : ∀ state action, |utility state action| ≤ C)
    (policy : Signal → PMF Action) :
    PayoffIntegrable (outcomeLaw prior observe policy) fun result => utility result.1 result.2 :=
  payoffIntegrable_of_bounded _ _ fun result => bound result.1 result.2

theorem value_eq_expect (prior : PMF State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → PMF Action)
    (integrable : PayoffIntegrable (outcomeLaw prior observe policy)
      fun result => utility result.1 result.2) :
    value prior observe utility policy =
      expect prior (fun state => expect (policy (observe state)) (utility state)) := by
  rw [value, outcomeLaw, expect_bind_tower _ _ _ integrable]
  simp only [expect_map, Function.comp_def]

/-- Unnormalized conditional value. Zero-probability observations impose no
constraint; on a positive-probability fiber normalization cancels from comparisons. -/
def localValue (prior : PMF State) (observe : State → Signal)
    (utility : State → Action → ℝ) (signal : Signal) (response : PMF Action) : ℝ :=
  expect prior ((observe ⁻¹' {signal}).indicator fun state => expect response (utility state))

/-- At every observation, no response with a finite expected payoff improves on the
policy's own response, whose payoffs also have finite expectations. -/
def IsBayesOptimal (prior : PMF State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → PMF Action) : Prop :=
  PolicyIntegrable prior utility policy ∧
    ∀ signal alternative, ResponseIntegrable prior utility alternative →
      localValue prior observe utility signal alternative ≤
        localValue prior observe utility signal (policy signal)

theorem value_eq_sum_local (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (utility : State → Action → ℝ) (policy : Signal → PMF Action)
    (integrable : PolicyIntegrable prior utility policy) :
    value prior observe utility policy =
      ∑ signal ∈ (priorFinite.image observe).toFinset,
        localValue prior observe utility signal (policy signal) := by
  classical
  rw [value_eq_expect _ _ _ _ (outcomeLaw_integrable prior priorFinite observe utility policy
    integrable), expect_eq_sum_of_support_finite _ priorFinite]
  simp only [localValue, expect_eq_sum_of_support_finite _ priorFinite]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state supported
  rw [Finset.sum_eq_single (observe state)]
  · simp
  · intro signal _ different
    simp [Ne.symm different]
  · intro absent
    exact (absent ((Set.Finite.mem_toFinset _).mpr
      ⟨state, (Set.Finite.mem_toFinset _).mp supported, rfl⟩)).elim

theorem IsBayesOptimal.value_le {prior : PMF State} {observe : State → Signal}
    {utility : State → Action → ℝ} {policy : Signal → PMF Action}
    (optimal : IsBayesOptimal prior observe utility policy) (priorFinite : prior.support.Finite)
    (alternative : Signal → PMF Action) (integrable : PolicyIntegrable prior utility alternative) :
    value prior observe utility alternative ≤ value prior observe utility policy := by
  rw [value_eq_sum_local prior priorFinite observe utility alternative integrable,
    value_eq_sum_local prior priorFinite observe utility policy optimal.1]
  exact Finset.sum_le_sum fun signal _ => optimal.2 signal (alternative signal) (integrable signal)

theorem localValue_eq_expect_pure (prior : PMF State) (priorFinite : prior.support.Finite)
    (observe : State → Signal) (utility : State → Action → ℝ) (signal : Signal)
    (response : PMF Action) (integrable : ResponseIntegrable prior utility response) :
    localValue prior observe utility signal response =
      expect response fun action =>
        localValue prior observe utility signal (PMF.pure action) := by
  classical
  unfold localValue
  have indicator (state : State) :
      (observe ⁻¹' {signal}).indicator (fun state => expect response (utility state)) state =
        expect response fun action =>
          (observe ⁻¹' {signal}).indicator (fun state => utility state action) state := by
    by_cases same : observe state = signal
    · simp [same]
    · simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, same, ↓reduceIte,
        expect_constant]
  rw [funext indicator,
    expect_comm_of_support_finite_left _ _ priorFinite _ fun state supported => by
    by_cases same : observe state = signal
    · simpa [same] using integrable state supported
    · simpa [same] using payoffIntegrable_constant response 0]
  apply expect_congr_on_support
  intro action _
  apply expect_congr_on_support
  intro state _
  by_cases same : observe state = signal
  · simp [same, expect_pure]
  · simp [same]

/-- A finite action menu has an optimal response at every observation. The
observation and hidden-state carriers need not themselves be finite; the prior
has finite support. -/
theorem exists_bayesOptimal [Finite Action] [Nonempty Action]
    (prior : PMF State) (priorFinite : prior.support.Finite) (observe : State → Signal)
    (utility : State → Action → ℝ) :
    ∃ policy, IsBayesOptimal prior observe utility policy := by
  classical
  choose best maximal using fun signal => Finite.exists_max
    (fun action => localValue prior observe utility signal (PMF.pure action))
  refine ⟨fun signal => PMF.pure (best signal),
    fun _ => ResponseIntegrable.of_finite prior utility _, ?_⟩
  intro signal alternative integrable
  rw [localValue_eq_expect_pure prior priorFinite observe utility signal alternative integrable]
  refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun action _ => ?_
  exact maximal signal action

/-- The payoff-relevant fact can be recovered from the observation wherever
the prior has positive mass. -/
def Determines (prior : PMF State) (observe : State → Signal) (fact : State → Fact) : Prop :=
  ∀ first ∈ prior.support, ∀ second ∈ prior.support,
    observe first = observe second → fact first = fact second

theorem determines_iff_of_fullSupport (prior : PMF State) (full : FullSupport prior)
    (observe : State → Signal) (fact : State → Fact) :
    Determines prior observe fact ↔
      ∀ first second, observe first = observe second → fact first = fact second := by
  exact ⟨fun determines first second => determines first (full first) second (full second),
    fun determines first _ second _ => determines first second⟩

theorem determines_iff_decoder (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) :
    Determines prior observe fact ↔
      ∃ decode : Signal → Fact, ∀ state ∈ prior.support, decode (observe state) = fact state := by
  classical
  constructor
  · intro determines
    let representative (signal : Signal) : State :=
      if found : ∃ state ∈ prior.support, observe state = signal then found.choose
      else prior.support_nonempty.choose
    refine ⟨fun signal => fact (representative signal), ?_⟩
    intro state supported
    have found : ∃ other ∈ prior.support, observe other = observe state :=
      ⟨state, supported, rfl⟩
    have properties : representative (observe state) ∈ prior.support ∧
        observe (representative (observe state)) = observe state := by
      simpa only [representative, dite_eq_left found] using found.choose_spec
    exact determines _ properties.1 state supported properties.2
  · rintro ⟨decode, decodes⟩ first firstPresent second secondPresent same
    rw [← decodes first firstPresent, ← decodes second secondPresent, same]

def reportUtility [DecidableEq Fact] (fact : State → Fact) (state : State) (report : Fact) : ℝ :=
  if fact state = report then 1 else 0

theorem reportUtility_abs_le [DecidableEq Fact] (fact : State → Fact) (state : State)
    (report : Fact) : |reportUtility fact state report| ≤ 1 := by
  unfold reportUtility
  split_ifs <;> norm_num

theorem report_value [DecidableEq Fact] (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → PMF Fact) :
    value prior observe (reportUtility fact) policy =
      expect prior fun state => ((policy (observe state)) (fact state)).toReal := by
  rw [value_eq_expect _ _ _ _ (outcomeLaw_integrable_of_bounded prior observe _
    (reportUtility_abs_le fact) policy)]
  apply expect_congr_on_support
  intro state _
  change expect (policy (observe state)) (fun report => if fact state = report then 1 else 0) = _
  rw [expect_ite_eq, mul_one]

private theorem atomIntegrable (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → PMF Fact) :
    PayoffIntegrable prior fun state => ((policy (observe state)) (fact state)).toReal :=
  payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact pmf_toReal_apply_le_one _ _

theorem report_value_le_one [DecidableEq Fact] (prior : PMF State)
    (observe : State → Signal) (fact : State → Fact) (policy : Signal → PMF Fact) :
    value prior observe (reportUtility fact) policy ≤ 1 := by
  rw [report_value]
  exact expect_le_const _ _ (atomIntegrable prior observe fact policy) _ fun _ _ =>
    pmf_toReal_apply_le_one _ _

private theorem eq_pure_of_prob_one (law : PMF Fact) (fact : Fact)
    (certain : (law fact).toReal = 1) : law = PMF.pure fact := by
  classical
  have one : law fact = 1 := by
    rw [← ENNReal.toReal_eq_one_iff]
    exact certain
  have support := (PMF.apply_eq_one_iff law fact).mp one
  ext other
  by_cases same : other = fact
  · subst other
    rw [one, PMF.pure_apply_self]
  · have absent : other ∉ law.support := by
      rw [support]
      exact same
    rw [(PMF.apply_eq_zero_iff _ _).mpr absent, PMF.pure_apply_of_ne _ _ same]

theorem report_value_eq_one_iff [DecidableEq Fact] (prior : PMF State)
    (observe : State → Signal) (fact : State → Fact) (policy : Signal → PMF Fact) :
    value prior observe (reportUtility fact) policy = 1 ↔
      ∀ state ∈ prior.support, policy (observe state) = PMF.pure (fact state) := by
  rw [report_value]
  constructor
  · intro one state supported
    exact eq_pure_of_prob_one _ _ (expect_eq_const_of_le_on_support prior _ 1
      (atomIntegrable prior observe fact policy) (fun _ _ => pmf_toReal_apply_le_one _ _) one
        state supported)
  · intro certain
    calc
      _ = expect prior (fun _ => (1 : ℝ)) := by
        apply expect_congr_on_support
        intro state supported
        rw [certain state supported, PMF.pure_apply_self, ENNReal.toReal_one]
      _ = 1 := expect_constant _ _

/-- Exact classification: randomized reporting achieves certainty precisely
when an ordinary deterministic decoder exists on the prior support. -/
theorem exists_perfect_report_iff [DecidableEq Fact] (prior : PMF State)
    (observe : State → Signal) (fact : State → Fact) :
    (∃ policy, value prior observe (reportUtility fact) policy = 1) ↔
      Determines prior observe fact := by
  constructor
  · rintro ⟨policy, perfect⟩ first firstPresent second secondPresent same
    have certain := (report_value_eq_one_iff prior observe fact policy).mp perfect
    have equal : PMF.pure (fact first) = PMF.pure (fact second) := by
      rw [← certain first firstPresent, ← certain second secondPresent, same]
    have member : fact first ∈ (PMF.pure (fact second)).support := by
      rw [← equal, PMF.mem_support_pure_iff _ _]
    exact (PMF.mem_support_pure_iff _ _).mp member
  · intro determines
    obtain ⟨decode, decodes⟩ := (determines_iff_decoder prior observe fact).mp determines
    refine ⟨fun signal => PMF.pure (decode signal), ?_⟩
    rw [report_value_eq_one_iff]
    intro state supported
    rw [decodes state supported]

/-- Equality of the complete initialized state/report law, not only its value. -/
theorem report_value_eq_one_iff_law [DecidableEq Fact] (prior : PMF State)
    (observe : State → Signal) (fact : State → Fact) (policy : Signal → PMF Fact) :
    value prior observe (reportUtility fact) policy = 1 ↔
      outcomeLaw prior observe policy = prior.map (fun state => (state, fact state)) := by
  constructor
  · intro perfect
    have certain := (report_value_eq_one_iff prior observe fact policy).mp perfect
    rw [outcomeLaw, ← pmf_bind_pure_eq_map]
    apply bind_congr_on_support _
    intro state supported
    rw [certain state supported, PMF.pure_map]
  · intro sameLaw
    rw [value, sameLaw, expect_map]
    simp only [Function.comp_def, reportUtility, ↓reduceIte, expect_constant]

theorem bayesOptimal_report_value_eq_one [DecidableEq Fact]
    (prior : PMF State) (priorFinite : prior.support.Finite) (observe : State → Signal)
    (fact : State → Fact) (determines : Determines prior observe fact) (policy : Signal → PMF Fact)
    (optimal : IsBayesOptimal prior observe (reportUtility fact) policy) :
    value prior observe (reportUtility fact) policy = 1 := by
  obtain ⟨perfect, perfectValue⟩ := (exists_perfect_report_iff prior observe fact).mpr determines
  apply le_antisymm (report_value_le_one prior observe fact policy)
  rw [← perfectValue]
  exact optimal.value_le priorFinite perfect fun _ =>
    ResponseIntegrable.of_bounded prior _ (reportUtility_abs_le fact) _

/-- Merging two positive-probability states with different payoff-relevant
facts forces a strictly positive error for every randomized abstract policy. -/
theorem report_value_lt_one_of_collision [DecidableEq Fact]
    (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    {first second : State} (firstPresent : first ∈ prior.support)
    (secondPresent : second ∈ prior.support) (same : observe first = observe second)
    (different : fact first ≠ fact second) (policy : Signal → PMF Fact) :
    value prior observe (reportUtility fact) policy < 1 := by
  refine lt_of_le_of_ne (report_value_le_one prior observe fact policy) ?_
  intro perfect
  exact different ((exists_perfect_report_iff prior observe fact).mp ⟨policy, perfect⟩
    first firstPresent second secondPresent same)

variable {Fine : Type*}

/-- For the fact-reporting utility, an informed optimum cannot match any
coarse policy's fact/report outcome law if the coarse observation merges two
positive-prior states with distinct facts. The source policy is unrestricted;
in particular this holds for every source optimum and every translator. -/
theorem no_optimal_report_law_match [DecidableEq Fact]
    (prior : PMF State) (priorFinite : prior.support.Finite) (coarse : State → Signal)
    (fine : State → Fine) (fact : State → Fact) (fineDetermines : Determines prior fine fact)
    {first second : State} (firstPresent : first ∈ prior.support)
    (secondPresent : second ∈ prior.support) (same : coarse first = coarse second)
    (different : fact first ≠ fact second) (source : Signal → PMF Fact)
    (target : Fine → PMF Fact)
    (targetOptimal : IsBayesOptimal prior fine (reportUtility fact) target) :
    (outcomeLaw prior fine target).map (fun result => (fact result.1, result.2)) ≠
      (outcomeLaw prior coarse source).map (fun result => (fact result.1, result.2)) := by
  intro sameLaw
  have sourceBound := report_value_lt_one_of_collision prior coarse fact
    firstPresent secondPresent same different source
  have targetValue := bayesOptimal_report_value_eq_one prior priorFinite fine fact
    fineDetermines target targetOptimal
  have sameValue := congrArg (fun law : PMF (Fact × Fact) =>
    expect law (fun result => if result.1 = result.2 then (1 : ℝ) else 0)) sameLaw
  simp only [expect_map, Function.comp_def] at sameValue
  change value prior fine (reportUtility fact) target =
    value prior coarse (reportUtility fact) source at sameValue
  linarith

/-- A finite reporting experiment has a source optimum, but no informed
target optimum can match its fact/report law after a relevant observation merge.
This does not quantify over general protocol sequential equilibria. -/
theorem exists_optimal_no_report_law_match [Finite Fact] [Nonempty Fact] [DecidableEq Fact]
    (prior : PMF State) (priorFinite : prior.support.Finite) (coarse : State → Signal)
    (fine : State → Fine) (fact : State → Fact) (fineDetermines : Determines prior fine fact)
    {first second : State} (firstPresent : first ∈ prior.support)
    (secondPresent : second ∈ prior.support) (same : coarse first = coarse second)
    (different : fact first ≠ fact second) :
    ∃ source : Signal → PMF Fact,
      IsBayesOptimal prior coarse (reportUtility fact) source ∧
      ∀ target : Fine → PMF Fact,
        IsBayesOptimal prior fine (reportUtility fact) target →
          (outcomeLaw prior fine target).map (fun result => (fact result.1, result.2)) ≠
            (outcomeLaw prior coarse source).map (fun result => (fact result.1, result.2)) := by
  obtain ⟨source, optimal⟩ := exists_bayesOptimal prior priorFinite coarse (reportUtility fact)
  exact ⟨source, optimal, fun target targetOptimal => no_optimal_report_law_match
    prior priorFinite coarse fine fact fineDetermines firstPresent secondPresent same different
      source target targetOptimal⟩

end GameTheory.DecisionExperiment

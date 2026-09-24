/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

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

These are decision-theoretic results. Their optimality predicate is Bayesian
optimality at every observation of a terminal decision experiment, not a new
definition of sequential equilibrium for general protocols.
-/

noncomputable section

namespace GameTheory.DecisionExperiment

open Math.Probability

variable {State Signal Action Fact : Type*}

def outcomeLaw (prior : FinDist State) (observe : State → Signal)
    (policy : Signal → FinDist Action) : FinDist (State × Action) :=
  prior.bind fun state => (policy (observe state)).map fun action => (state, action)

def value (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → FinDist Action) : ℝ :=
  (outcomeLaw prior observe policy).expect fun result => utility result.1 result.2

theorem value_eq_expect (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → FinDist Action) :
    value prior observe utility policy =
      prior.expect (fun state => (policy (observe state)).expect (utility state)) := by
  simp only [value, outcomeLaw, FinDist.expect_bind, FinDist.expect_map]

/-- Unnormalized conditional value. Zero-probability observations impose no
constraint; on a positive-probability fiber normalization cancels from comparisons. -/
def localValue (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) (signal : Signal) (response : FinDist Action) : ℝ :=
  prior.expect ((observe ⁻¹' {signal}).indicator fun state => response.expect (utility state))

def IsBayesOptimal (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → FinDist Action) : Prop :=
  ∀ signal alternative,
    localValue prior observe utility signal alternative ≤
      localValue prior observe utility signal (policy signal)

theorem value_eq_sum_local (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) (policy : Signal → FinDist Action) :
    value prior observe utility policy =
      ∑ signal ∈ (prior.map observe).supportFinset,
        localValue prior observe utility signal (policy signal) := by
  classical
  rw [value_eq_expect, FinDist.expect_eq_sum_fibers prior observe]
  apply Finset.sum_congr rfl
  intro signal _
  apply FinDist.expect_congr
  intro state _
  by_cases same : observe state = signal
  · simp [same]
  · simp [same]

theorem IsBayesOptimal.value_le {prior : FinDist State} {observe : State → Signal}
    {utility : State → Action → ℝ} {policy : Signal → FinDist Action}
    (optimal : IsBayesOptimal prior observe utility policy)
    (alternative : Signal → FinDist Action) :
    value prior observe utility alternative ≤ value prior observe utility policy := by
  rw [value_eq_sum_local, value_eq_sum_local]
  exact Finset.sum_le_sum fun signal _ => optimal signal (alternative signal)

theorem localValue_eq_expect_pure (prior : FinDist State) (observe : State → Signal)
    (utility : State → Action → ℝ) (signal : Signal) (response : FinDist Action) :
    localValue prior observe utility signal response =
      response.expect fun action =>
        localValue prior observe utility signal (FinDist.pure action) := by
  classical
  unfold localValue
  rw [FinDist.expect_comm]
  apply FinDist.expect_congr
  intro state _
  by_cases same : observe state = signal
  · simp [same, FinDist.expect_pure]
  · simp [same, FinDist.expect_const]

/-- A finite action menu has an optimal response at every observation. The
observation and hidden-state carriers need not themselves be finite. -/
theorem exists_bayesOptimal [Finite Action] [Nonempty Action]
    (prior : FinDist State) (observe : State → Signal) (utility : State → Action → ℝ) :
    ∃ policy, IsBayesOptimal prior observe utility policy := by
  classical
  choose best maximal using fun signal => Finite.exists_max
    (fun action => localValue prior observe utility signal (FinDist.pure action))
  refine ⟨fun signal => FinDist.pure (best signal), ?_⟩
  intro signal alternative
  rw [localValue_eq_expect_pure]
  apply FinDist.expect_le_of_forall
  intro action _
  exact maximal signal action

/-- The payoff-relevant fact can be recovered from the observation wherever
the prior has positive mass. -/
def Determines (prior : FinDist State) (observe : State → Signal) (fact : State → Fact) : Prop :=
  ∀ first ∈ prior.support, ∀ second ∈ prior.support,
    observe first = observe second → fact first = fact second

theorem determines_iff_of_fullSupport (prior : FinDist State) (full : prior.FullSupport)
    (observe : State → Signal) (fact : State → Fact) :
    Determines prior observe fact ↔
      ∀ first second, observe first = observe second → fact first = fact second := by
  exact ⟨fun determines first second => determines first (full first) second (full second),
    fun determines first _ second _ => determines first second⟩

theorem determines_iff_decoder (prior : FinDist State) (observe : State → Signal)
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

theorem report_value [DecidableEq Fact] (prior : FinDist State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → FinDist Fact) :
    value prior observe (reportUtility fact) policy =
      prior.expect fun state => (policy (observe state)).prob (fact state) := by
  rw [value_eq_expect]
  apply FinDist.expect_congr
  intro state _
  change (policy (observe state)).expect (fun report => if fact state = report then 1 else 0) = _
  rw [FinDist.expect_ite_eq, mul_one]

theorem report_value_le_one [DecidableEq Fact] (prior : FinDist State)
    (observe : State → Signal) (fact : State → Fact) (policy : Signal → FinDist Fact) :
    value prior observe (reportUtility fact) policy ≤ 1 := by
  rw [report_value]
  exact FinDist.expect_le_of_forall _ _ _ fun _ _ => FinDist.prob_le_one _ _

private theorem eq_pure_of_prob_one (law : FinDist Fact) (fact : Fact)
    (certain : law.prob fact = 1) : law = FinDist.pure fact := by
  symm
  apply FinDist.ext_of_prob_on_support
  intro other supported
  rw [FinDist.mem_support_pure] at supported
  subst other
  rw [FinDist.prob_pure_self, certain]

theorem report_value_eq_one_iff [DecidableEq Fact] (prior : FinDist State)
    (observe : State → Signal) (fact : State → Fact) (policy : Signal → FinDist Fact) :
    value prior observe (reportUtility fact) policy = 1 ↔
      ∀ state ∈ prior.support, policy (observe state) = FinDist.pure (fact state) := by
  rw [report_value]
  constructor
  · intro one state supported
    exact eq_pure_of_prob_one _ _ (FinDist.eq_of_expect_eq_of_le prior _ 1
      (fun _ _ => FinDist.prob_le_one _ _) one supported)
  · intro certain
    calc
      _ = prior.expect (fun _ => (1 : ℝ)) := by
        apply FinDist.expect_congr
        intro state supported
        rw [certain state supported, FinDist.prob_pure_self]
      _ = 1 := FinDist.expect_const _ _

/-- Exact classification: randomized reporting achieves certainty precisely
when an ordinary deterministic decoder exists on the prior support. -/
theorem exists_perfect_report_iff [DecidableEq Fact] (prior : FinDist State)
    (observe : State → Signal) (fact : State → Fact) :
    (∃ policy, value prior observe (reportUtility fact) policy = 1) ↔
      Determines prior observe fact := by
  constructor
  · rintro ⟨policy, perfect⟩ first firstPresent second secondPresent same
    have certain := (report_value_eq_one_iff prior observe fact policy).mp perfect
    have equal : FinDist.pure (fact first) = FinDist.pure (fact second) := by
      rw [← certain first firstPresent, ← certain second secondPresent, same]
    have member : fact first ∈ (FinDist.pure (fact second)).support := by
      rw [← equal, FinDist.mem_support_pure]
    exact FinDist.mem_support_pure.mp member
  · intro determines
    obtain ⟨decode, decodes⟩ := (determines_iff_decoder prior observe fact).mp determines
    refine ⟨fun signal => FinDist.pure (decode signal), ?_⟩
    rw [report_value_eq_one_iff]
    intro state supported
    rw [decodes state supported]

/-- Equality of the complete initialized state/report law, not only its value. -/
theorem report_value_eq_one_iff_law [DecidableEq Fact] (prior : FinDist State)
    (observe : State → Signal) (fact : State → Fact) (policy : Signal → FinDist Fact) :
    value prior observe (reportUtility fact) policy = 1 ↔
      outcomeLaw prior observe policy = prior.map (fun state => (state, fact state)) := by
  constructor
  · intro perfect
    have certain := (report_value_eq_one_iff prior observe fact policy).mp perfect
    rw [outcomeLaw, FinDist.map_eq_bind]
    apply FinDist.bind_congr
    intro state supported
    rw [certain state supported, FinDist.map_pure]
  · intro sameLaw
    rw [value, sameLaw, FinDist.expect_map]
    simp only [reportUtility, ↓reduceIte, FinDist.expect_const]

theorem bayesOptimal_report_value_eq_one [DecidableEq Fact]
    (prior : FinDist State) (observe : State → Signal) (fact : State → Fact)
    (determines : Determines prior observe fact) (policy : Signal → FinDist Fact)
    (optimal : IsBayesOptimal prior observe (reportUtility fact) policy) :
    value prior observe (reportUtility fact) policy = 1 := by
  obtain ⟨perfect, perfectValue⟩ := (exists_perfect_report_iff prior observe fact).mpr determines
  apply le_antisymm (report_value_le_one prior observe fact policy)
  rw [← perfectValue]
  exact optimal.value_le perfect

/-- Merging two positive-probability states with different payoff-relevant
facts forces a strictly positive error for every randomized abstract policy. -/
theorem report_value_lt_one_of_collision [DecidableEq Fact]
    (prior : FinDist State) (observe : State → Signal) (fact : State → Fact)
    {first second : State} (firstPresent : first ∈ prior.support)
    (secondPresent : second ∈ prior.support) (same : observe first = observe second)
    (different : fact first ≠ fact second) (policy : Signal → FinDist Fact) :
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
    (prior : FinDist State) (coarse : State → Signal) (fine : State → Fine)
    (fact : State → Fact) (fineDetermines : Determines prior fine fact)
    {first second : State} (firstPresent : first ∈ prior.support)
    (secondPresent : second ∈ prior.support) (same : coarse first = coarse second)
    (different : fact first ≠ fact second) (source : Signal → FinDist Fact)
    (target : Fine → FinDist Fact)
    (targetOptimal : IsBayesOptimal prior fine (reportUtility fact) target) :
    (outcomeLaw prior fine target).map (fun result => (fact result.1, result.2)) ≠
      (outcomeLaw prior coarse source).map (fun result => (fact result.1, result.2)) := by
  intro sameLaw
  have sourceBound := report_value_lt_one_of_collision prior coarse fact
    firstPresent secondPresent same different source
  have targetValue := bayesOptimal_report_value_eq_one prior fine fact
    fineDetermines target targetOptimal
  have sameValue := congrArg (fun law : FinDist (Fact × Fact) =>
    law.expect (fun result => if result.1 = result.2 then (1 : ℝ) else 0)) sameLaw
  simp only [FinDist.expect_map] at sameValue
  change value prior fine (reportUtility fact) target =
    value prior coarse (reportUtility fact) source at sameValue
  linarith

/-- A finite reporting experiment has a source optimum, but no informed
target optimum can match its fact/report law after a relevant observation merge.
This does not quantify over general protocol sequential equilibria. -/
theorem exists_optimal_no_report_law_match [Finite Fact] [Nonempty Fact] [DecidableEq Fact]
    (prior : FinDist State) (coarse : State → Signal) (fine : State → Fine)
    (fact : State → Fact) (fineDetermines : Determines prior fine fact)
    {first second : State} (firstPresent : first ∈ prior.support)
    (secondPresent : second ∈ prior.support) (same : coarse first = coarse second)
    (different : fact first ≠ fact second) :
    ∃ source : Signal → FinDist Fact,
      IsBayesOptimal prior coarse (reportUtility fact) source ∧
      ∀ target : Fine → FinDist Fact,
        IsBayesOptimal prior fine (reportUtility fact) target →
          (outcomeLaw prior fine target).map (fun result => (fact result.1, result.2)) ≠
            (outcomeLaw prior coarse source).map (fun result => (fact result.1, result.2)) := by
  obtain ⟨source, optimal⟩ := exists_bayesOptimal prior coarse (reportUtility fact)
  exact ⟨source, optimal, fun target targetOptimal => no_optimal_report_law_match
    prior coarse fine fact fineDetermines firstPresent secondPresent same different
      source target targetOptimal⟩

end GameTheory.DecisionExperiment

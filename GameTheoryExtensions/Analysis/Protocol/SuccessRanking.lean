/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.CopiedSiteLimit

/-! # Local values that depend on a success probability alone

At an information site, installing a local law yields a law over observed
outcomes (`GameTheory.Protocol.InformationModel.localLaw`) and the expected
utility of its player (`GameTheory.Protocol.InformationModel.localValue`); the
local gain is the comparison used by the limit obligations of
`GameTheory.Protocol.InformationModel.PooledLimitCertificate`
(`GameTheory.Protocol.InformationModel.localGain`). With finitely many
histories and decisions taken once where it matters, both are affine in the
local law (`GameTheory.Protocol.InformationModel.localValue_bind`,
`GameTheory.Protocol.InformationModel.localGain_bind`).

Fix a set of failed outcomes on which the player receives a fixed payoff. The
local value splits into the expected payoff on the successful outcomes and the
failure probability times the fixed payoff
(`GameTheory.Protocol.InformationModel.localValue_eq_successValue_add`). If the
successful part is, up to an error, the success probability times a
continuation value that does not depend on the local law, then the local value
is `P * W + (1 - P) * a` up to that error
(`GameTheory.Protocol.InformationModel.localValue_near_success`), and laws are
ranked by their success probabilities alone, up to vanishing errors, as soon
as the fixed payoff is at most the continuation value up to the error
(`GameTheory.Math.Probability.successValue_le`,
`GameTheory.Protocol.InformationModel.localValue_le_of_failure_le`). The
site-level hypotheses follow from the same statements at every history of the
site's belief when the failure probability is common to those histories
(`GameTheory.Protocol.InformationModel.localFailure_successValue_of_histories`,
`GameTheory.Protocol.InformationModel.localFailure_near_of_histories`).

For pooled agents sharing component weights, a part that ranks nearly best
for every member makes every member nearly rational
(`GameTheory.Protocol.InformationModel.memberGain_le_of_common_best`), and a
part that maximizes a success probability common to the pool
(`GameTheory.Protocol.InformationModel.failure_le_of_common`), with the value
of each member's site one-dimensional in it, gives the member-rationality
obligation of a pooled limit certificate on those pools
(`GameTheory.Protocol.InformationModel.memberRational_of_success`). Single
choices marked for comparison with a best part whose component fails least
give the local-comparison obligation
(`GameTheory.Protocol.InformationModel.localComparisons_of_success`). Failure
probabilities are local values of the failure indicator, so mixing in a law
with a small weight raises them by at most that weight
(`GameTheory.Protocol.InformationModel.localFailure_mix_le`).
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- **Ranking by success probability.** Two values that are each the mixture of
a common continuation value `W` with weight their success probability and of a
fixed payoff `a` otherwise, up to `error`, are ordered by their success
probabilities up to `slack * bound + 3 * error`, whenever `a` is at most `W` up
to `error`, the gap `W - a` is at most `bound`, and the success probability of
the first exceeds that of the second by at most `slack`. -/
theorem successValue_le {success best continuation excluded error slack bound value
      bestValue : ℝ}
    (valueNear : |value - (success * continuation + (1 - success) * excluded)| ≤ error)
    (bestNear : |bestValue - (best * continuation + (1 - best) * excluded)| ≤ error)
    (success_nonneg : 0 ≤ success) (best_le_one : best ≤ 1)
    (ranked : success ≤ best + slack) (slack_nonneg : 0 ≤ slack)
    (excluded_le : excluded ≤ continuation + error) (gap_le : continuation - excluded ≤ bound)
    (bound_nonneg : 0 ≤ bound) :
    value ≤ bestValue + slack * bound + 3 * error := by
  have valueUpper := (abs_le.mp valueNear).2
  have bestLower := (abs_le.mp bestNear).1
  have product : (success - best) * (continuation - excluded) ≤ slack * bound + error := by
    have slackBound : 0 ≤ slack * bound := mul_nonneg slack_nonneg bound_nonneg
    rcases le_or_gt 0 (continuation - excluded) with nonnegative | negative
    · have first : (success - best) * (continuation - excluded) ≤
          slack * (continuation - excluded) :=
        mul_le_mul_of_nonneg_right (by linarith) nonnegative
      have second : slack * (continuation - excluded) ≤ slack * bound :=
        mul_le_mul_of_nonneg_left gap_le slack_nonneg
      have errorNonneg : 0 ≤ error := (abs_nonneg _).trans valueNear
      linarith
    · have : (success - best + 1) * (continuation - excluded) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) negative.le
      nlinarith
  nlinarith

end GameTheory.Math.Probability

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {T : ExecutionProtocol Player} {N : InformationModel T}
  [∀ who, DecidableEq (N.InfoState who)] {Outcome : Type*}

section Values

variable (fuel : Nat) (observe : T.History → Outcome) (utility : Outcome → Player → ℝ)
  (assessment : N.BehavioralAssessment) {who : Player} (site : N.InformationSite who)

/-- The law of play from one history of a site when its player installs a
local law there, cut off after `fuel` steps. -/
def localHistoryRun (law : PMF (N.Choice who site.1))
    (history : N.InformationHistory who site.1) : PMF T.History :=
  N.truncatedRunner fuel (Profile.update (sig := N.behavioralSignature) assessment.strategy who
    ((assessment.strategy who).withLaw site.1 law)) history.1

/-- The law of play from a site's belief when its player installs a local law
there, cut off after `fuel` steps. -/
def localRun (law : PMF (N.Choice who site.1)) : PMF T.History :=
  N.assessmentLawWith (N.truncatedRunner fuel) assessment site
    ((assessment.strategy who).withLaw site.1 law)

/-- The observed law of installing a local law at a site, from the site's
belief. -/
def localLaw (law : PMF (N.Choice who site.1)) : PMF Outcome :=
  (localRun fuel assessment site law).map observe

/-- The expected utility of installing a local law at a site. -/
def localValue (law : PMF (N.Choice who site.1)) : ℝ :=
  expect (localLaw fuel observe assessment site law) (utility · who)

/-- The local gain of a law at a site: the comparison of the limit obligations
of a pooled component family. -/
def localGain (law : PMF (N.Choice who site.1)) : ℝ :=
  let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel) observe assessment who
    (site, (assessment.strategy who).withLaw site.1 law)
  expect comparison.alternative (utility · who) - expect comparison.prescribed (utility · who)

open Classical in
/-- The probability of a failed history after installing a local law. -/
def localFailure (failed : Set T.History) (law : PMF (N.Choice who site.1)) : ℝ :=
  expect (localRun fuel assessment site law) (fun history => if history ∈ failed then 1 else 0)

open Classical in
/-- The expected utility on the successful histories after installing a local
law, zero on the failed ones. -/
def localSuccessValue (failed : Set T.History) (law : PMF (N.Choice who site.1)) : ℝ :=
  expect (localRun fuel assessment site law)
    (fun history => if history ∈ failed then 0 else utility (observe history) who)

theorem localRun_eq_bind (law : PMF (N.Choice who site.1)) :
    localRun fuel assessment site law =
      (assessment.belief who site).bind (localHistoryRun fuel assessment site law) := rfl

/-- The local value is the expected utility of the observed outcome under the
local run. -/
theorem localValue_eq_expect_localRun (law : PMF (N.Choice who site.1)) :
    localValue fuel observe utility assessment site law =
      expect (localRun fuel assessment site law)
        (fun history => utility (observe history) who) := by
  unfold localValue localLaw
  rw [expect_map]
  rfl

/-- The local gain is the value of the law minus the value of the assessed
local law. -/
theorem localGain_eq_sub (law : PMF (N.Choice who site.1)) :
    localGain fuel observe utility assessment site law =
      localValue fuel observe utility assessment site law -
        localValue fuel observe utility assessment site (assessment.strategy who site.1) := by
  simp only [localGain, localValue, localLaw, localRun, assessmentComparisonWith,
    BehavioralPolicy.withLaw_eq_self]

/-- The local gain of the assessed local law is zero. -/
theorem localGain_self :
    localGain fuel observe utility assessment site (assessment.strategy who site.1) = 0 := by
  rw [localGain_eq_sub, sub_self]

/-- The local value is the continuation value of installing the law. -/
theorem localValue_eq_continuationContext (bounded : T.BoundedHorizon fuel)
    (law : PMF (N.Choice who site.1)) :
    localValue fuel observe utility assessment site law =
      (assessment.continuationContext bounded.wellFoundedHistories site
          (fun history => utility (observe history) who)).value
        ((assessment.strategy who).withLaw site.1 law) := by
  rw [assessment.continuationContext_eq_truncated_of_bounded _ bounded]
  simp only [localValue, localLaw, localRun, expect_map]
  rfl

/-- **Local values are affine in the local law.** -/
theorem localValue_bind [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters)
    {Part : Type*} [Finite Part] (weights : PMF Part)
    (component : Part → PMF (N.Choice who site.1)) :
    localValue fuel observe utility assessment site (weights.bind component) =
      expect weights (fun part => localValue fuel observe utility assessment site
        (component part)) := by
  let := Fintype.ofFinite T.History
  have : Finite (N.Choice who site.1) :=
    N.finite_choice_of_played (N.site_mem_playedInformation site)
  simp only [localValue_eq_continuationContext fuel observe utility assessment site bounded,
    BehavioralAssessment.continuationContext_withLaw_eq_expect actsOnce]
  exact expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)

/-- **Local gains are affine in the local law.** -/
theorem localGain_bind [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters)
    {Part : Type*} [Finite Part] (weights : PMF Part)
    (component : Part → PMF (N.Choice who site.1)) :
    localGain fuel observe utility assessment site (weights.bind component) =
      expect weights (fun part => localGain fuel observe utility assessment site
        (component part)) := by
  simp only [localGain_eq_sub, localValue_bind fuel observe utility assessment site bounded
    actsOnce]
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_constant]

theorem localFailure_nonneg (failed : Set T.History) (law : PMF (N.Choice who site.1)) :
    0 ≤ localFailure fuel assessment site failed law := by
  classical
  refine expect_nonneg _ _ fun outcome _ => ?_
  split <;> norm_num

theorem localFailure_le_one [Finite T.History] (failed : Set T.History)
    (law : PMF (N.Choice who site.1)) :
    localFailure fuel assessment site failed law ≤ 1 := by
  classical
  unfold localFailure
  exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun _ _ => by
    split <;> norm_num

/-- **Failure pays a fixed payoff.** If the player receives `excluded` on every
failed outcome, the local value is the successful part plus the failure
probability times `excluded`. -/
theorem localValue_eq_successValue_add [Finite T.History] (failed : Set T.History) (excluded : ℝ)
    (pays : ∀ history ∈ failed, utility (observe history) who = excluded)
    (law : PMF (N.Choice who site.1)) :
    localValue fuel observe utility assessment site law =
      localSuccessValue fuel observe utility assessment site failed law +
        localFailure fuel assessment site failed law * excluded := by
  classical
  rw [localValue_eq_expect_localRun]
  unfold localSuccessValue localFailure
  have pointwise : (fun history => utility (observe history) who) = fun history =>
      (if history ∈ failed then 0 else utility (observe history) who) +
        excluded * (if history ∈ failed then (1 : ℝ) else 0) := by
    funext history
    split
    · rename_i member
      rw [pays _ member]
      ring
    · ring
  rw [pointwise, expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_const_mul, mul_comm excluded]

/-- **The local value is one-dimensional.** If failure pays `excluded` and the
successful part is the success probability times a continuation value
`continuation` up to `error`, the local value is the mixture of `continuation`
with weight the success probability and of `excluded` otherwise, up to
`error`. -/
theorem localValue_near_success [Finite T.History] (failed : Set T.History) (excluded : ℝ)
    (pays : ∀ history ∈ failed, utility (observe history) who = excluded)
    (continuation error : ℝ) (law : PMF (N.Choice who site.1))
    (successNear : |localSuccessValue fuel observe utility assessment site failed law -
      (1 - localFailure fuel assessment site failed law) * continuation| ≤ error) :
    |localValue fuel observe utility assessment site law -
      ((1 - localFailure fuel assessment site failed law) * continuation +
        (1 - (1 - localFailure fuel assessment site failed law)) * excluded)| ≤
      error := by
  rw [localValue_eq_successValue_add fuel observe utility assessment site failed excluded pays]
  convert successNear using 2
  ring

/-- **Laws are ranked by success probability.** At a site where failure pays
`excluded` and the successful part of two laws is their success probability
times a common continuation value up to `error`, a law whose success
probability exceeds that of `best` by at most `slack` has value at most that
of `best` plus `slack * bound + 3 * error`, provided `excluded` is at most the
continuation value up to `error` and the gap is at most `bound`. -/
theorem localValue_le_of_failure_le [Finite T.History] (failed : Set T.History) (excluded : ℝ)
    (pays : ∀ history ∈ failed, utility (observe history) who = excluded)
    (continuation error slack bound : ℝ) (law best : PMF (N.Choice who site.1))
    (lawNear : |localSuccessValue fuel observe utility assessment site failed law -
      (1 - localFailure fuel assessment site failed law) * continuation| ≤ error)
    (bestNear : |localSuccessValue fuel observe utility assessment site failed best -
      (1 - localFailure fuel assessment site failed best) * continuation| ≤ error)
    (ranked : localFailure fuel assessment site failed best ≤
      localFailure fuel assessment site failed law + slack)
    (slack_nonneg : 0 ≤ slack) (excluded_le : excluded ≤ continuation + error)
    (gap_le : continuation - excluded ≤ bound) (bound_nonneg : 0 ≤ bound) :
    localValue fuel observe utility assessment site law ≤
      localValue fuel observe utility assessment site best + slack * bound + 3 * error :=
  successValue_le
    (localValue_near_success fuel observe utility assessment site failed excluded pays
      continuation error law lawNear)
    (localValue_near_success fuel observe utility assessment site failed excluded pays
      continuation error best bestNear)
    (by linarith [localFailure_le_one fuel assessment site failed law])
    (by linarith [localFailure_nonneg fuel assessment site failed best])
    (by linarith) slack_nonneg excluded_le gap_le bound_nonneg

/-- The ranking of `localValue_le_of_failure_le`, for local gains. -/
theorem localGain_le_of_failure_le [Finite T.History] (failed : Set T.History) (excluded : ℝ)
    (pays : ∀ history ∈ failed, utility (observe history) who = excluded)
    (continuation error slack bound : ℝ) (law best : PMF (N.Choice who site.1))
    (lawNear : |localSuccessValue fuel observe utility assessment site failed law -
      (1 - localFailure fuel assessment site failed law) * continuation| ≤ error)
    (bestNear : |localSuccessValue fuel observe utility assessment site failed best -
      (1 - localFailure fuel assessment site failed best) * continuation| ≤ error)
    (ranked : localFailure fuel assessment site failed best ≤
      localFailure fuel assessment site failed law + slack)
    (slack_nonneg : 0 ≤ slack) (excluded_le : excluded ≤ continuation + error)
    (gap_le : continuation - excluded ≤ bound) (bound_nonneg : 0 ≤ bound) :
    localGain fuel observe utility assessment site law ≤
      localGain fuel observe utility assessment site best + slack * bound + 3 * error := by
  rw [localGain_eq_sub, localGain_eq_sub]
  linarith [localValue_le_of_failure_le fuel observe utility assessment site failed excluded pays
    continuation error slack bound law best lawNear bestNear ranked slack_nonneg excluded_le gap_le
    bound_nonneg]

/-- An expectation under the site's local run averages, over the belief, the
expectations from each history. -/
theorem expect_localRun [Finite T.History] (law : PMF (N.Choice who site.1))
    (payoff : T.History → ℝ) :
    expect (localRun fuel assessment site law) payoff =
      expect (assessment.belief who site) (fun history =>
        expect (localHistoryRun fuel assessment site law history) payoff) := by
  rw [localRun_eq_bind, expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]

/-- A belief average of quantities within `error` of their targets is within
`error` of the average target. -/
private theorem expect_near_of_near {α : Type*} [Finite α] (belief : PMF α) (value target : α → ℝ)
    (error : ℝ) (near : ∀ point ∈ belief.support, |value point - target point| ≤ error) :
    |expect belief value - expect belief target| ≤ error := by
  rw [← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  have upper := expect_le_const belief _ (payoffIntegrable_of_finite _ _) error
    fun point supported => (abs_le.mp (near point supported)).2
  have lower := expect_mono (μ := belief) (f := fun _ => -error)
    (fun point supported => (abs_le.mp (near point supported)).1)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_constant] at lower
  exact abs_le.mpr ⟨lower, upper⟩

open Classical in
/-- **A failure probability common to the histories is the site's.** If the
failure probability after installing a law from every history of the site's
belief is within `drift` of `failure`, so is the site's. -/
theorem localFailure_near_of_histories [Finite T.History] (failed : Set T.History)
    (law : PMF (N.Choice who site.1)) (failure drift : ℝ)
    (historyFailure : ∀ history ∈ (assessment.belief who site).support,
      |expect (localHistoryRun fuel assessment site law history)
        (fun history => if history ∈ failed then 1 else 0) - failure| ≤ drift) :
    |localFailure fuel assessment site failed law - failure| ≤ drift := by
  have near := expect_near_of_near (assessment.belief who site) _ (fun _ => failure) drift
    historyFailure
  rwa [expect_constant, ← expect_localRun] at near

open Classical in
/-- **From histories to the site.** If every history of the site's belief has
the same failure probability `failure` after installing a law, and its
successful part is `1 - failure` times its own continuation value up to
`error`, then the site has failure probability `failure` and its successful
part is `1 - failure` times the belief's average continuation value up to
`error`. -/
theorem localFailure_successValue_of_histories [Finite T.History] (failed : Set T.History)
    (law : PMF (N.Choice who site.1)) (failure error : ℝ)
    (continuation : N.InformationHistory who site.1 → ℝ)
    (historyFailure : ∀ history ∈ (assessment.belief who site).support,
      expect (localHistoryRun fuel assessment site law history)
        (fun history => if history ∈ failed then 1 else 0) = failure)
    (historySuccess : ∀ history ∈ (assessment.belief who site).support,
      |expect (localHistoryRun fuel assessment site law history)
          (fun history => if history ∈ failed then 0 else utility (observe history) who) -
        (1 - failure) * continuation history| ≤ error) :
    localFailure fuel assessment site failed law = failure ∧
      |localSuccessValue fuel observe utility assessment site failed law -
        (1 - failure) * expect (assessment.belief who site) continuation| ≤ error := by
  classical
  refine ⟨?_, ?_⟩
  · unfold localFailure
    rw [expect_localRun, expect_congr_on_support historyFailure, expect_constant]
  · unfold localSuccessValue
    rw [expect_localRun, ← expect_const_mul]
    exact expect_near_of_near _ _ _ error historySuccess

/-- **Local values of a mixture.** -/
theorem localValue_mix [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (le_one : weight ≤ 1) (first second : PMF (N.Choice who site.1)) :
    localValue fuel observe utility assessment site (mix weight nonnegative le_one first second) =
      weight * localValue fuel observe utility assessment site first +
        (1 - weight) * localValue fuel observe utility assessment site second := by
  let := Fintype.ofFinite T.History
  have : Finite (N.Choice who site.1) :=
    N.finite_choice_of_played (N.site_mem_playedInformation site)
  simp only [localValue_eq_continuationContext fuel observe utility assessment site bounded,
    BehavioralAssessment.continuationContext_withLaw_eq_expect actsOnce]
  exact expect_mix _ _ _ _ _ _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

open Classical in
/-- The failure probability is the local value of the failure indicator, the
history being observed as itself. -/
theorem localFailure_eq_localValue (failed : Set T.History) (law : PMF (N.Choice who site.1)) :
    localFailure fuel assessment site failed law =
      localValue fuel id (fun history (_ : Player) => if history ∈ failed then 1 else 0)
        assessment site law := by
  rw [localValue_eq_expect_localRun]
  rfl

/-- Mixing in a law with weight `weight` raises the failure probability by at
most `weight`. -/
theorem localFailure_mix_le [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters) (failed : Set T.History) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (le_one : weight ≤ 1) (first second : PMF (N.Choice who site.1)) :
    localFailure fuel assessment site failed (mix weight nonnegative le_one first second) ≤
      weight + localFailure fuel assessment site failed second := by
  classical
  have mixed := localValue_mix fuel id
    (fun history (_ : Player) => if history ∈ failed then (1 : ℝ) else 0) assessment site bounded
    actsOnce weight nonnegative le_one first second
  rw [← localFailure_eq_localValue, ← localFailure_eq_localValue,
    ← localFailure_eq_localValue] at mixed
  rw [mixed]
  have firstLe := localFailure_le_one fuel assessment site failed first
  have secondNonneg := localFailure_nonneg fuel assessment site failed second
  nlinarith

/-- **Failure probabilities are affine in the local law.** -/
theorem localFailure_bind [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters) (failed : Set T.History) {Part : Type*} [Finite Part]
    (weights : PMF Part) (component : Part → PMF (N.Choice who site.1)) :
    localFailure fuel assessment site failed (weights.bind component) =
      expect weights (fun part => localFailure fuel assessment site failed (component part)) := by
  classical
  simp only [localFailure_eq_localValue]
  exact localValue_bind fuel id _ assessment site bounded actsOnce weights component

/-- **Failure under a mass bound.** If a law gives every choice at least
`1 - weight` times the mass a main law gives it, it fails with probability at
most the main law's plus `weight`. -/
theorem localFailure_le_of_mass [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters) (failed : Set T.History) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (law main : PMF (N.Choice who site.1))
    (mass : ∀ choice, (1 - weight) * (main choice).toReal ≤ (law choice).toReal) :
    localFailure fuel assessment site failed law ≤
      weight + localFailure fuel assessment site failed main := by
  let := Fintype.ofFinite T.History
  have : Finite (N.Choice who site.1) :=
    N.finite_choice_of_played (N.site_mem_playedInformation site)
  let := Fintype.ofFinite (N.Choice who site.1)
  have pure (law : PMF (N.Choice who site.1)) :
      localFailure fuel assessment site failed law =
        ∑ choice, (law choice).toReal *
          localFailure fuel assessment site failed (PMF.pure choice) := by
    conv_lhs => rw [← PMF.bind_pure law]
    rw [localFailure_bind fuel assessment site bounded actsOnce failed law PMF.pure, expect_eq_sum]
  rw [pure law, pure main]
  have lawSum : ∑ choice, (law choice).toReal = 1 := by
    have total := expect_eq_sum law (fun _ => (1 : ℝ))
    rw [expect_constant] at total
    simpa using total.symm
  have mainSum : ∑ choice, (main choice).toReal = 1 := by
    have total := expect_eq_sum main (fun _ => (1 : ℝ))
    rw [expect_constant] at total
    simpa using total.symm
  have split : ∑ choice, (law choice).toReal *
        localFailure fuel assessment site failed (PMF.pure choice) ≤
      ∑ choice, (((law choice).toReal - (1 - weight) * (main choice).toReal) +
        (main choice).toReal * localFailure fuel assessment site failed (PMF.pure choice)) := by
    refine Finset.sum_le_sum fun choice _ => ?_
    have low := localFailure_nonneg fuel assessment site failed (PMF.pure choice)
    have high := localFailure_le_one fuel assessment site failed (PMF.pure choice)
    have gap := mass choice
    have mainNonneg : 0 ≤ (main choice).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right gap low,
      mul_nonneg (mul_nonneg nonnegative mainNonneg) low,
      mul_le_mul_of_nonneg_left high (sub_nonneg.mpr gap)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, lawSum, mainSum] at split
  linarith

/-- **A law close to a reliable main law fails least.** If a law gives every
choice at least `1 - weight` times the mass of a main law that fails with
probability at most `later`, it fails at most as often as any law, up to
`weight + later`. -/
theorem localFailure_le_add_of_mass [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters) (failed : Set T.History) (weight later : ℝ)
    (nonnegative : 0 ≤ weight) (law main : PMF (N.Choice who site.1))
    (mass : ∀ choice, (1 - weight) * (main choice).toReal ≤ (law choice).toReal)
    (mainFails : localFailure fuel assessment site failed main ≤ later)
    (other : PMF (N.Choice who site.1)) :
    localFailure fuel assessment site failed law ≤
      localFailure fuel assessment site failed other + (weight + later) := by
  have := localFailure_le_of_mass fuel assessment site bounded actsOnce failed weight nonnegative
    law main mass
  have := localFailure_nonneg fuel assessment site failed other
  linarith

/-- **Sure failure ranks last.** A law that fails surely fails at least as
often as every law, as every choice of a player whose event is doomed does. -/
theorem localFailure_le_of_sure_failure [Finite T.History] (failed : Set T.History)
    (law other : PMF (N.Choice who site.1))
    (sure : localFailure fuel assessment site failed other = 1) :
    localFailure fuel assessment site failed law ≤
      localFailure fuel assessment site failed other := by
  rw [sure]
  exact localFailure_le_one fuel assessment site failed law

/-- A law under which every reached history from the site's belief has failed
fails surely. -/
theorem localFailure_eq_one_of_support (failed : Set T.History)
    (law : PMF (N.Choice who site.1))
    (sure : ∀ history ∈ (localRun fuel assessment site law).support, history ∈ failed) :
    localFailure fuel assessment site failed law = 1 := by
  classical
  unfold localFailure
  rw [expect_congr_on_support (g := fun _ => 1) fun history member => by
    simp only [sure history member, ↓reduceIte], expect_constant]

end Values

section Pooled

variable [Fintype T.History] {Outcome : Type*} (fuel : Nat) (bounded : T.BoundedHorizon fuel)
  (targetRecall : N.DecisionRecall) (observe : T.History → Outcome)
  (utility : Outcome → Player → ℝ) (fallback : ∀ who, N.Policy who)
  {Pool : Type*} (pool : N.InformationAgent N.playedInformation → Pool)
  {Part : Pool → Type*} [∀ p, Finite (Part p)]

open Classical in
/-- **Members sharing a nearly best part are nearly rational.** Suppose the
agents of a played assessment mix components with the common weights of their
pools, the weights are optimal for the sum of the members' local gains, and
one part of the pool `p` is within `error` of the best part at every member's
site. Then every member's gain from every mixture of its components is at most
the number of agents times `error`. -/
theorem memberGain_le_of_common_best [DecidableEq Pool] (actsOnce : N.ActsOnceWhereItMatters)
    (component : ∀ agent, Part (pool agent) →
      PMF ((N.agentForm fallback bounded.wellFoundedHistories).sig.Strategy agent))
    (weights : ∀ p, PMF (Part p)) (assessment : N.BehavioralAssessment)
    (played : assessment.strategy = N.agentBehavior N.playedInformation fallback
      fun agent => (weights (pool agent)).bind (component agent))
    (pooled : ∀ (alternative : ∀ p, PMF (Part p)) p,
      ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
        (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
          let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
            observe assessment agent.1
            (⟨agent.2.1, decision⟩, (assessment.strategy agent.1).withLaw agent.2.1
              ((alternative (pool agent)).bind (component agent)))
          expect comparison.alternative (utility · agent.1) -
            expect comparison.prescribed (utility · agent.1)
        else 0) ≤ 0)
    (p : Pool) (best : ∀ p, Part p) (error : ℝ)
    (nearBest : ∀ (agent : N.InformationAgent N.playedInformation), pool agent = p →
      ∀ (decision : N.IsDecisionInfo agent.1 agent.2.1) part,
      localGain fuel observe utility assessment (who := agent.1) ⟨agent.2.1, decision⟩
          (component agent part) ≤
        localGain fuel observe utility assessment (who := agent.1) ⟨agent.2.1, decision⟩
          (component agent (best (pool agent))) + error) :
    ∀ who (site : N.InformationSite who), pool (N.agentAt site) = p →
      ∀ alternative : PMF (Part (pool (N.agentAt site))),
        localGain fuel observe utility assessment site
            (alternative.bind (component (N.agentAt site))) ≤
          Fintype.card (N.InformationAgent N.playedInformation) * error := by
  classical
  intro who site inPool alternative
  subst p
  let gainAt (agent : N.InformationAgent N.playedInformation)
      (decision : N.IsDecisionInfo agent.1 agent.2.1) (law : PMF (N.Choice agent.1 agent.2.1)) :=
    localGain fuel observe utility assessment ⟨agent.2.1, decision⟩ law
  -- At the assessed weights each member's gain is zero, so the best part loses at most `error`.
  have bestLower (agent : N.InformationAgent N.playedInformation)
      (inPool : pool agent = pool (N.agentAt site))
      (decision : N.IsDecisionInfo agent.1 agent.2.1) :
      -error ≤ gainAt agent decision (component agent (best (pool agent))) := by
    have current : (weights (pool agent)).bind (component agent) =
        assessment.strategy agent.1 agent.2.1 := by
      rw [played]
      exact (N.agentBehavior_at N.playedInformation fallback
        (fun agent => (weights (pool agent)).bind (component agent)) agent).symm
    have zero := localGain_self fuel observe utility assessment
      (who := agent.1) ⟨agent.2.1, decision⟩
    have mixture := localGain_bind fuel observe utility assessment
      (who := agent.1) ⟨agent.2.1, decision⟩ bounded actsOnce
      (weights (pool agent)) (component agent)
    change localGain fuel observe utility assessment ⟨agent.2.1, decision⟩
      ((weights (pool agent)).bind (component agent)) = _ at mixture
    rw [current, zero] at mixture
    have upper := expect_le_const (weights (pool agent)) _ (payoffIntegrable_of_finite _ _) _
      fun part _ => nearBest agent inPool decision part
    rw [← mixture] at upper
    exact neg_le_iff_add_nonneg.mpr (by simpa [gainAt] using upper)
  have errorNonnegative : 0 ≤ error := by
    have := nearBest (N.agentAt site) rfl site.2 (best (pool (N.agentAt site)))
    linarith
  -- The pool's sum at the common best part bounds the chosen member's gain there.
  let chosen := N.agentAt site
  let p := pool chosen
  have atBest := pooled (fun q => PMF.pure (best q)) p
  have term (agent : N.InformationAgent N.playedInformation) :
      (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
          let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
            observe assessment agent.1
            (⟨agent.2.1, decision⟩, (assessment.strategy agent.1).withLaw agent.2.1
              ((PMF.pure (best (pool agent))).bind (component agent)))
          expect comparison.alternative (utility · agent.1) -
            expect comparison.prescribed (utility · agent.1)
        else 0) =
        if decision : N.IsDecisionInfo agent.1 agent.2.1 then
          gainAt agent decision (component agent (best (pool agent))) else 0 := by
    split
    · rw [PMF.pure_bind]
      rfl
    · rfl
  simp only [term] at atBest
  have present : chosen ∈ Finset.univ.filter (fun agent => pool agent = p) := by simp [p]
  rw [← Finset.add_sum_erase _ _ present] at atBest
  have others : -(((Finset.univ.filter (fun agent => pool agent = p)).erase chosen).card *
      error) ≤ ∑ agent ∈ (Finset.univ.filter (fun agent => pool agent = p)).erase chosen,
        (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
          gainAt agent decision (component agent (best (pool agent))) else 0) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun agent member => ?_
    split
    · exact bestLower agent (Finset.mem_filter.mp (Finset.mem_of_mem_erase member)).2 _
    · exact neg_nonpos.mpr errorNonnegative
  have chosenTerm : (if decision : N.IsDecisionInfo chosen.1 chosen.2.1 then
      gainAt chosen decision (component chosen (best (pool chosen))) else 0) =
      gainAt chosen site.2 (component chosen (best (pool chosen))) := dite_eq_left site.2
  rw [chosenTerm] at atBest
  have cardLe : ((Finset.univ.filter (fun agent => pool agent = p)).erase chosen).card + 1 ≤
      Fintype.card (N.InformationAgent N.playedInformation) := by
    rw [Finset.card_erase_of_mem present]
    have := Finset.card_le_univ (Finset.univ.filter (fun agent => pool agent = p))
    have := Finset.card_pos.mpr ⟨chosen, present⟩
    omega
  have cardLeReal : (((Finset.univ.filter (fun agent => pool agent = p)).erase chosen).card : ℝ) +
      1 ≤ Fintype.card (N.InformationAgent N.playedInformation) := by
    exact_mod_cast cardLe
  -- Every mixture of the chosen member's components is within `error` of the best part.
  have mixture := localGain_bind fuel observe utility assessment site bounded actsOnce
    alternative (component chosen)
  have upper := expect_le_const alternative _ (payoffIntegrable_of_finite _ _) _
    fun part _ => nearBest chosen rfl site.2 part
  change localGain fuel observe utility assessment site (alternative.bind (component chosen)) ≤ _
  rw [mixture]
  refine upper.trans ?_
  change gainAt chosen site.2 (component chosen (best (pool chosen))) + error ≤ _
  nlinarith

open Classical in
/-- **Member rationality from a common success ranking.** Fix the delivery
pools. Suppose that, for every weights family the pooled completion may choose,
the value of each member site of a delivery pool is one-dimensional in a
success probability: failure pays the player a fixed payoff, and the
successful part of each component is its success probability times a
continuation value of the site up to `error n`. Suppose also that the fixed
payoff is at most that continuation value up to `error n`, the gap is at most
`bound`, and a best part of the pool at index `n`, which may depend on the
weights family, fails with probability at most that of every other part at
every member's site up to `slack n`, as when the success probability of each
part is common to the pool and the best part maximizes it
(`failure_le_of_common`). If `error` and `slack` vanish and the members of the
other pools are rational up to a vanishing error, the member-rationality
obligation of a pooled limit certificate holds. -/
theorem memberRational_of_success [Finite Pool] [DecidableEq Pool]
    (component : ℕ → ∀ agent, Part (pool agent) →
      PMF ((N.agentForm fallback bounded.wellFoundedHistories).sig.Strategy agent))
    (delivery : Set Pool)
    (failed : N.InformationAgent N.playedInformation → Set T.History) (excluded : Player → ℝ)
    (pays : ∀ agent, ∀ history ∈ failed agent, utility (observe history) agent.1 =
      excluded agent.1)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (oneDimensional : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → N.InformationAgent N.playedInformation → ℝ)
        (best : ℕ → ∀ p, Part p) (error slack : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ slack n) ∧
        ∀ n (agent : N.InformationAgent N.playedInformation), pool agent ∈ delivery →
          ∀ decision : N.IsDecisionInfo agent.1 agent.2.1,
          excluded agent.1 ≤ continuation n agent + error n ∧
          continuation n agent - excluded agent.1 ≤ bound ∧
          (∀ part, |localSuccessValue fuel observe utility (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent) (component n agent part) -
            (1 - localFailure fuel (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent) (component n agent part)) * continuation n agent| ≤ error n) ∧
          ∀ part, localFailure fuel (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent) (component n agent (best n (pool agent))) ≤
            localFailure fuel (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent) (component n agent part) + slack n)
    (otherMembers : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), pool (N.agentAt site) ∉ delivery →
          ∀ alternative : PMF (Part (pool (N.agentAt site))),
          let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
            observe (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (component n (N.agentAt site))))
          expect comparison.alternative (utility · who) -
            expect comparison.prescribed (utility · who) ≤ otherError n) :
    ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who)
          (alternative : PMF (Part (pool (N.agentAt site)))),
          let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
            observe (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (component n (N.agentAt site))))
          expect comparison.alternative (utility · who) -
            expect comparison.prescribed (utility · who) ≤ memberError n := by
  intro weights targetSequence played mixed bayes pooled
  obtain ⟨continuation, best, error, slack, errorVanishes, slackVanishes, slack_nonneg,
    facts⟩ := oneDimensional weights targetSequence played mixed bayes
  obtain ⟨otherError, otherVanishes, otherBound⟩ :=
    otherMembers weights targetSequence played mixed bayes pooled
  let deliveryError (n : ℕ) : ℝ :=
    Fintype.card (N.InformationAgent N.playedInformation) * (slack n * bound + 3 * error n)
  have deliveryVanishes : Tendsto deliveryError atTop (nhds 0) := by
    have := ((slackVanishes.mul_const bound).add (errorVanishes.const_mul 3)).const_mul
      (Fintype.card (N.InformationAgent N.playedInformation) : ℝ)
    rwa [zero_mul, mul_zero, zero_add, mul_zero] at this
  refine ⟨fun n => max (deliveryError n) (otherError n), by
    simpa using deliveryVanishes.max otherVanishes, fun n who site alternative => ?_⟩
  by_cases inDelivery : pool (N.agentAt site) ∈ delivery
  · refine le_trans ?_ (le_max_left _ _)
    exact memberGain_le_of_common_best fuel bounded observe utility fallback pool
      targetRecall.actsOnceWhereItMatters (component n) (weights n) (targetSequence n) (played n)
      (pooled n) (pool (N.agentAt site)) (best n) (slack n * bound + 3 * error n)
      (fun agent inPool decision part => by
        obtain ⟨excluded_le, gap_le, near, ranked⟩ :=
          facts n agent (inPool ▸ inDelivery) decision
        have := localGain_le_of_failure_le fuel observe utility (targetSequence n)
          (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent) (excluded agent.1)
          (pays agent) (continuation n agent) (error n) (slack n) bound
          (component n agent part) (component n agent (best n (pool agent))) (near part)
          (near (best n (pool agent))) (ranked part) (slack_nonneg n) excluded_le gap_le
          bound_nonneg
        linarith)
      who site rfl alternative
  · exact le_trans (otherBound n who site inDelivery alternative) (le_max_right _ _)

end Pooled

section Comparisons

variable [Fintype T.History] {E : ExecutionProtocol Player} {M : InformationModel E}
  {Outcome : Type*} (sourceObserve : E.History → Outcome) (sourceFuel : Nat)
  (sourceSequence : ℕ → M.BehavioralAssessment) (fuel : Nat)
  (bounded : T.BoundedHorizon fuel) (targetRecall : N.DecisionRecall)
  (observe : T.History → Outcome) (utility : Outcome → Player → ℝ)
  (fallback : ∀ who, N.Policy who) {Pool : Type*}
  (pool : N.InformationAgent N.playedInformation → Pool) {Part : Pool → Type*}

open Classical in
/-- **Local comparisons from a success ranking.** Mark, at each site, the
single choices to be compared with a best part of the site's pool. Suppose
that, for every weights family the pooled completion may choose, at every
compared site and choice: failure pays the player a fixed payoff; the
successful part of the choice and of the component of the best part are each
their success probability times a common continuation value up to `error n`;
the fixed payoff is at most that continuation value up to `error n` and the
gap is at most `bound`; and the best part's component fails with probability at
most that of the choice up to `slack n`. If `error` and `slack` vanish and
the unmarked choices meet the comparisons on their own, the local-comparison
obligation of a pooled limit certificate holds: a marked choice gains at most
what the best part's component gains, up to a vanishing error. -/
theorem localComparisons_of_success [DecidableEq Pool]
    (component : ℕ → ∀ agent, Part (pool agent) →
      PMF ((N.agentForm fallback bounded.wellFoundedHistories).sig.Strategy agent))
    (free : Finset (N.InformationAgent N.playedInformation))
    (compared : ∀ who (site : N.InformationSite who), N.Choice who site.1 → Prop)
    (failed : N.InformationAgent N.playedInformation → Set T.History) (excluded : Player → ℝ)
    (pays : ∀ agent, ∀ history ∈ failed agent, utility (observe history) agent.1 =
      excluded agent.1)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (ranking : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → N.InformationAgent N.playedInformation → ℝ)
        (best : ℕ → ∀ p, Part p) (error slack : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ slack n) ∧
        ∀ n who (site : N.InformationSite who) (choice : N.Choice who site.1),
          N.agentAt site ∉ free → compared who site choice →
          (excluded who ≤ continuation n (N.agentAt site) + error n ∨
            failed (N.agentAt site) = ∅) ∧
          continuation n (N.agentAt site) - excluded who ≤ bound ∧
          |localSuccessValue fuel observe utility (targetSequence n) site (failed (N.agentAt site))
              (PMF.pure choice) -
            (1 - localFailure fuel (targetSequence n) site (failed (N.agentAt site))
              (PMF.pure choice)) * continuation n (N.agentAt site)| ≤ error n ∧
          |localSuccessValue fuel observe utility (targetSequence n) site (failed (N.agentAt site))
              (component n (N.agentAt site) (best n (pool (N.agentAt site)))) -
            (1 - localFailure fuel (targetSequence n) site (failed (N.agentAt site))
              (component n (N.agentAt site) (best n (pool (N.agentAt site))))) *
              continuation n (N.agentAt site)| ≤ error n ∧
          localFailure fuel (targetSequence n) site (failed (N.agentAt site))
              (component n (N.agentAt site) (best n (pool (N.agentAt site)))) ≤
            localFailure fuel (targetSequence n) site (failed (N.agentAt site)) (PMF.pure choice) +
              slack n)
    (otherComparisons : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
          ∀ choice : N.Choice who site.1, ¬ compared who site choice →
          let gain := fun law : PMF (N.Choice who site.1) =>
            let comparison := N.assessmentComparisonWith (N.truncatedRunner
                fuel) observe (targetSequence n)
              who (site, ((targetSequence n).strategy who).withLaw site.1 law)
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who)
          gain (PMF.pure choice) ≤ otherError n ∨
            (∃ alternative : PMF (Part (pool (N.agentAt site))),
              gain (PMF.pure choice) ≤
                gain (alternative.bind (component n (N.agentAt site))) + otherError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              gain (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative (utility · who) -
                    expect sourceComparison.prescribed (utility · who)) + otherError n) :
    ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
          ∀ choice : N.Choice who site.1,
          let gain := fun law : PMF (N.Choice who site.1) =>
            let comparison := N.assessmentComparisonWith (N.truncatedRunner
                fuel) observe (targetSequence n)
              who (site, ((targetSequence n).strategy who).withLaw site.1 law)
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who)
          gain (PMF.pure choice) ≤ comparisonError n ∨
            (∃ alternative : PMF (Part (pool (N.agentAt site))),
              gain (PMF.pure choice) ≤
                gain (alternative.bind (component n (N.agentAt site))) + comparisonError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              gain (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative (utility · who) -
                    expect sourceComparison.prescribed (utility · who)) + comparisonError n := by
  intro weights targetSequence played mixed bayes pooled
  obtain ⟨continuation, best, error, slack, errorVanishes, slackVanishes, slack_nonneg,
    facts⟩ := ranking weights targetSequence played mixed bayes
  obtain ⟨otherError, otherVanishes, otherBound⟩ :=
    otherComparisons weights targetSequence played mixed bayes pooled
  let rankedError (n : ℕ) : ℝ := slack n * bound + 3 * error n
  have rankedVanishes : Tendsto rankedError atTop (nhds 0) := by
    have := (slackVanishes.mul_const bound).add (errorVanishes.const_mul 3)
    rwa [zero_mul, mul_zero, zero_add] at this
  refine ⟨fun n => max (rankedError n) (otherError n), by
    simpa using rankedVanishes.max otherVanishes, fun n who site notFree choice => ?_⟩
  by_cases marked : compared who site choice
  · obtain ⟨excludedOrEmpty, gap_le, choiceNear, bestNear, ranked⟩ :=
      facts n who site choice notFree marked
    have dominated : localGain fuel observe utility (targetSequence n) site (PMF.pure choice) ≤
        localGain fuel observe utility (targetSequence n) site
          (component n (N.agentAt site) (best n (pool (N.agentAt site)))) +
          slack n * bound + 3 * error n := by
      rcases excludedOrEmpty with excluded_le | empty
      · exact localGain_le_of_failure_le fuel observe utility (targetSequence n) site
          (failed (N.agentAt site)) (excluded who) (pays (N.agentAt site))
          (continuation n (N.agentAt site)) (error n) (slack n) bound (PMF.pure choice)
          (component n (N.agentAt site) (best n (pool (N.agentAt site)))) choiceNear bestNear
          ranked (slack_nonneg n) excluded_le gap_le bound_nonneg
      · -- Without failed histories the excluded payoff enters nothing: any value pays.
        have errorNonneg : 0 ≤ error n := (abs_nonneg _).trans choiceNear
        exact localGain_le_of_failure_le fuel observe utility (targetSequence n) site
          (failed (N.agentAt site)) (continuation n (N.agentAt site))
          (by rw [empty]; exact fun _ impossible => impossible.elim)
          (continuation n (N.agentAt site)) (error n) (slack n) bound (PMF.pure choice)
          (component n (N.agentAt site) (best n (pool (N.agentAt site)))) choiceNear bestNear
          ranked (slack_nonneg n) (by linarith) (by linarith) bound_nonneg
    refine Or.inr (Or.inl ⟨PMF.pure (best n (pool (N.agentAt site))), ?_⟩)
    change localGain fuel observe utility (targetSequence n) site (PMF.pure choice) ≤
      localGain fuel observe utility (targetSequence n) site
        ((PMF.pure (best n (pool (N.agentAt site)))).bind (component n (N.agentAt site))) + _
    rw [PMF.pure_bind]
    linarith [le_max_left (rankedError n) (otherError n)]
  · have weaker := le_max_right (rankedError n) (otherError n)
    rcases otherBound n who site notFree choice marked with
      small | ⟨alternative, dominated⟩ | ⟨mixture, sourced⟩
    · exact Or.inl (small.trans weaker)
    · exact Or.inr (Or.inl ⟨alternative, dominated.trans (by linarith)⟩)
    · exact Or.inr (Or.inr ⟨mixture, sourced.trans (by linarith)⟩)

end Comparisons


/-- A failure probability within `drift` of one common to the pool, minimized
by the pool's best part, ranks the best part first at every member up to
`2 * drift`. -/
theorem failure_le_of_common {Member Pool : Type*} {Part : Pool → Type*}
    (pool : Member → Pool) (failure : (member : Member) → Part (pool member) → ℝ)
    (common : (p : Pool) → Part p → ℝ) (best : ∀ p, Part p) (drift : ℝ)
    (near : ∀ member part, |failure member part - common (pool member) part| ≤ drift)
    (minimal : ∀ p part, common p (best p) ≤ common p part) :
    ∀ member part, failure member (best (pool member)) ≤ failure member part + 2 * drift := by
  intro member part
  have first := (abs_le.mp (near member (best (pool member)))).2
  have second := (abs_le.mp (near member part)).1
  linarith [minimal (pool member) part]

end GameTheory.Protocol.InformationModel

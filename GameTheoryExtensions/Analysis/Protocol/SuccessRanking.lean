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
(`GameTheory.Protocol.InformationModel.localFailure_successValue_of_histories`).

For pooled agents sharing component weights, a part that ranks nearly best
for every member makes every member nearly rational
(`GameTheory.Protocol.InformationModel.memberGain_le_of_common_best`), and a
part that maximizes a success probability common to the pool
(`GameTheory.Protocol.InformationModel.failure_le_of_common`), with the value
of each member's site one-dimensional in it, gives the member-rationality
obligation of a pooled limit certificate on those pools
(`GameTheory.Protocol.InformationModel.memberRational_of_success`).
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

/-- The observed law of play from one history of a site when its player
installs a local law there, cut off after `fuel` steps. -/
def localHistoryLaw (law : PMF (N.Choice who site.1))
    (history : N.InformationHistory who site.1) : PMF Outcome :=
  (N.truncatedRunner fuel (Profile.update (sig := N.behavioralSignature) assessment.strategy who
    ((assessment.strategy who).withLaw site.1 law)) history.1).map observe

/-- The observed law of installing a local law at a site, from the site's
belief. -/
def localLaw (law : PMF (N.Choice who site.1)) : PMF Outcome :=
  (N.assessmentLawWith (N.truncatedRunner fuel) assessment site
    ((assessment.strategy who).withLaw site.1 law)).map observe

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
/-- The probability of a failed outcome after installing a local law. -/
def localFailure (failed : Set Outcome) (law : PMF (N.Choice who site.1)) : ℝ :=
  expect (localLaw fuel observe assessment site law)
    (fun outcome => if outcome ∈ failed then 1 else 0)

open Classical in
/-- The expected utility on the successful outcomes after installing a local
law, zero on the failed ones. -/
def localSuccessValue (failed : Set Outcome) (law : PMF (N.Choice who site.1)) : ℝ :=
  expect (localLaw fuel observe assessment site law)
    (fun outcome => if outcome ∈ failed then 0 else utility outcome who)

theorem localLaw_eq_bind (law : PMF (N.Choice who site.1)) :
    localLaw fuel observe assessment site law =
      (assessment.belief who site).bind
        (localHistoryLaw fuel observe assessment site law) := by
  unfold localLaw localHistoryLaw assessmentLawWith
  rw [PMF.map_bind]

/-- The local gain is the value of the law minus the value of the assessed
local law. -/
theorem localGain_eq_sub (law : PMF (N.Choice who site.1)) :
    localGain fuel observe utility assessment site law =
      localValue fuel observe utility assessment site law -
        localValue fuel observe utility assessment site (assessment.strategy who site.1) := by
  simp only [localGain, localValue, localLaw, assessmentComparisonWith,
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
  simp only [localValue, localLaw, expect_map]
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

theorem localFailure_nonneg (failed : Set Outcome) (law : PMF (N.Choice who site.1)) :
    0 ≤ localFailure fuel observe assessment site failed law := by
  classical
  refine expect_nonneg _ _ fun outcome _ => ?_
  split <;> norm_num

theorem localFailure_le_one [Finite T.History] (failed : Set Outcome)
    (law : PMF (N.Choice who site.1)) :
    localFailure fuel observe assessment site failed law ≤ 1 := by
  classical
  unfold localFailure localLaw
  rw [expect_map]
  exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun _ _ => by
    simp only [Function.comp_apply]
    split <;> norm_num

/-- **Failure pays a fixed payoff.** If the player receives `excluded` on every
failed outcome, the local value is the successful part plus the failure
probability times `excluded`. -/
theorem localValue_eq_successValue_add [Finite T.History] (failed : Set Outcome) (excluded : ℝ)
    (pays : ∀ outcome ∈ failed, utility outcome who = excluded)
    (law : PMF (N.Choice who site.1)) :
    localValue fuel observe utility assessment site law =
      localSuccessValue fuel observe utility assessment site failed law +
        localFailure fuel observe assessment site failed law * excluded := by
  classical
  unfold localValue localSuccessValue localFailure localLaw
  simp only [expect_map]
  have pointwise : ((utility · who) ∘ observe) = fun history =>
      ((fun outcome => if outcome ∈ failed then 0 else utility outcome who) ∘ observe)
          history +
        excluded * ((fun outcome => if outcome ∈ failed then (1 : ℝ) else 0) ∘ observe)
          history := by
    funext history
    simp only [Function.comp_apply]
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
theorem localValue_near_success [Finite T.History] (failed : Set Outcome) (excluded : ℝ)
    (pays : ∀ outcome ∈ failed, utility outcome who = excluded)
    (continuation error : ℝ) (law : PMF (N.Choice who site.1))
    (successNear : |localSuccessValue fuel observe utility assessment site failed law -
      (1 - localFailure fuel observe assessment site failed law) * continuation| ≤ error) :
    |localValue fuel observe utility assessment site law -
      ((1 - localFailure fuel observe assessment site failed law) * continuation +
        (1 - (1 - localFailure fuel observe assessment site failed law)) * excluded)| ≤
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
theorem localValue_le_of_failure_le [Finite T.History] (failed : Set Outcome) (excluded : ℝ)
    (pays : ∀ outcome ∈ failed, utility outcome who = excluded)
    (continuation error slack bound : ℝ) (law best : PMF (N.Choice who site.1))
    (lawNear : |localSuccessValue fuel observe utility assessment site failed law -
      (1 - localFailure fuel observe assessment site failed law) * continuation| ≤ error)
    (bestNear : |localSuccessValue fuel observe utility assessment site failed best -
      (1 - localFailure fuel observe assessment site failed best) * continuation| ≤ error)
    (ranked : localFailure fuel observe assessment site failed best ≤
      localFailure fuel observe assessment site failed law + slack)
    (slack_nonneg : 0 ≤ slack) (excluded_le : excluded ≤ continuation + error)
    (gap_le : continuation - excluded ≤ bound) (bound_nonneg : 0 ≤ bound) :
    localValue fuel observe utility assessment site law ≤
      localValue fuel observe utility assessment site best + slack * bound + 3 * error :=
  successValue_le
    (localValue_near_success fuel observe utility assessment site failed excluded pays
      continuation error law lawNear)
    (localValue_near_success fuel observe utility assessment site failed excluded pays
      continuation error best bestNear)
    (by linarith [localFailure_le_one fuel observe assessment site failed law])
    (by linarith [localFailure_nonneg fuel observe assessment site failed best])
    (by linarith) slack_nonneg excluded_le gap_le bound_nonneg

/-- The ranking of `localValue_le_of_failure_le`, for local gains. -/
theorem localGain_le_of_failure_le [Finite T.History] (failed : Set Outcome) (excluded : ℝ)
    (pays : ∀ outcome ∈ failed, utility outcome who = excluded)
    (continuation error slack bound : ℝ) (law best : PMF (N.Choice who site.1))
    (lawNear : |localSuccessValue fuel observe utility assessment site failed law -
      (1 - localFailure fuel observe assessment site failed law) * continuation| ≤ error)
    (bestNear : |localSuccessValue fuel observe utility assessment site failed best -
      (1 - localFailure fuel observe assessment site failed best) * continuation| ≤ error)
    (ranked : localFailure fuel observe assessment site failed best ≤
      localFailure fuel observe assessment site failed law + slack)
    (slack_nonneg : 0 ≤ slack) (excluded_le : excluded ≤ continuation + error)
    (gap_le : continuation - excluded ≤ bound) (bound_nonneg : 0 ≤ bound) :
    localGain fuel observe utility assessment site law ≤
      localGain fuel observe utility assessment site best + slack * bound + 3 * error := by
  rw [localGain_eq_sub, localGain_eq_sub]
  linarith [localValue_le_of_failure_le fuel observe utility assessment site failed excluded pays
    continuation error slack bound law best lawNear bestNear ranked slack_nonneg excluded_le gap_le
    bound_nonneg]

open Classical in
/-- **From histories to the site.** If every history of the site's belief has
the same failure probability `failure` after installing a law, and its
successful part is `1 - failure` times its own continuation value up to
`error`, then the site has failure probability `failure` and its successful
part is `1 - failure` times the belief's average continuation value up to
`error`. -/
theorem localFailure_successValue_of_histories [Finite T.History] (failed : Set Outcome)
    (law : PMF (N.Choice who site.1)) (failure error : ℝ)
    (continuation : N.InformationHistory who site.1 → ℝ)
    (historyFailure : ∀ history ∈ (assessment.belief who site).support,
      expect (localHistoryLaw fuel observe assessment site law history)
        (fun outcome => if outcome ∈ failed then 1 else 0) = failure)
    (historySuccess : ∀ history ∈ (assessment.belief who site).support,
      |expect (localHistoryLaw fuel observe assessment site law history)
          (fun outcome => if outcome ∈ failed then 0 else utility outcome who) -
        (1 - failure) * continuation history| ≤ error) :
    localFailure fuel observe assessment site failed law = failure ∧
      |localSuccessValue fuel observe utility assessment site failed law -
        (1 - failure) * expect (assessment.belief who site) continuation| ≤ error := by
  classical
  have tower (payoff : Outcome → ℝ) :
      expect (localLaw fuel observe assessment site law) payoff =
        expect (assessment.belief who site) (fun history =>
          expect (localHistoryLaw fuel observe assessment site law history) payoff) := by
    rw [localLaw_eq_bind]
    unfold localHistoryLaw
    simp only [← PMF.map_bind, expect_map]
    rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  refine ⟨?_, ?_⟩
  · unfold localFailure
    rw [tower, expect_congr_on_support historyFailure, expect_constant]
  · unfold localSuccessValue
    rw [tower, ← expect_const_mul,
      ← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
    have upper := expect_le_const (assessment.belief who site) _ (payoffIntegrable_of_finite _ _)
      error fun history supported => (abs_le.mp (historySuccess history supported)).2
    have lower := expect_mono (μ := assessment.belief who site) (f := fun _ => -error)
      (fun history supported => (abs_le.mp (historySuccess history supported)).1)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_constant] at lower
    exact abs_le.mpr ⟨lower, upper⟩

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
`bound`, and the pool's best part fails with probability at most that of every
other part at every member's site up to `slack n`, as when the success
probability of each part is common to the pool and the best part maximizes it
(`failure_le_of_common`). If `error` and `slack` vanish and the members of the
other pools are rational up to a vanishing error, the member-rationality
obligation of a pooled limit certificate holds. -/
theorem memberRational_of_success [Finite Pool] [DecidableEq Pool]
    (component : ℕ → ∀ agent, Part (pool agent) →
      PMF ((N.agentForm fallback bounded.wellFoundedHistories).sig.Strategy agent))
    (delivery : Set Pool)
    (failed : Player → Set Outcome) (excluded : Player → ℝ)
    (pays : ∀ who, ∀ outcome ∈ failed who, utility outcome who = excluded who)
    (best : ∀ p, Part p) (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (oneDimensional : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → N.InformationAgent N.playedInformation → ℝ) (error slack : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ slack n) ∧
        ∀ n (agent : N.InformationAgent N.playedInformation), pool agent ∈ delivery →
          ∀ decision : N.IsDecisionInfo agent.1 agent.2.1,
          excluded agent.1 ≤ continuation n agent + error n ∧
          continuation n agent - excluded agent.1 ≤ bound ∧
          (∀ part, |localSuccessValue fuel observe utility (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent.1) (component n agent part) -
            (1 - localFailure fuel observe (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent.1) (component n agent part)) * continuation n agent| ≤ error n) ∧
          ∀ part, localFailure fuel observe (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent.1) (component n agent (best (pool agent))) ≤
            localFailure fuel observe (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent.1) (component n agent part) + slack n)
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
  obtain ⟨continuation, error, slack, errorVanishes, slackVanishes, slack_nonneg, facts⟩ :=
    oneDimensional weights targetSequence played mixed bayes
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
      (pooled n) (pool (N.agentAt site)) best (slack n * bound + 3 * error n)
      (fun agent inPool decision part => by
        obtain ⟨excluded_le, gap_le, near, ranked⟩ :=
          facts n agent (inPool ▸ inDelivery) decision
        have := localGain_le_of_failure_le fuel observe utility (targetSequence n)
          (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent.1) (excluded agent.1)
          (pays agent.1) (continuation n agent) (error n) (slack n) bound
          (component n agent part) (component n agent (best (pool agent))) (near part)
          (near (best (pool agent))) (ranked part) (slack_nonneg n) excluded_le gap_le
          bound_nonneg
        linarith)
      who site rfl alternative
  · exact le_trans (otherBound n who site inDelivery alternative) (le_max_right _ _)

end Pooled

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

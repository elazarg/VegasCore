/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.CopiedSiteLimit

/-! # Local values and failure probabilities at an information site

At an information site, installing a local law yields a law over observed
outcomes (`GameTheory.Protocol.InformationModel.localLaw`) and the expected
utility of its player (`GameTheory.Protocol.InformationModel.localValue`); the
local gain is the comparison used by the limit obligations of
`GameTheory.Protocol.InformationModel.PooledLimitCertificate`
(`GameTheory.Protocol.InformationModel.localGain`). With finitely many
histories and decisions taken once where it matters, both are affine in the
local law (`GameTheory.Protocol.InformationModel.localValue_bind`,
`GameTheory.Protocol.InformationModel.localGain_bind`).

Fix a set of failed histories. The probability of failure after installing a
local law (`GameTheory.Protocol.InformationModel.localFailure`) is the local
value of the failure indicator
(`GameTheory.Protocol.InformationModel.localFailure_eq_localValue`), and so is
affine in the local law as well
(`GameTheory.Protocol.InformationModel.localFailure_bind`). The expected utility
on the successful histories alone is
`GameTheory.Protocol.InformationModel.localSuccessValue`.

For pooled agents sharing component weights, a part that ranks nearly best
for every member makes every member nearly rational
(`GameTheory.Protocol.InformationModel.memberGain_le_of_common_best`).
-/

noncomputable section

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

/-- An expectation under the site's local run averages, over the belief, the
expectations from each history. -/
theorem expect_localRun [Finite T.History] (law : PMF (N.Choice who site.1))
    (payoff : T.History → ℝ) :
    expect (localRun fuel assessment site law) payoff =
      expect (assessment.belief who site) (fun history =>
        expect (localHistoryRun fuel assessment site law history) payoff) := by
  rw [localRun_eq_bind, expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]

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

/-- **Failure probabilities are affine in the local law.** -/
theorem localFailure_bind [Finite T.History] (bounded : T.BoundedHorizon fuel)
    (actsOnce : N.ActsOnceWhereItMatters) (failed : Set T.History) {Part : Type*} [Finite Part]
    (weights : PMF Part) (component : Part → PMF (N.Choice who site.1)) :
    localFailure fuel assessment site failed (weights.bind component) =
      expect weights (fun part => localFailure fuel assessment site failed (component part)) := by
  classical
  simp only [localFailure_eq_localValue]
  exact localValue_bind fuel id _ assessment site bounded actsOnce weights component

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

end Pooled


end GameTheory.Protocol.InformationModel

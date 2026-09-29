/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationErasure
import GameTheory.Analysis.Protocol.Sequential

/-! # Inducing an information advantage in a larger game

A terminal decision experiment can bound an observer's accuracy even when the
experiment is induced by another player's whole continuation deviation. The
observer may receive a partial signal, randomize, and later suppress reports.
The operational premises identify the induced state law, the observer's
signal-dependent reporting policy, and a payoff advantage over its score.

An optimal policy for the observation experiment gives a bound uniform in the
opponents' actual reporting policies. If the observer merges two supported
states with different facts, perfect informed reporting gives a strictly
positive advantage. The second part lifts an induced deviation guarantee to
the initialized payoff of every sequentially rational assessment when a genuine
decision information site has the initialized continuation value throughout
its compatible-history fiber. No consistency or translation premise is needed.
-/

noncomputable section

namespace GameTheory.DecisionExperiment

open Math.Probability

variable {State Signal Action Outcome : Type*}

/-- A score advantage survives arbitrary continuation mechanics when the
less informed score is bounded by a policy using only the specified signal.
The informed benchmark may already subtract errors or publication costs. -/
theorem induced_advantage
    (prior : PMF State) (observe : State → Signal)
    (score : State → Action → ℝ) (reference policy : Signal → PMF Action)
    (optimal : IsBayesOptimal prior observe score reference)
    (outcomes : State → PMF Outcome) (payoff : Outcome → ℝ)
    (uninformedScore : State → Outcome → ℝ) (benchmark : ℝ)
    (payoffBound : ∀ state ∈ prior.support, ∀ outcome ∈ (outcomes state).support,
      benchmark - uninformedScore state outcome ≤ payoff outcome)
    (observationBound : ∀ state ∈ prior.support,
      expect (outcomes state) (uninformedScore state) ≤
        expect (policy (observe state)) (score state)) :
    benchmark - value prior observe score reference ≤
      expect (prior.bind outcomes) payoff := by
  have lessInformed : expect prior (fun state =>
      expect (outcomes state) (uninformedScore state)) ≤
      value prior observe score reference := by
    calc
      _ ≤ expect prior (fun state =>
          expect (policy (observe state)) (score state)) :=
        FinDist.expect_mono observationBound
      _ = value prior observe score policy :=
        (value_eq_expect prior observe score policy).symm
      _ ≤ _ := optimal.value_le policy
  have advantage : expect prior (fun state =>
      benchmark - expect (outcomes state) (uninformedScore state)) ≤
      expect (prior.bind outcomes) payoff := by
    rw [expect_bind_of_finite]
    refine expect_mono (fun state supported => ?_) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [← expect_constant (outcomes state) benchmark, ← FinDist.expect_sub]
    exact FinDist.expect_mono (payoffBound state supported)
  rw [FinDist.expect_sub, expect_constant] at advantage
  linarith

variable {Fact : Type*} [DecidableEq Fact]

/-- A relevant observation merge yields one strictly positive margin which
works for every actual observer policy and every induced continuation obeying
the score premises. The margin depends only on the observation experiment,
not on the opponents' strategies. -/
theorem exists_positive_induced_advantage_of_collision
    [Finite Fact] [Nonempty Fact]
    (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    {first second : State} (firstPresent : first ∈ prior.support)
    (secondPresent : second ∈ prior.support) (same : observe first = observe second)
    (different : fact first ≠ fact second) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ (policy : Signal → PMF Fact) (outcomes : State → PMF Outcome)
        (payoff : Outcome → ℝ) (uninformedScore : State → Outcome → ℝ),
        (∀ state ∈ prior.support, ∀ outcome ∈ (outcomes state).support,
          1 - uninformedScore state outcome ≤ payoff outcome) →
        (∀ state ∈ prior.support,
          expect (outcomes state) (uninformedScore state) ≤
            expect (policy (observe state)) (reportUtility fact state)) →
        margin ≤ expect (prior.bind outcomes) payoff := by
  obtain ⟨reference, optimal⟩ :=
    exists_bayesOptimal prior observe (reportUtility fact)
  refine ⟨1 - value prior observe (reportUtility fact) reference, ?_, ?_⟩
  · exact sub_pos.mpr (report_value_lt_one_of_collision prior observe fact
      firstPresent secondPresent same different reference)
  · intro policy outcomes payoff uninformedScore payoffBound observationBound
    exact induced_advantage prior observe (reportUtility fact) reference policy
      optimal outcomes payoff uninformedScore 1 payoffBound observationBound

end GameTheory.DecisionExperiment

namespace GameTheory.Protocol.InformationModel

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} {M : InformationModel E}

/-- Operational equality on every compatible history makes this site's
comparison equal to the initialized comparison, independently of beliefs.
The alternative is a whole policy, not only the immediate action. -/
theorem continuation_value_eq_initial
    (assessment : M.BehavioralAssessment) (player : ι)
    (site : M.InformationSite player) (payoff : E.History → ℝ) (fuel : Nat)
    (historyValue : ∀ (profile : Profile M.behavioralSignature)
      (history : M.InformationHistory player site.1),
      expect (M.runBehavioralFrom profile fuel history.1) payoff =
        expect (M.runBehavioral profile fuel) payoff)
    (alternative : M.BehavioralPolicy player) :
    (assessment.continuationContext site payoff fuel).value alternative =
      expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy player alternative) fuel) payoff := by
  rw [BehavioralAssessment.continuationContext_value, expect_bind_of_finite]
  calc
    _ = expect (assessment.belief player site) (fun _ =>
        expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
          assessment.strategy player alternative) fuel) payoff) := by
      apply expect_congr_on_support
      intro history _
      exact historyValue _ history
    _ = _ := expect_constant _ _

/-- A feasible induced deviation with a guaranteed initialized payoff bounds
every sequentially rational assessment, provided the stated actual information
site compares initialized continuations. Rationality at off-path sites may be
used separately to establish the guarantee against the assessment's opponents. -/
theorem initial_value_ge_of_induced_deviation
    (assessment : M.BehavioralAssessment) (payoff : ι → E.History → ℝ)
    (fuel : Nat) (rational : assessment.IsSequentiallyRationalWithin payoff fuel)
    (player : ι) (site : M.InformationSite player)
    (historyValue : ∀ (profile : Profile M.behavioralSignature)
      (history : M.InformationHistory player site.1),
      expect (M.runBehavioralFrom profile fuel history.1) (payoff player) =
        expect (M.runBehavioral profile fuel) (payoff player))
    (alternative : M.BehavioralPolicy player) (bound : ℝ)
    (guarantee : bound ≤ expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy player alternative) fuel) (payoff player)) :
    bound ≤ expect (M.runBehavioral assessment.strategy fuel) (payoff player) := by
  have comparison := rational player site alternative (Set.mem_univ _)
  change (assessment.continuationContext site (payoff player) fuel).value alternative ≤
    (assessment.continuationContext site (payoff player) fuel).value
      (assessment.strategy player) at comparison
  rw [continuation_value_eq_initial assessment player site (payoff player) fuel historyValue,
    continuation_value_eq_initial assessment player site (payoff player) fuel historyValue,
    Profile.update_eq_self] at comparison
  exact guarantee.trans comparison

variable {State Signal Action Result : Type}

/-- A player can induce an information experiment with a payoff advantage
larger than a proposed source outcome's payoff. Every sequentially rational
target then has a different initialized result law. The observer's optimal
reference policy is analysis data; the actual observer may use any policy.

This theorem is about one fixed payoff assignment. The excluded implementation
may choose its entire strategy and belief system with knowledge of that payoff.
The premises concern feasible continuation laws and information, not a chosen
strategy translator. -/
theorem initial_law_ne_of_induced_information
    (assessment : M.BehavioralAssessment) (payoff : ι → E.History → ℝ)
    (fuel : Nat) (rational : assessment.IsSequentiallyRationalWithin payoff fuel)
    (player : ι) (site : M.InformationSite player)
    (historyValue : ∀ (profile : Profile M.behavioralSignature)
      (history : M.InformationHistory player site.1),
      expect (M.runBehavioralFrom profile fuel history.1) (payoff player) =
        expect (M.runBehavioral profile fuel) (payoff player))
    (alternative : M.BehavioralPolicy player)
    (result : E.History → Result) (resultPayoff : Result → ℝ)
    (initialValue : ∀ profile : Profile M.behavioralSignature,
      expect ((M.runBehavioral profile fuel).map result) resultPayoff =
        expect (M.runBehavioral profile fuel) (payoff player))
    (prior : PMF State) (observe : State → Signal) (score : State → Action → ℝ)
    (reference policy : Signal → PMF Action)
    (optimal : DecisionExperiment.IsBayesOptimal prior observe score reference)
    (outcomes : State → PMF Result) (uninformedScore : State → Result → ℝ)
    (benchmark : ℝ)
    (deviationValue : expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy player alternative) fuel) (payoff player) =
        expect (prior.bind outcomes) resultPayoff)
    (payoffBound : ∀ state ∈ prior.support, ∀ outcome ∈ (outcomes state).support,
      benchmark - uninformedScore state outcome ≤ resultPayoff outcome)
    (observationBound : ∀ state ∈ prior.support,
      expect (outcomes state) (uninformedScore state) ≤
        expect (policy (observe state)) (score state))
    (sourceLaw : PMF Result)
    (sourceBound : expect sourceLaw resultPayoff <
      benchmark - DecisionExperiment.value prior observe score reference) :
    (M.runBehavioral assessment.strategy fuel).map result ≠ sourceLaw := by
  have advantage := DecisionExperiment.induced_advantage prior observe score reference policy
    optimal outcomes resultPayoff uninformedScore benchmark payoffBound observationBound
  have bound := initial_value_ge_of_induced_deviation assessment payoff fuel rational
    player site historyValue alternative
    (benchmark - DecisionExperiment.value prior observe score reference)
      (by rw [deviationValue]; exact advantage)
  intro sameLaw
  rw [← initialValue assessment.strategy, sameLaw] at bound
  exact (not_lt_of_ge bound) sourceBound

end GameTheory.Protocol.InformationModel

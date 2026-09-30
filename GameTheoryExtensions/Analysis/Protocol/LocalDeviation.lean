/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.DecisionRecall
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheoryExtensions.Math.Probability.Support

/-! # Ex ante and conditional comparisons at one information site

At a positive-mass common-depth information site, changing only its behavioral
law changes ex ante utility by the site's reach mass times its Bayes
continuation gain. Decision-site recall supplies the common own-reach coefficient;
the existing run decomposition supplies the actual protocol law identity.

The two-alternative comparison is useful for perturbed agent-form equilibria:
the residual best response and a competing action can both differ from the
fully mixed baseline at the same site. This result does not by itself turn
one-site optimality into whole-policy sequential rationality.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} {E : ExecutionProtocol Player} (M : InformationModel E)

variable [Fintype Player] [DecidableEq Player]
  (assessment : M.BehavioralAssessment) (recall : M.DecisionRecall)
  (who : Player) (site : M.InformationSite who)
  [Finite (M.InformationHistory who site.1)]
  (depth fuel : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
  (positive : 0 < M.informationMass assessment.strategy who site)
  (bayes : BehavioralAssessment.IsBayesConsistentAt M assessment who site
    (recall.decisionInformationAntichain who site) positive)
  (payoff : E.History → ℝ)

include recall sameDepth positive bayes in
/-- The integrability premises are exactly those of the upstream decomposition;
every finitely supported law satisfies them. -/
theorem root_gain_eq_mass_mul_context_gain
    (alternative : M.BehavioralPolicy who)
    (onlyHere : ∀ {info}, info ≠ site.1 → alternative info = assessment.strategy who info)
    (updatedIntegrable : PayoffIntegrable (M.runBehavioral (Profile.update
      (sig := M.behavioralSignature) assessment.strategy who alternative) (depth + fuel)) payoff)
    (baselineIntegrable : PayoffIntegrable (M.runBehavioral assessment.strategy (depth + fuel))
      payoff)
    (alternativeIntegrable : CounterfactualContinuationIntegrable M assessment.strategy who site
      alternative payoff (M.truncatedRunner fuel))
    (incumbentIntegrable : CounterfactualContinuationIntegrable M assessment.strategy who site
      (assessment.strategy who) payoff (M.truncatedRunner fuel)) :
    expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who alternative) (depth + fuel)) payoff -
      expect (M.runBehavioral assessment.strategy (depth + fuel)) payoff =
    (M.informationMass assessment.strategy who site).toReal *
      ((assessment.truncatedContinuationContext site payoff fuel).value alternative -
        (assessment.truncatedContinuationContext site payoff fuel).value (assessment.strategy
            who)) := by
  let := Fintype.ofFinite (M.InformationHistory who site.1)
  let antichain := recall.decisionInformationAntichain who site
  have belief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site antichain positive := by
    ext history
    rw [M.bayesBelief_apply]
    exact bayes history
  have context (policy : M.BehavioralPolicy who) :
      (assessment.truncatedContinuationContext site payoff fuel).value policy =
        M.bayesContinuationValue assessment.strategy who site antichain positive
          policy payoff (M.truncatedRunner fuel) := by
    unfold bayesContinuationValue BehavioralAssessment.truncatedContinuationContext
      BehavioralAssessment.continuationContextWith
    rw [belief]
  obtain ⟨ownReach, shared⟩ :=
    M.commonPlayerReachAt_of_decisionRecall recall assessment.strategy who site
  rw [M.rootGain_eq_ownReach_mul_counterfactualRegret assessment.strategy who site
    alternative depth sameDepth onlyHere ownReach shared payoff
    (fun policies => M.runBehavioral policies (depth + fuel)) (M.truncatedRunner fuel)
    (M.runnerReadsReachable_truncated fuel)
    (fun policies => M.runBehavioralFrom_add policies depth fuel E.initHistory)
    updatedIntegrable baselineIntegrable, context, context]
  exact (M.informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
    assessment.strategy who site antichain positive ownReach shared alternative payoff
    (M.truncatedRunner fuel)
    alternativeIntegrable incumbentIntegrable).symm

include recall sameDepth positive bayes in
/-- Local ex ante best responses are exactly conditional best responses,
including comparisons of two replacements against a different baseline. -/
theorem local_root_comparison_iff_context_comparison
    (first second : M.BehavioralPolicy who)
    (firstOnly : ∀ {info}, info ≠ site.1 → first info = assessment.strategy who info)
    (secondOnly : ∀ {info}, info ≠ site.1 → second info = assessment.strategy who info)
    (firstIntegrable : PayoffIntegrable (M.runBehavioral (Profile.update
      (sig := M.behavioralSignature) assessment.strategy who first) (depth + fuel)) payoff)
    (secondIntegrable : PayoffIntegrable (M.runBehavioral (Profile.update
      (sig := M.behavioralSignature) assessment.strategy who second) (depth + fuel)) payoff)
    (baselineIntegrable : PayoffIntegrable (M.runBehavioral assessment.strategy (depth + fuel))
      payoff)
    (firstContinuation : CounterfactualContinuationIntegrable M assessment.strategy who site
      first payoff (M.truncatedRunner fuel))
    (secondContinuation : CounterfactualContinuationIntegrable M assessment.strategy who site
      second payoff (M.truncatedRunner fuel))
    (incumbentContinuation : CounterfactualContinuationIntegrable M assessment.strategy who site
      (assessment.strategy who) payoff (M.truncatedRunner fuel)) :
    expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who first) (depth + fuel)) payoff ≤
      expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who second) (depth + fuel)) payoff ↔
    (assessment.truncatedContinuationContext site payoff fuel).value first ≤
      (assessment.truncatedContinuationContext site payoff fuel).value second := by
  have firstGain := M.root_gain_eq_mass_mul_context_gain assessment recall who site
    depth fuel sameDepth positive bayes payoff first firstOnly firstIntegrable
    baselineIntegrable firstContinuation incumbentContinuation
  have secondGain := M.root_gain_eq_mass_mul_context_gain assessment recall who site
    depth fuel sameDepth positive bayes payoff second secondOnly secondIntegrable
    baselineIntegrable secondContinuation incumbentContinuation
  have massPositive : 0 < (M.informationMass assessment.strategy who site).toReal :=
    ENNReal.toReal_pos positive.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one _ _ _ (recall.decisionInformationAntichain who site)))
  constructor <;> intro bound <;> nlinarith

include recall sameDepth positive bayes in
/-- Concrete law replacements are supported directly; callers need no
agreement certificates for the unchanged information states. -/
theorem local_law_root_comparison_iff_context_comparison
    [DecidableEq (M.InfoState who)]
    (first second : PMF (M.Choice who site.1))
    (firstIntegrable : PayoffIntegrable (M.runBehavioral (Profile.update
      (sig := M.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 first)) (depth + fuel)) payoff)
    (secondIntegrable : PayoffIntegrable (M.runBehavioral (Profile.update
      (sig := M.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 second)) (depth + fuel)) payoff)
    (baselineIntegrable : PayoffIntegrable (M.runBehavioral assessment.strategy (depth + fuel))
      payoff)
    (firstContinuation : CounterfactualContinuationIntegrable M assessment.strategy who site
      ((assessment.strategy who).withLaw site.1 first) payoff (M.truncatedRunner fuel))
    (secondContinuation : CounterfactualContinuationIntegrable M assessment.strategy who site
      ((assessment.strategy who).withLaw site.1 second) payoff (M.truncatedRunner fuel))
    (incumbentContinuation : CounterfactualContinuationIntegrable M assessment.strategy who site
      (assessment.strategy who) payoff (M.truncatedRunner fuel)) :
    expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who ((assessment.strategy who).withLaw site.1 first))
        (depth + fuel)) payoff ≤
      expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who ((assessment.strategy who).withLaw site.1 second))
          (depth + fuel)) payoff ↔
    (assessment.truncatedContinuationContext site payoff fuel).value
        ((assessment.strategy who).withLaw site.1 first) ≤
      (assessment.truncatedContinuationContext site payoff fuel).value
        ((assessment.strategy who).withLaw site.1 second) :=
  M.local_root_comparison_iff_context_comparison assessment recall who site depth fuel
    sameDepth positive bayes payoff _ _
    (fun different => BehavioralPolicy.withLaw_of_ne _ _ _ different)
    (fun different => BehavioralPolicy.withLaw_of_ne _ _ _ different)
    firstIntegrable secondIntegrable baselineIntegrable firstContinuation secondContinuation
    incumbentContinuation

end GameTheory.Protocol.InformationModel

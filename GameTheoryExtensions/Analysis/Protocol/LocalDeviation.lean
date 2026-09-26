/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Ex ante and conditional comparisons at one information site

At a positive-mass common-depth information site, changing only its behavioral
law changes ex ante utility by the site's reach mass times its Bayes
continuation gain. Perfect recall supplies the common own-reach coefficient;
the existing run decomposition supplies the actual protocol law identity.

The two-alternative comparison is useful for perturbed agent-form equilibria:
the residual best response and a competing action can both differ from the
fully mixed baseline at the same site. This result does not by itself turn
one-site optimality into whole-policy sequential rationality.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)
  (assessment : M.BehavioralAssessment) (recall : M.PerfectRecall)
  (who : Player) (site : M.InformationSite who)
  [Fintype (M.InformationHistory who site.1)]
  (depth fuel : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
  (positive : 0 < M.informationMass assessment.strategy who site)
  (bayes : BehavioralAssessment.IsBayesConsistentAt M assessment who site
    (M.decisionInformationAntichain_of_perfectRecall recall who site) positive)
  (payoff : E.History → ℝ)

include recall sameDepth positive bayes in
theorem root_gain_eq_mass_mul_context_gain
    (alternative : M.BehavioralPolicy who)
    (onlyHere : ∀ {info}, info ≠ site.1 → alternative info = assessment.strategy who info) :
    (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who alternative) (depth + fuel)).expect payoff -
      (M.runBehavioral assessment.strategy (depth + fuel)).expect payoff =
    M.informationMass assessment.strategy who site *
      ((assessment.continuationContext site payoff fuel).value alternative -
        (assessment.continuationContext site payoff fuel).value (assessment.strategy who)) := by
  let antichain := M.decisionInformationAntichain_of_perfectRecall recall who site
  have belief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site antichain positive := by
    apply FinDist.ext_of_prob
    intro history
    rw [M.bayesBelief_prob]
    exact bayes history
  have context (policy : M.BehavioralPolicy who) :
      (assessment.continuationContext site payoff fuel).value policy =
        M.bayesContinuationValue assessment.strategy who site antichain positive
          policy payoff fuel := by
    rw [BehavioralAssessment.continuationContext_value, belief, FinDist.expect_bind]
    rfl
  obtain ⟨ownReach, shared⟩ :=
    M.commonPlayerReachAt_of_perfectRecall recall assessment.strategy who site
  rw [M.rootGain_eq_ownReach_mul_counterfactualRegret assessment.strategy who site
    alternative depth fuel sameDepth onlyHere ownReach shared payoff, context, context]
  exact (M.informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
    assessment.strategy who site antichain positive ownReach shared alternative payoff fuel).symm

include recall sameDepth positive bayes in
/-- Local ex ante best responses are exactly conditional best responses,
including comparisons of two replacements against a different baseline. -/
theorem local_root_comparison_iff_context_comparison
    (first second : M.BehavioralPolicy who)
    (firstOnly : ∀ {info}, info ≠ site.1 → first info = assessment.strategy who info)
    (secondOnly : ∀ {info}, info ≠ site.1 → second info = assessment.strategy who info) :
    (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who first) (depth + fuel)).expect payoff ≤
      (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who second) (depth + fuel)).expect payoff ↔
    (assessment.continuationContext site payoff fuel).value first ≤
      (assessment.continuationContext site payoff fuel).value second := by
  have firstGain := M.root_gain_eq_mass_mul_context_gain assessment recall who site
    depth fuel sameDepth positive bayes payoff first firstOnly
  have secondGain := M.root_gain_eq_mass_mul_context_gain assessment recall who site
    depth fuel sameDepth positive bayes payoff second secondOnly
  constructor <;> intro bound <;> nlinarith

include recall sameDepth positive bayes in
/-- Concrete law replacements are supported directly; callers need no
agreement certificates for the unchanged information states. -/
theorem local_law_root_comparison_iff_context_comparison
    [DecidableEq (M.InfoState who)]
    (first second : FinDist (M.Choice who site.1)) :
    (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who ((assessment.strategy who).withLaw site.1 first))
        (depth + fuel)).expect payoff ≤
      (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who ((assessment.strategy who).withLaw site.1 second))
          (depth + fuel)).expect payoff ↔
    (assessment.continuationContext site payoff fuel).value
        ((assessment.strategy who).withLaw site.1 first) ≤
      (assessment.continuationContext site payoff fuel).value
        ((assessment.strategy who).withLaw site.1 second) :=
  M.local_root_comparison_iff_context_comparison assessment recall who site depth fuel
    sameDepth positive bayes payoff _ _
    (fun different => BehavioralPolicy.withLaw_of_ne _ _ _ different)
    (fun different => BehavioralPolicy.withLaw_of_ne _ _ _ different)

end GameTheory.Protocol.InformationModel

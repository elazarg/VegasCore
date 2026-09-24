/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheory.Protocol.BehavioralAssessment

/-! # Supported responses under sequential rationality

The existing no-revisit condition makes a continuation value affine in the
current response distribution. Sequential rationality therefore makes every
supported current response optimal, with the subsequent strategy unchanged.
A uniform payoff gap excludes a response without requiring positive belief
on each history in the information set. Concrete applications must establish
that gap across the entire information set, including its zero-belief nodes.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} {M : InformationModel E}
  {who : ι} [DecidableEq (M.InfoState who)]

theorem BehavioralAssessment.continuationContext_value_withLaw
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (law : FinDist (M.Choice who site.1)) :
    (assessment.continuationContext site payoff (fuel + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      law.expect (fun choice =>
        (assessment.continuationContext site payoff (fuel + 1)).value
          ((assessment.strategy who).commit site.1 choice)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief who site).expect (fun history =>
          law.expect (fun choice =>
            (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
              assessment.strategy who ((assessment.strategy who).commit site.1 choice))
                (fuel + 1) history.1).expect payoff)) := by
      apply FinDist.expect_congr
      intro history _
      rw [M.runBehavioralFrom_update_withLaw_eq_bind once assessment.strategy who
        (assessment.strategy who) site.1 law history.1 history.2 (nonterminal history)
          (InformationSite.active M site history) fuel, FinDist.expect_bind]
    _ = _ := FinDist.expect_comm _ _ _

/-- Each supported pure current response has the same continuation value as
the rational mixed response. Future choices remain the assessment's strategy. -/
theorem BehavioralAssessment.supported_choice_value
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff (fuel + 1)))
    (choice : M.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support) :
    (assessment.continuationContext site payoff (fuel + 1)).value
        ((assessment.strategy who).commit site.1 choice) =
      (assessment.continuationContext site payoff (fuel + 1)).value
        (assessment.strategy who) := by
  have affine := assessment.continuationContext_value_withLaw once site nonterminal
    payoff fuel (assessment.strategy who site.1)
  rw [BehavioralPolicy.withLaw_eq_self] at affine
  apply FinDist.eq_of_expect_eq_of_le (assessment.strategy who site.1) _ _
    (fun alternative _ => rational ((assessment.strategy who).commit site.1 alternative)
      (Set.mem_univ _)) affine.symm supported

/-- Supported responses maximize against whole continuation-policy deviations,
not merely other current responses. -/
theorem BehavioralAssessment.supported_choice_optimal
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff (fuel + 1)))
    (choice : M.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support)
    (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContext site payoff (fuel + 1)).value alternative ≤
      (assessment.continuationContext site payoff (fuel + 1)).value
        ((assessment.strategy who).commit site.1 choice) := by
  rw [assessment.supported_choice_value once site nonterminal payoff fuel rational choice supported]
  exact rational alternative (Set.mem_univ _)

/-- Uniformly worse responses receive no probability. The bounds range over
all compatible histories, so this conclusion also controls an actual history
that the assessment happens to assign zero probability. -/
theorem BehavioralAssessment.not_supported_choice_of_uniform_gap
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff (fuel + 1)))
    (choice : M.Choice who site.1) (alternative : M.BehavioralPolicy who)
    (upper lower : ℝ) (gap : upper < lower)
    (bad : ∀ history : M.InformationHistory who site.1,
      (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who ((assessment.strategy who).commit site.1 choice))
          (fuel + 1) history.1).expect payoff ≤ upper)
    (good : ∀ history : M.InformationHistory who site.1,
      lower ≤ (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) (fuel + 1) history.1).expect payoff) :
    choice ∉ (assessment.strategy who site.1).support := by
  intro supported
  have best := assessment.supported_choice_optimal once site nonterminal payoff fuel rational
    choice supported alternative
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind] at best
  have badBound := FinDist.expect_le_of_forall (assessment.belief who site) _ upper
    (fun history _ => bad history)
  have goodBound : lower ≤ (assessment.belief who site).expect (fun history =>
      (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) (fuel + 1) history.1).expect payoff) := by
    calc
      lower = (assessment.belief who site).expect (fun _ => lower) :=
        (FinDist.expect_const _ _).symm
      _ ≤ _ := FinDist.expect_mono (fun history _ => good history)
  exact (not_le_of_gt gap) (goodBound.trans (best.trans badBound))

end GameTheory.Protocol.InformationModel

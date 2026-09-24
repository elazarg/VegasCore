/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ContinuationDecision

/-! # A continuation capability obstructing uniform sequential compilation

A binary decision is more than a menu with two actions. At one actual decision
information set, every compatible history has the same profile-dependent
continuation value, and the player can force either of two opposite outcomes.
These operational laws make beliefs irrelevant to the local conflict between
the two utilities. A source assessment that is an equilibrium for both therefore
has no utility-independent sequential translation into any such target.

Disclosure is one way to supply this capability: transferable evidence fixes a
previously hidden fact throughout the receiver's information set, after which
the receiver can choose either answer. The witness does not presume that every
communication or commitment implementation has this capability.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} {M : InformationModel E}

/-- An information-local, controllable binary continuation with opposite
utilities. The history law must hold at every compatible history, including
histories assigned zero probability by a proposed assessment. -/
structure BinaryDecision (M : InformationModel E)
    (utility : Bool → ι → E.History → ℝ) (fuel : Nat) where
  player : ι
  site : M.InformationSite player
  outcome : Profile M.behavioralSignature → FinDist Bool
  policy : Bool → M.BehavioralPolicy player
  history_value : ∀ profile goal (history : M.InformationHistory player site.1),
    (M.runBehavioralFrom profile fuel history.1).expect (utility goal player) =
      (outcome profile).expect (fun result => if result = goal then 1 else 0)
  force : ∀ profile goal,
    outcome (Profile.update (sig := M.behavioralSignature) profile player (policy goal)) =
      FinDist.pure goal

namespace BinaryDecision

variable {utility : Bool → ι → E.History → ℝ} {fuel : Nat}
  (decision : M.BinaryDecision utility fuel)

/-- The binary capability is the fully informed, indicator-reward instance
of an ordinary continuation decision. -/
def toContinuationDecision (goal : Bool) :
    M.ContinuationDecision (utility goal) fuel Unit Bool where
  player := decision.player
  site := decision.site
  state _ := ()
  response := decision.outcome
  reward _ result := if result = goal then 1 else 0
  policy := decision.policy
  history_value profile history := decision.history_value profile goal history
  realize := decision.force

private theorem expectedReward_eq (assessment : M.BehavioralAssessment) (goal : Bool) :
    (decision.toContinuationDecision goal).expectedReward assessment =
      fun result => if result = goal then 1 else 0 := by
  funext result
  exact FinDist.expect_const _ _

/-- The compatible-history law removes all dependence on the assessment's
beliefs; the deviation still replaces a complete continuation policy. -/
theorem continuation_value (assessment : M.BehavioralAssessment)
    (goal : Bool) (alternative : M.BehavioralPolicy decision.player) :
    (assessment.continuationContext decision.site (utility goal decision.player) fuel).value
        alternative =
      (decision.outcome (Profile.update (sig := M.behavioralSignature)
        assessment.strategy decision.player alternative)).expect
          (fun result => if result = goal then 1 else 0) := by
  have value := (decision.toContinuationDecision goal).continuation_value assessment alternative
  rw [decision.expectedReward_eq] at value
  exact value

/-- Rationality for either utility forces that utility's maximal value. -/
theorem rational_value (assessment : M.BehavioralAssessment) (goal : Bool)
    (rational : assessment.IsSequentiallyRationalWithin (utility goal) fuel) :
    1 ≤ (decision.outcome assessment.strategy).expect
      (fun result => if result = goal then 1 else 0) := by
  have bound :=
    (decision.toContinuationDecision goal).rational_value_bound assessment rational goal
  rw [decision.expectedReward_eq] at bound
  simpa only [↓reduceIte, toContinuationDecision] using bound

include decision in
/-- Even separate, utility-dependent beliefs cannot rationalize one strategy
for both utilities. No consistency premise is needed for this obstruction. -/
theorem no_common_rational_strategy : ¬ ∃ first second : M.BehavioralAssessment,
    first.strategy = second.strategy ∧
      first.IsSequentiallyRationalWithin (utility true) fuel ∧
      second.IsSequentiallyRationalWithin (utility false) fuel := by
  rintro ⟨first, second, same, firstRational, secondRational⟩
  have firstOptimal := decision.rational_value first true firstRational
  have secondOptimal := decision.rational_value second false secondRational
  rw [← same] at secondOptimal
  have total :
      (decision.outcome first.strategy).expect (fun result => if result = true then 1 else 0) +
        (decision.outcome first.strategy).expect
          (fun result => if result = false then (1 : ℝ) else 0) = 1 := by
    rw [← FinDist.expect_add]
    calc
      _ = (decision.outcome first.strategy).expect (fun _ => (1 : ℝ)) := by
        apply FinDist.expect_congr
        intro result _
        cases result <;> norm_num
      _ = _ := FinDist.expect_const _ _
  linarith

variable {S : ExecutionProtocol ι} {N : InformationModel S}
  [∀ who (site : N.InformationSite who), Fintype (N.InformationHistory who site.1)]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]

include decision in
/-- An implementation-class obstruction: any target supplying this decision
capability fails to translate a shared source equilibrium for the two utilities.
The translator may inspect the entire profile, and target beliefs may depend
on the utility. The two utilities need not agree away from the decisive site. -/
theorem no_utility_independent_sequential_translation
    (source : N.BehavioralAssessment)
    (sourceAntichain : N.DecisionInformationAntichain)
    (targetAntichain : M.DecisionInformationAntichain)
    (sourceUtility : Bool → ι → S.History → ℝ) (sourceFuel : Nat)
    (equilibrium : ∀ goal,
      source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        source.continuationContext site (sourceUtility goal who) sourceFuel)) :
    ¬ ∃ translate : Profile N.behavioralSignature → Profile M.behavioralSignature,
      ∀ goal,
        source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
          source.continuationContext site (sourceUtility goal who) sourceFuel) →
        ∃ target : M.BehavioralAssessment,
          target.strategy = translate source.strategy ∧
            target.IsSequentialEquilibriumFor targetAntichain (fun who site =>
              target.continuationContext site (utility goal who) fuel) := by
  rintro ⟨translate, preserves⟩
  obtain ⟨first, firstEq, firstEquilibrium⟩ := preserves true (equilibrium true)
  obtain ⟨second, secondEq, secondEquilibrium⟩ := preserves false (equilibrium false)
  exact decision.no_common_rational_strategy ⟨first, second, firstEq.trans secondEq.symm,
    firstEquilibrium.1, secondEquilibrium.1⟩

end BinaryDecision

end GameTheory.Protocol.InformationModel

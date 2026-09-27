/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.OneShotLimit
import GameTheoryExtensions.Analysis.Protocol.BehavioralOneShot

/-! # Uniform continuation regret along a consistent approximation

Finite decision menus strengthen the fixed-alternative continuity bound to a
bound for every continuation policy at once. This is needed when a realization
or private-history posterior chooses a different simulated deviation at each
perturbation. The bound has no inverse information-set reach probability.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E}
  [∀ who, DecidableEq (M.InfoState who)]

/-- A single information-set lottery averages the pure committed responses,
including when the current history is terminal or the horizon is zero. -/
theorem BehavioralAssessment.context_withLaw_expect
    (assessment : M.BehavioralAssessment) (recall : M.DecisionRecall)
    (who : Player) (site : M.InformationSite who) (payoff : E.History → ℝ)
    (fuel : Nat) (law : FinDist (M.Choice who site.1)) :
    (assessment.continuationContext site payoff fuel).value
        ((assessment.strategy who).withLaw site.1 law) =
      law.expect (fun choice => (assessment.continuationContext site payoff fuel).value
        ((assessment.strategy who).commit site.1 choice)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  have each (history : M.InformationHistory who site.1) :
      (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy who
          ((assessment.strategy who).withLaw site.1 law)) fuel history.1).expect payoff =
      law.expect (fun choice => (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy who
          ((assessment.strategy who).commit site.1 choice)) fuel history.1).expect payoff) := by
    cases fuel with
    | zero =>
      simp only [runBehavioralFrom, runRandomizedFor_zero,
        FinDist.expect_pure, FinDist.expect_const]
    | succ fuel =>
      by_cases stopped : E.terminal history.1.state
      · simp only [M.runBehavioralFrom_of_terminal _ _ stopped,
          FinDist.expect_pure, FinDist.expect_const]
      · exact M.behavioralContinuationValue_withLaw_eq_expect
          recall.actsOnceWhereItMatters assessment.strategy who site
            (assessment.strategy who) law history stopped payoff fuel
  calc
    _ = (assessment.belief who site).expect (fun history => law.expect (fun choice =>
        (M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who
            ((assessment.strategy who).commit site.1 choice)) fuel history.1).expect payoff)) :=
      FinDist.expect_congr fun history _ => each history
    _ = _ := FinDist.expect_comm _ _ _

/-- All local lotteries share one vanishing error bound. A source posterior or
an action realization may therefore select its lottery after the perturbation
index is known. -/
theorem BehavioralAssessmentConvergesPointwise.exists_uniform_local_gain_bound
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (recall : M.DecisionRecall) (who : Player) [Finite (M.InformationSite who)]
    [∀ site : M.InformationSite who, Finite (M.InformationHistory who site.1)]
    (clock : ∀ site : M.InformationSite who,
      ∃ depth, InformationSite.CommonDepth M site depth)
    (horizon : Nat) (payoff : E.History → ℝ)
    (localOptimal : ∀ (site : M.InformationSite who) depth,
      InformationSite.CommonDepth M site depth → depth < horizon →
      ∀ law : FinDist (M.Choice who site.1),
        (assessment.continuationContext site payoff (horizon - depth)).value
            ((assessment.strategy who).withLaw site.1 law) ≤
          (assessment.continuationContext site payoff (horizon - depth)).value
            (assessment.strategy who)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : M.InformationSite who) depth,
        InformationSite.CommonDepth M site depth → depth < horizon →
        ∀ law : FinDist (M.Choice who site.1),
          ((sequence n).continuationContext site payoff (horizon - depth)).value
              (((sequence n).strategy who).withLaw site.1 law) -
            ((sequence n).continuationContext site payoff (horizon - depth)).value
              ((sequence n).strategy who) ≤ error n := by
  classical
  let _ (site : M.InformationSite who) : Finite (M.Choice who site.1) :=
    (mixed who site).finite
  let Entry := (site : M.InformationSite who) × M.Choice who site.1
  let _ := Fintype.ofFinite Entry
  have existsError (entry : Entry) :
      ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
        ∀ n (site : M.InformationSite who) depth,
          InformationSite.CommonDepth M site depth → depth < horizon →
          ((sequence n).continuationContext site payoff (horizon - depth)).value
              (((sequence n).strategy who).withLaw site.1
                (((assessment.strategy who).commit entry.1.1 entry.2) site.1)) -
            ((sequence n).continuationContext site payoff (horizon - depth)).value
              ((sequence n).strategy who) ≤ error n :=
    converges.exists_vanishing_local_gain_bound reference mixed who clock horizon payoff
      ((assessment.strategy who).commit entry.1.1 entry.2)
      (fun site depth sameDepth before => localOptimal site depth sameDepth before _)
  choose errors nonnegative vanishes bounds using existsError
  let error (n : ℕ) := ∑ entry, errors entry n
  have positive (n : ℕ) : 0 ≤ error n :=
    Finset.sum_nonneg (fun entry _ => nonnegative entry n)
  have tends : Tendsto error atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun entry _ => vanishes entry)
  refine ⟨error, positive, tends, ?_⟩
  intro n site depth sameDepth before law
  rw [(sequence n).context_withLaw_expect recall who site payoff (horizon - depth) law]
  apply sub_le_iff_le_add.mpr
  calc
    _ ≤ law.expect (fun _ => error n +
        ((sequence n).continuationContext site payoff (horizon - depth)).value
          ((sequence n).strategy who)) := by
      apply FinDist.expect_mono
      intro choice _
      have bound := bounds ⟨site, choice⟩ n site depth sameDepth before
      rw [BehavioralPolicy.commit_self] at bound
      exact sub_le_iff_le_add.mp (bound.trans
        (Finset.single_le_sum (fun entry _ => nonnegative entry n)
          (Finset.mem_univ (⟨site, choice⟩ : Entry))))
    _ = _ := FinDist.expect_const _ _

omit [∀ who, DecidableEq (M.InfoState who)] in
/-- Sequential rationality of the limit controls every whole continuation
policy uniformly along its fully mixed Bayesian sequence. Alternatives may
vary with the index, the current information set, or a private-memory draw. -/
theorem BehavioralAssessmentConvergesPointwise.exists_uniform_continuation_gain_bound
    [Finite E.History]
    [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (recall : M.DecisionRecall)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) recall.antichain)
    (who : Player)
    (clock : ∀ site : M.InformationSite who,
      ∃ depth, InformationSite.CommonDepth M site depth)
    (horizon : Nat) (payoff : E.History → ℝ)
    (rational : ∀ (site : M.InformationSite who) depth,
      InformationSite.CommonDepth M site depth → depth ≤ horizon →
      assessment.IsSequentiallyRationalAt site
        (assessment.continuationContext site payoff (horizon - depth))) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : M.InformationSite who) depth,
        InformationSite.CommonDepth M site depth → depth ≤ horizon →
        ∀ alternative : M.BehavioralPolicy who,
          ((sequence n).continuationContext site payoff (horizon - depth)).value alternative -
            ((sequence n).continuationContext site payoff (horizon - depth)).value
              ((sequence n).strategy who) ≤ error n := by
  classical
  obtain ⟨error, nonnegative, vanishes, localBound⟩ :=
    converges.exists_uniform_local_gain_bound (sequence 0) (mixed 0) recall who clock
      horizon payoff (fun site depth sameDepth before law =>
        rational site depth sameDepth before.le
          ((assessment.strategy who).withLaw site.1 law) (Set.mem_univ _))
  refine ⟨fun n => horizon * error n, (fun n => mul_nonneg (Nat.cast_nonneg _) (nonnegative n)),
    ?_, ?_⟩
  · simpa only [mul_zero] using vanishes.const_mul (horizon : ℝ)
  · intro n site depth sameDepth within alternative
    have bound := M.whole_policy_gain_le_of_local_gains (sequence n) recall (mixed n) (bayes n)
      who alternative clock horizon payoff (error n) (nonnegative n)
      (fun site depth sameDepth before => localBound n site depth sameDepth before _)
      site depth sameDepth within
    exact bound.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.sub_le horizon depth) (nonnegative n))

end GameTheory.Protocol.InformationModel

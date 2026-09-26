/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConditionalOneShot
import GameTheoryExtensions.Analysis.Protocol.ContinuationBranch

/-! # Approximate posterior one-shot deviations control whole policies

For a fully mixed Bayes assessment with perfect recall and common-depth
information sites, a bound on each local deviation gives the remaining
horizon times that bound for a whole continuation-policy deviation. The
proof telescopes deviating prefixes followed by the baseline continuation.
It keeps the starting branch's probability as a factor until the final
cancellation, so the estimate is uniform even at very rare information sets.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E) [Finite E.History]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]

/-- Only the fixed alternative's local laws need be tested. In particular,
passing to a consistent limit needs a finite maximum over information sites,
not an additional maximization over alternative policies or local lotteries. -/
theorem whole_policy_gain_le_of_local_gains
    (assessment : M.BehavioralAssessment) (recall : M.PerfectRecall)
    (mixed : assessment.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent M assessment
      (M.decisionInformationAntichain_of_perfectRecall recall))
    (who : Player) [DecidableEq (M.InfoState who)]
    (alternative : M.BehavioralPolicy who)
    (clock : ∀ site : M.InformationSite who,
      ∃ depth, InformationSite.CommonDepth M site depth)
    (horizon : Nat) (payoff : E.History → ℝ) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (localBound : ∀ (site : M.InformationSite who) (depth : Nat),
      InformationSite.CommonDepth M site depth → depth < horizon →
      (assessment.continuationContext site payoff (horizon - depth)).value
          ((assessment.strategy who).withLaw site.1 (alternative site.1)) -
        (assessment.continuationContext site payoff (horizon - depth)).value
          (assessment.strategy who) ≤ epsilon)
    (site : M.InformationSite who) (depth : Nat)
    (sameDepth : InformationSite.CommonDepth M site depth) (within : depth ≤ horizon) :
    (assessment.continuationContext site payoff (horizon - depth)).value alternative -
      (assessment.continuationContext site payoff (horizon - depth)).value
        (assessment.strategy who) ≤ (horizon - depth : Nat) * epsilon := by
  classical
  let switched := (assessment.strategy who).switchAt M alternative site
  let updated := Profile.update (sig := M.behavioralSignature) assessment.strategy who switched
  let remaining := horizon - depth
  let branch := fun info : M.InfoState who =>
    info = site.1 ∨ site.1 ∈ (M.recordAt who info).map Prod.fst
  let allowance := fun info : M.InfoState who => if branch info then epsilon else 0
  let value := fun step : Nat =>
    (M.runBehavioral updated (depth + step)).expect (fun history =>
      (M.runBehavioralFrom assessment.strategy (remaining - step) history).expect payoff)
  have oneStep (step : Nat) (before : step < remaining) :
      value (step + 1) - value step ≤ epsilon * M.informationMass assessment.strategy who site := by
    let suffix := remaining - (step + 1)
    have remainder : remaining - step = suffix + 1 := by dsimp [suffix]; omega
    have total : horizon - (depth + step) = suffix + 1 := by dsimp [suffix, remaining]; omega
    have atStep : depth + step < horizon := by dsimp [remaining] at before; omega
    have increments : value (step + 1) - value step =
        (M.runBehavioral updated (depth + step)).expect (fun history =>
          ((M.runBehavioralFrom updated 1 history).bind
            (M.runBehavioralFrom assessment.strategy suffix)).expect payoff -
          (M.runBehavioralFrom assessment.strategy (suffix + 1) history).expect payoff) := by
      dsimp only [value]
      rw [show depth + (step + 1) = (depth + step) + 1 by omega]
      change ((M.runBehavioralFrom updated ((depth + step) + 1) E.initHistory).expect _) - _ = _
      rw [M.runBehavioralFrom_add updated (depth + step) 1 E.initHistory,
        FinDist.expect_bind, remainder]
      simp_rw [FinDist.expect_bind]
      exact (FinDist.expect_sub _ _ _).symm
    rw [increments]
    have bound := M.one_step_gain_le_after_own_prefix assessment recall mixed bayes who
      switched clock (depth + step) suffix payoff allowance
      (fun info => by dsimp [allowance]; split <;> positivity)
      (fun current currentDepth => by
        by_cases inside : branch current.1
        · have localChoice : switched current.1 = alternative current.1 :=
            ite_eq_left inside
          rw [localChoice]
          change _ ≤ if branch current.1 then epsilon else 0
          rw [ite_eq_left inside, ← total]
          exact localBound current (depth + step) currentDepth atStep
        · have localChoice : switched current.1 = assessment.strategy who current.1 :=
            ite_eq_right inside
          rw [localChoice, BehavioralPolicy.withLaw_eq_self, sub_self]
          change 0 ≤ if branch current.1 then epsilon else 0
          rw [ite_eq_right inside])
    apply bound.trans_eq
    calc
      _ = (M.runBehavioral updated (depth + step)).expect (fun history =>
          epsilon * (if history ∈ M.continuationBranch who site then 1 else 0)) := by
        apply FinDist.expect_congr
        intro history _
        dsimp only [allowance, branch]
        rw [M.recordAt_eq_ownPlay recall, ← InfoSignals.actedAt_eq_map_ownPlay]
        simp only [continuationBranch, Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]
      _ = epsilon * (M.runBehavioral updated (depth + step)).probOf
          (M.continuationBranch who site) := by
        rw [FinDist.expect_smul, FinDist.expect_indicator_eq_probOf]
      _ = _ := by
        rw [M.switched_continuationBranch_probability recall assessment.strategy who site
          alternative depth sameDepth step]
  have summed := Finset.sum_le_sum (s := Finset.range remaining)
    (fun step member => oneStep step (Finset.mem_range.mp member))
  rw [Finset.sum_range_sub, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at summed
  have start : value 0 = (M.runBehavioral assessment.strategy horizon).expect payoff := by
    dsimp only [value]
    rw [Nat.add_zero, Nat.sub_zero,
      M.run_switchAt_prefix recall assessment.strategy who site alternative depth sameDepth,
      ← FinDist.expect_bind]
    change ((M.runBehavioralFrom assessment.strategy depth E.initHistory).bind
      (M.runBehavioralFrom assessment.strategy remaining)).expect payoff = _
    rw [← M.runBehavioralFrom_add]
    have total : depth + remaining = horizon := by dsimp [remaining]; omega
    rw [total]
    rfl
  have finish : value remaining = (M.runBehavioral updated horizon).expect payoff := by
    dsimp only [value]
    rw [Nat.sub_self]
    have total : depth + remaining = horizon := by dsimp [remaining]; omega
    rw [total]
    apply FinDist.expect_congr
    intro history _
    exact FinDist.expect_pure _ _
  rw [start, finish] at summed
  have positive := mixed.informationMass_pos who site
  have gain := M.switched_root_gain_eq_mass_mul_context_gain assessment recall who site
    depth remaining sameDepth positive (bayes who site positive) payoff alternative
  have total : depth + remaining = horizon := by dsimp [remaining]; omega
  rw [total] at gain
  rw [gain] at summed
  apply (mul_le_mul_iff_right₀ positive).mp
  convert summed using 1; ring

end GameTheory.Protocol.InformationModel

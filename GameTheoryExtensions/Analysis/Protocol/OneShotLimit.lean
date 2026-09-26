/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity
import GameTheoryExtensions.Analysis.Protocol.LocalDeviation

/-! # Vanishing local deviation gains in a consistent assessment limit

For a fixed alternative policy, only finitely many information-set deviations
matter. Continuity turns local optimality of the limit into a uniform vanishing
bound along its common approximating sequence. The approximating strategies
need not themselves be locally optimal.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E}
  [∀ who, DecidableEq (M.InfoState who)]

/-- Every fixed alternative's local gains vanish uniformly over the finite
decision sites. This allows source behavior to be pinned at finite trembles
even when only its limiting assessment is locally rational. -/
theorem BehavioralAssessmentConvergesPointwise.exists_vanishing_local_gain_bound
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : Player) [Finite (M.InformationSite who)]
    [∀ site : M.InformationSite who, Finite (M.InformationHistory who site.1)]
    (clock : ∀ site : M.InformationSite who,
      ∃ depth, InformationSite.CommonDepth M site depth)
    (horizon : Nat) (payoff : E.History → ℝ) (alternative : M.BehavioralPolicy who)
    (localOptimal : ∀ (site : M.InformationSite who) depth,
      InformationSite.CommonDepth M site depth → depth < horizon →
      (assessment.continuationContext site payoff (horizon - depth)).value
          ((assessment.strategy who).withLaw site.1 (alternative site.1)) ≤
        (assessment.continuationContext site payoff (horizon - depth)).value
          (assessment.strategy who)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : M.InformationSite who) depth,
        InformationSite.CommonDepth M site depth → depth < horizon →
        ((sequence n).continuationContext site payoff (horizon - depth)).value
            (((sequence n).strategy who).withLaw site.1 (alternative site.1)) -
          ((sequence n).continuationContext site payoff (horizon - depth)).value
            ((sequence n).strategy who) ≤ error n := by
  classical
  let _ := Fintype.ofFinite (M.InformationSite who)
  let depth (site : M.InformationSite who) := (clock site).choose
  have sameDepth (site : M.InformationSite who) :
      InformationSite.CommonDepth M site (depth site) := (clock site).choose_spec
  let gain (current : M.BehavioralAssessment) (site : M.InformationSite who) : ℝ :=
    if depth site < horizon then
      (current.continuationContext site payoff (horizon - depth site)).value
          ((current.strategy who).withLaw site.1 (alternative site.1)) -
        (current.continuationContext site payoff (horizon - depth site)).value
          (current.strategy who)
    else 0
  have gainNonpositive (site : M.InformationSite who) : gain assessment site ≤ 0 := by
    dsimp only [gain]
    split
    · rename_i before
      exact sub_nonpos.mpr (localOptimal site (depth site) (sameDepth site) before)
    · exact le_rfl
  have gainConverges (site : M.InformationSite who) :
      Tendsto (fun n => gain (sequence n) site) atTop (nhds (gain assessment site)) := by
    by_cases before : depth site < horizon
    · simp only [gain, ite_eq_left before]
      apply Filter.Tendsto.sub
      · apply converges.context_value reference mixed site payoff (horizon - depth site)
        intro decision
        by_cases same : decision = site
        · subst decision
          simpa only [BehavioralPolicy.withLaw_self] using
            finDistConvergesPointwise_const (alternative site.1)
        · have different : decision.1 ≠ site.1 := fun equal => same (Subtype.ext equal)
          simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
            converges.strategy who decision
      · exact converges.context_value reference mixed site payoff (horizon - depth site)
          (fun n => (sequence n).strategy who) (assessment.strategy who)
          (converges.strategy who)
    · simp only [gain, ite_eq_right before]
      exact tendsto_const_nhds
  let error (n : ℕ) : ℝ := ∑ site, max (gain (sequence n) site) 0
  have nonnegative (n : ℕ) : 0 ≤ error n :=
    Finset.sum_nonneg fun _ _ => le_max_right _ _
  have vanishes : Tendsto error atTop (nhds 0) := by
    have each (site : M.InformationSite who) :
        Tendsto (fun n => max (gain (sequence n) site) 0) atTop (nhds 0) := by
      simpa only [max_eq_right (gainNonpositive site)] using
        (gainConverges site).max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun site _ => each site)
  refine ⟨error, nonnegative, vanishes, ?_⟩
  intro n site atDepth uniformDepth before
  have same : depth site = atDepth :=
    (sameDepth site site.2.choose).symm.trans (uniformDepth site.2.choose)
  have bound : gain (sequence n) site ≤ error n :=
    (le_max_left _ _).trans (Finset.single_le_sum (fun _ _ => le_max_right _ _)
      (Finset.mem_univ site))
  simpa only [gain, same, ite_eq_left before] using bound

end GameTheory.Protocol.InformationModel

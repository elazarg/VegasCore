/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.BehavioralOneShot
import GameTheoryExtensions.Analysis.Protocol.OneShotLimit

/-! # Posterior one-shot deviations characterize sequential rationality

At a consistent assessment of a finite perfect-recall protocol with clocked
information sites, local optimality implies optimality against every whole
continuation policy. A common fully mixed Bayesian sequence supplies compatible
posteriors even at zero-probability sites. Its local regrets tend uniformly to
zero, and the finite-horizon deviation bound has no inverse reach factor.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E} [Finite E.History]
  [∀ who, DecidableEq (M.InfoState who)]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]

/-- Local optimality at every future information site rules out arbitrary
whole-policy deviations, including at off-path sites. Consistency is essential
for the common posterior relationships used by this implication. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.rationalAt_of_localOptimal
    {assessment : M.BehavioralAssessment} (perfectRecall : M.PerfectRecall)
    (consistent : assessment.IsSequentiallyConsistent
      (M.decisionInformationAntichain_of_perfectRecall perfectRecall))
    (who : Player)
    (clock : ∀ site : M.InformationSite who,
      ∃ depth, InformationSite.CommonDepth M site depth)
    (horizon : Nat) (payoff : E.History → ℝ)
    (localOptimal : ∀ (site : M.InformationSite who) depth,
      InformationSite.CommonDepth M site depth → depth < horizon →
      ∀ law : FinDist (M.Choice who site.1),
        (assessment.continuationContext site payoff (horizon - depth)).value
            ((assessment.strategy who).withLaw site.1 law) ≤
          (assessment.continuationContext site payoff (horizon - depth)).value
            (assessment.strategy who))
    (site : M.InformationSite who) (depth : Nat)
    (sameDepth : InformationSite.CommonDepth M site depth) (within : depth ≤ horizon) :
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff (horizon - depth)) := by
  obtain ⟨sequence, approximates, converges⟩ := consistent
  intro alternative _
  obtain ⟨error, nonnegative, vanishes, localBound⟩ :=
    converges.exists_vanishing_local_gain_bound (sequence 0) (approximates 0).1
      who clock horizon payoff alternative
      (fun current atDepth uniformDepth before =>
        localOptimal current atDepth uniformDepth before (alternative current.1))
  have first := converges.context_value (sequence 0) (approximates 0).1 site payoff
    (horizon - depth) (fun _ => alternative) alternative
    (fun _ => finDistConvergesPointwise_const _)
  have second := converges.context_value (sequence 0) (approximates 0).1 site payoff
    (horizon - depth) (fun n => (sequence n).strategy who) (assessment.strategy who)
    (converges.strategy who)
  have boundLimit : Tendsto (fun n => (horizon - depth : Nat) * error n) atTop (nhds 0) := by
    simpa only [mul_zero] using vanishes.const_mul ((horizon - depth : Nat) : ℝ)
  apply sub_nonpos.mp
  exact le_of_tendsto_of_tendsto (first.sub second) boundLimit
    (Eventually.of_forall fun n =>
      M.whole_policy_gain_le_of_local_gains (sequence n) perfectRecall
        (approximates n).1 (approximates n).2 who alternative clock horizon payoff
        (error n) (nonnegative n) (localBound n) site depth sameDepth within)

/-- The standard assessment predicate, with remaining fuel determined by the
public decision clock, follows from one-shot comparisons at all sites. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.sequentiallyRational_of_localOptimal
    {assessment : M.BehavioralAssessment} (perfectRecall : M.PerfectRecall)
    (consistent : assessment.IsSequentiallyConsistent
      (M.decisionInformationAntichain_of_perfectRecall perfectRecall))
    (horizon : Nat) (payoff : Player → E.History → ℝ)
    (depth : ∀ who, M.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth M site (depth who site))
    (within : ∀ who site, depth who site ≤ horizon)
    (localOptimal : ∀ who (site : M.InformationSite who), depth who site < horizon →
      ∀ law : FinDist (M.Choice who site.1),
        (assessment.continuationContext site (payoff who) (horizon - depth who site)).value
            ((assessment.strategy who).withLaw site.1 law) ≤
          (assessment.continuationContext site (payoff who) (horizon - depth who site)).value
            (assessment.strategy who)) :
    assessment.IsSequentiallyRational fun who site =>
      assessment.continuationContext site (payoff who) (horizon - depth who site) := by
  intro who site
  apply consistent.rationalAt_of_localOptimal perfectRecall who
    (fun current => ⟨depth who current, clock who current⟩) horizon (payoff who)
      _ site (depth who site) (clock who site) (within who site)
  intro current atDepth uniformDepth before law
  have same : depth who current = atDepth :=
    (clock who current current.2.choose).symm.trans (uniformDepth current.2.choose)
  simpa only [same] using localOptimal who current (by omega) law

end GameTheory.Protocol.InformationModel

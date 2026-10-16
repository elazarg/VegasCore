/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoverySuccessLimit
import Vegas.Game.CommitRecoveryPooledOrdinaryLimit

/-! # Original source domain regret conditional on successful first close

The original pooled sequence supplies ordinary limit optimality. Its same
varying domain prescription and every fixed domain alternative retain the
actual success-induced history tilt; their conditional regret has nonpositive
limit superior. No success-mass floor or new domain optimizer is supplied.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

section Components

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  [Fintype setup.commitRecoveryProtocol.History]
  (omission bad floor : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (floorNonnegative : ∀ n, 0 ≤ floor n) (floorBounded : ∀ n, floor n ≤ 1)
  (pins : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
    Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (badVanishes : Tendsto bad atTop (nhds 0))
  (floorVanishes : Tendsto floor atTop (nhds 0))

include omissionVanishes badVanishes floorVanishes

open Classical in
/-- The same original prescribed domain sequence has vanishing positive
regret under actual success conditioning at every ordinary unpinned valued
source site. The finite-stage premise is the original whole-pool inequality. -/
theorem commitRecovery_pooled_ordinary_success_regret
    (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (limit : setup.commitRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel (sequence n) setup.commitRecoveryModel_decisionAntichain)
    (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
            (floorBounded n) (pins n) (weights n)) who
              (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.commitRecoveryAgentPool finite agent = pool),
        setup.commitRecoveryComponentGain finite (sequence n)
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (floor n) (floorNonnegative n) (floorBounded n) (pins n)
          alternative utility excludedPayoff agent ≤ 0)
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal)
    (committing : source.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (ordinary : source.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal source.1)
    (unpinned : ∀ n, pins n (setup.commitRecoveryAgentPool finite
      (setup.commitRecoveryModel.agentAt source)) = none)
    (law : PMF (setup.CommitRecoveryPoolPart finite
      (setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source))))
    (regular : ∀ history : setup.commitRecoveryModel.InformationHistory focal source.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧
        first.excluded = first.entryExcluded ∧
        ProtocolState.BindingsHoldValues focal setup.program first.point) :
    let values := fun n => setup.commitRecoveryPooledDomainLaw finite (floor n)
      (floorNonnegative n) (floorBounded n) (pins n) (weights n)
    let current := fun n => setup.commitRecoveryNormalizedDomainLaw (values n) focal source.1
    let alternative : PMF (setup.CommitRecoveryValueChoice focal source.1) :=
      law.map (fun part =>
        ⟨(setup.commitRecoveryNoMissErasedChoice focal source.1).symm part.val, part.property⟩)
    let success := fun n choice => setup.commitRecoverySuccessValue
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n) (sequence n)
        focal source choice utility excludedPayoff
    limsup (fun n => success n alternative - success n (current n)) atTop ≤ 0 ∧
      ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ n in atTop,
        success n alternative - success n (current n) ≤ tolerance := by
  classical
  intro values current alternative success
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let total := ∑ history : setup.commitRecoveryProtocol.History, |payoff history|
  have totalBound (history : setup.commitRecoveryProtocol.History) : |payoff history| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ history)
  have totalNonnegative : 0 ≤ total := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have alternativeLimit := setup.commitRecoverySuccessValue_tendsto
    omission bad omissionNonnegative omissionBounded badNonnegative badBounded
    omissionVanishes badVanishes values sequence limit converges prescribed focal source regular
    (fun _ => alternative) (alternative.map Subtype.val)
    (pmfConvergesPointwise_const (alternative.map Subtype.val))
    utility excludedPayoff total totalNonnegative totalBound
  have currentLaw := setup.commitRecoveryNormalizedDomainLaw_converges
    omission bad omissionNonnegative omissionBounded badNonnegative badBounded
    omissionVanishes badVanishes values sequence limit converges prescribed focal source
  have currentLimit := setup.commitRecoverySuccessValue_tendsto
    omission bad omissionNonnegative omissionBounded badNonnegative badBounded
    omissionVanishes badVanishes values sequence limit converges prescribed focal source regular
    current (limit.strategy focal source.1) currentLaw utility excludedPayoff
    total totalNonnegative totalBound
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at currentLimit
  have optimal := setup.commitRecovery_pooled_ordinary_limit_domain_optimal finite
    omission bad floor omissionNonnegative omissionBounded badNonnegative badBounded
    floorNonnegative floorBounded pins omissionVanishes badVanishes floorVanishes
    sequence limit converges mixed bayes weights prescribed utility excludedPayoff pooled
    focal source committing ordinary unpinned law
  have difference := alternativeLimit.sub currentLimit
  change Tendsto (fun n => success n alternative - success n (current n)) atTop _ at difference
  let context := limit.continuationContext
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories source payoff
  let gap := context.value ((limit.strategy focal).withLaw source.1
    (alternative.map Subtype.val)) - context.value (limit.strategy focal)
  have gapNonpositive : gap ≤ 0 := by
    simpa only [gap, context, payoff, alternative, PMF.map_comp, Function.comp_def] using
      sub_nonpos.mpr optimal
  change Tendsto (fun n => success n alternative - success n (current n))
    atTop (nhds gap) at difference
  refine ⟨?_, ?_⟩
  · rw [difference.limsup_eq]
    exact gapNonpositive
  · intro tolerance positive
    exact (difference.eventually (gt_mem_nhds
      (lt_of_le_of_lt gapNonpositive positive))).mono (fun _ below => below.le)

open Classical in
/-- Finiteness of the genuine domain menu makes the same conditional regret
bound uniform over pure values, including a value selected separately at each
index of the original sequence. -/
theorem commitRecovery_pooled_ordinary_success_regret_uniform
    (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (limit : setup.commitRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel (sequence n) setup.commitRecoveryModel_decisionAntichain)
    (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
            (floorBounded n) (pins n) (weights n)) who
              (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.commitRecoveryAgentPool finite agent = pool),
        setup.commitRecoveryComponentGain finite (sequence n)
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (floor n) (floorNonnegative n) (floorBounded n) (pins n)
          alternative utility excludedPayoff agent ≤ 0)
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal)
    (committing : source.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (ordinary : source.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal source.1)
    (unpinned : ∀ n, pins n (setup.commitRecoveryAgentPool finite
      (setup.commitRecoveryModel.agentAt source)) = none)
    (regular : ∀ history : setup.commitRecoveryModel.InformationHistory focal source.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧
        first.excluded = first.entryExcluded ∧
        ProtocolState.BindingsHoldValues focal setup.program first.point) :
    let values := fun n => setup.commitRecoveryPooledDomainLaw finite (floor n)
      (floorNonnegative n) (floorBounded n) (pins n) (weights n)
    let current := fun n => setup.commitRecoveryNormalizedDomainLaw (values n) focal source.1
    let success := fun n choice => setup.commitRecoverySuccessValue
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n) (sequence n)
        focal source choice utility excludedPayoff
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ n in atTop,
      ∀ part : setup.CommitRecoveryPoolPart finite
        (setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source)),
        success n (PMF.pure
          ⟨(setup.commitRecoveryNoMissErasedChoice focal source.1).symm part.val, part.property⟩) -
          success n (current n) ≤ tolerance := by
  classical
  intro values current success tolerance positive
  let pool := setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source)
  let _ := setup.commitRecoveryValueChoice_finite finite pool.1 pool.2.val
  apply Filter.eventually_all.mpr
  intro part
  have individual := (setup.commitRecovery_pooled_ordinary_success_regret finite
    omission bad floor omissionNonnegative omissionBounded badNonnegative badBounded
    floorNonnegative floorBounded pins omissionVanishes badVanishes floorVanishes
    sequence limit converges mixed bayes weights prescribed utility excludedPayoff pooled
    focal source committing ordinary unpinned (PMF.pure part) regular).2 tolerance positive
  simpa only [PMF.pure_map] using individual

end Components

end Vegas.SourceProgram.Setup

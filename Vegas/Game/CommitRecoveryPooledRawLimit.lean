/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryRawLimit

/-! # Individual raw optimality of free ordinary source pools

The actual whole-pool completion inequalities control every original raw
current-law deviation at the same limit. The proof derives domain comparisons
from the actual components and uses the original accepted-failure coupling.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

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
/-- Every original raw local lottery is unprofitable at a free ordinary
site of the actual source limit, derived from the SAME whole-pool bounds.
Neither domain optimality nor any failure comparison is supplied as a premise. -/
theorem commitRecovery_pooled_ordinary_limit_localOptimal
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
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (law : PMF (setup.commitRecoveryModel.Choice focal source.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw source.1 law) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  apply setup.commitRecovery_normalized_limit_localOptimal_of_domain finite sequence limit
    converges omission bad omissionNonnegative omissionBounded badNonnegative badBounded
    (fun n => setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
      (floorBounded n) (pins n) (weights n)) prescribed utility excludedPayoff below
    focal source committing _ law
  intro domain
  let toPart : setup.CommitRecoveryValueChoice focal source.1 →
      setup.CommitRecoveryPoolPart finite (setup.commitRecoveryAgentPool finite
        (setup.commitRecoveryModel.agentAt source)) := fun choice =>
    ⟨setup.commitRecoveryNoMissErasedChoice focal source.1 choice.val, choice.property⟩
  have bound := setup.commitRecovery_pooled_ordinary_limit_domain_optimal finite
    omission bad floor omissionNonnegative omissionBounded badNonnegative badBounded
    floorNonnegative floorBounded pins omissionVanishes badVanishes floorVanishes
    sequence limit converges mixed bayes weights prescribed utility excludedPayoff
    pooled focal source committing ordinary unpinned (domain.map toPart)
  have sameLaw : (domain.map toPart).map
      (fun part => (setup.commitRecoveryNoMissErasedChoice focal source.1).symm part.val) =
        domain.map Subtype.val := by
    rw [PMF.map_comp]
    congr 1
  rwa [sameLaw] at bound

end Vegas.SourceProgram.Setup

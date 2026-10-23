/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryOrdinaryLimit
import Vegas.Game.ProposalRecoveryCommitLimit

/-! # Full legal ordinary-site incentives from the same pooled inequalities -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

section Components

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  [Fintype setup.proposalRecoveryProtocol.History]
  (omission bad delivery floor : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (deliveryNonnegative : ∀ n, 0 ≤ delivery n) (deliveryBounded : ∀ n, delivery n ≤ 1)
  (floorNonnegative : ∀ n, 0 ≤ floor n) (floorBounded : ∀ n, floor n ≤ 1)
  (pins : ℕ → (pool : setup.ProposalRecoveryValuePool) →
    Option (PMF (setup.ProposalRecoveryPoolPart pool)))
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (badVanishes : Tendsto bad atTop (nhds 0))
  (deliveryVanishes : Tendsto delivery atTop (nhds 0))
  (floorVanishes : Tendsto floor atTop (nhds 0))

include omissionVanishes badVanishes deliveryVanishes floorVanishes

open Classical in
theorem proposalRecovery_pooled_ordinary_limit_localOptimal
    (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
    (limit : setup.proposalRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel (sequence n) setup.proposalRecoveryModel_decisionAntichain)
    (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
          (setup.proposalRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
            (floorBounded n) (pins n) (weights n)) who
              (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.proposalRecoveryAgentPool agent = pool),
        setup.proposalRecoveryComponentGain finite (sequence n)
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
          (floor n) (floorNonnegative n) (floorBounded n) (pins n)
          alternative utility excludedPayoff agent ≤ 0)
    (focal : Player) (source : setup.proposalRecoveryModel.InformationSite focal)
    (first : CommitRecoveryState setup.program)
    (firstTrace : setup.proposalRecoveryProtocol.Trace (some first))
    (sourceAt : setup.proposalRecoveryModel.infoOf focal firstTrace = source.1)
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (ordinary : first.excluded = first.entryExcluded)
    (unpinned : ∀ n, pins n (setup.proposalRecoveryAgentPool
      (setup.proposalRecoveryModel.agentAt source)) = none)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (law : PMF (setup.proposalRecoveryModel.Choice focal source.1)) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw source.1
          law) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  apply setup.proposalRecovery_normalized_limit_localOptimal_of_domain finite sequence limit
    converges omission bad delivery omissionNonnegative omissionBounded badNonnegative badBounded
    deliveryNonnegative deliveryBounded
    (fun n => setup.proposalRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
      (floorBounded n) (pins n) (weights n)) prescribed utility excludedPayoff below
    focal source (by
      have clock := setup.commitRecovery_atCommit_info focal
        (setup.proposalRecoveryEraseTrace firstTrace)
      rw [← setup.proposalRecoveryEraseInfo_observed, sourceAt] at clock
      exact clock.trans committing) _ law
  intro domain
  let toPart : setup.CommitRecoveryValueChoice focal
      (setup.proposalRecoveryEraseInfo focal source.1) →
      setup.ProposalRecoveryPoolPart
        (setup.proposalRecoveryAgentPool
          (setup.proposalRecoveryModel.agentAt source)) := fun choice =>
    ⟨setup.commitRecoveryNoMissErasedChoice focal
      (setup.proposalRecoveryEraseInfo focal source.1) choice.val, choice.property⟩
  have bound := setup.proposalRecovery_pooled_ordinary_limit_domain_optimal finite
    omission bad delivery floor omissionNonnegative omissionBounded badNonnegative badBounded
    deliveryNonnegative deliveryBounded floorNonnegative floorBounded pins
    omissionVanishes badVanishes deliveryVanishes floorVanishes
    sequence limit converges mixed bayes weights prescribed utility excludedPayoff pooled
    focal source first firstTrace sourceAt committing ordinary unpinned (domain.map toPart)
  have sameLaw : (domain.map toPart).map
      (fun part => (setup.proposalRecoveryComponentChoice focal source.1).symm
        (setup.proposalRecoveryComponentLabelChoice focal
          (setup.proposalRecoveryQuery focal source.1) false part.val)) =
      domain.map (fun choice =>
        setup.proposalRecoveryLabelChoice focal source.1 false choice.val) := by
    rw [PMF.map_comp]
    congr 1
  rwa [sameLaw] at bound

end Components

end Vegas.SourceProgram.Setup

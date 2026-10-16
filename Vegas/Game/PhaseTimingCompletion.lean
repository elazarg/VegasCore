/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPools
import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion

/-! # One common assessment witness for actual phased timing pools -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

open Classical in
/-- All operational pools use the same weights, fully mixed approximants,
Bayes assessments and subsequence. Pool optimality concerns the sum of actual
member gains. Member optimality, source likelihood transport and a sequential
equilibrium conclusion require additional derived estimates. -/
theorem exists_phase_timing_completion (wellFormed : setup.WellFormed)
    (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℕ → ℝ) (positive : ∀ n, 0 < noise n) (noiseBounded : ∀ n, noise n ≤ 1)
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let parts := PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
    let pools := phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
    let laws := fun n => phaseTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed (sourceSequence n) (noise n) (positive n).le (noiseBounded n)
        (slotWeight n) (slotNonnegative n) (slotBounded n)
    let fallback : ∀ who, (N).Policy who := fun _ _ => Classical.arbitrary _
    let certificate := (menu).bounded initial horizon scheduler |>.wellFoundedHistories
    let payoff := fun who (final : (menu).protocol initial horizon scheduler |>.History) =>
      phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who
    ∃ (weights : ℕ → ∀ p, PMF (parts p)) (sequence : ℕ → (N).BehavioralAssessment)
      (limit : (N).BehavioralAssessment) (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = (N).agentBehavior (N).playedInformation fallback
        fun agent => (weights n (pools agent)).bind (laws n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent (N) (sequence n)
        ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent
        ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain ∧
      (∀ n (alternative : ∀ p, PMF (parts p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pools agent = p),
          (if decision : (N).IsDecisionInfo agent.1 agent.2.1 then
            ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pools agent)).bind (laws n agent))) -
              ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) ∧
      ∀ who (site : (N).InformationSite who)
        (limitComponent : parts (pools ((N).agentAt site)) → PMF ((N).Choice who site.1)),
        (∀ part, PMFConvergesPointwise (fun n => laws n ((N).agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (parts (pools ((N).agentAt site))),
          limit.strategy who site.1 = limitWeights.bind limitComponent) ∧
        ∀ (error : ℕ → ℝ), Filter.Tendsto error Filter.atTop (nhds 0) →
          (∀ n (alternative : PMF (parts (pools ((N).agentAt site)))),
            ((sequence n).continuationContext certificate site (payoff who)).value
                (((sequence n).strategy who).withLaw site.1
                  (alternative.bind (laws n ((N).agentAt site)))) ≤
              ((sequence n).continuationContext certificate site (payoff who)).value
                ((sequence n).strategy who) + error n) →
          ∀ alternative : PMF (parts (pools ((N).agentAt site))),
            (limit.continuationContext certificate site (payoff who)).value
                ((limit.strategy who).withLaw site.1 (alternative.bind limitComponent)) ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who) := by
  intro parts pools laws fallback certificate payoff
  exact (N).exists_consistent_pooled_completion
    ((menu).decisionRecall initial horizon scheduler) fallback certificate payoff pools laws
    (fun n agent part => phaseTimingComponent_fullSupport setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (sourceSequence n) (noise n) (positive n)
        (noiseBounded n) (slotWeight n) (slotNonnegative n) (slotBounded n) agent part)

end Vegas

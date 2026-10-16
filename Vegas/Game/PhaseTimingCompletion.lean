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
Bayes assessments and subsequence. Public-exclusion sites are rational for
whole continuations when raw noise vanishes. Pool optimality concerns the sum
of actual member gains. Keyed-member optimality, source likelihood transport and a sequential
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
      (Filter.Tendsto noise Filter.atTop (nhds 0) →
        ∀ who (site : (N).InformationSite who),
          PhasePublicExclusion setup mode runtime leaks site.1 →
            ∀ alternative : (N).BehavioralPolicy who,
              (limit.continuationContext certificate site (payoff who)).value alternative ≤
                (limit.continuationContext certificate site (payoff who)).value
                  (limit.strategy who)) ∧
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
  obtain ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
      consistent, pooled, limitFacts⟩ := (N).exists_consistent_pooled_completion
    ((menu).decisionRecall initial horizon scheduler) fallback certificate payoff pools laws
    (fun n agent part => phaseTimingComponent_fullSupport setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (sourceSequence n) (noise n) (positive n)
        (noiseBounded n) (slotWeight n) (slotNonnegative n) (slotBounded n) agent part)
  refine ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
    consistent, ?_, pooled, limitFacts⟩
  intro vanishes
  apply wholePolicyOptimal_of_phasePublicExclusion setup mode runtime leaks menu initial horizon
    scheduler certificate payoff limit consistent
  intro who site excluded alternative
  rcases site with ⟨input, decision⟩
  let site : (N).InformationSite who := ⟨input, decision⟩
  let identify := freeIdentify (agent := (N).agentAt site)
    (free := fun agent : (N).InformationAgent (N).playedInformation =>
      PhasePublicExclusion setup mode runtime leaks agent.2.1)
    (keyed := fun agent => PhaseUnprotected runtime leaks bound agent.1 agent.2.1)
    (key := fun agent => phaseTimingKey runtime leaks agent.1 agent.2.1)
    (Opt := LateOption bounds.candidateCount) excluded
  let limitComponent := fun part => PMF.pure (identify part)
  have componentConverges : ∀ part, PMFConvergesPointwise
      (fun n => laws n ((N).agentAt site) part) (limitComponent part) := by
    intro part
    exact phaseTimingComponent_free_converges setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed sourceSequence noise (fun n => (positive n).le) noiseBounded
        vanishes slotWeight slotNonnegative slotBounded ((N).agentAt site) excluded part
  have localOptimal := (limitFacts who site limitComponent componentConverges).2
    (fun _ => 0) tendsto_const_nhds (fun n replacement => by
      have single : Finset.univ.filter (fun agent => pools agent = pools ((N).agentAt site)) =
          {(N).agentAt site} := by
        ext agent
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro same
          change freeKeyedPool _ _ _ agent = freeKeyedPool _ _ _ ((N).agentAt site) at same
          rw [freeKeyedPool_of_free (agent := (N).agentAt site) excluded] at same
          exact eq_of_freeKeyedPool_eq_inl same
        · rintro rfl
          rfl
      have bound := pooled n
        (Function.update (weights n) (pools ((N).agentAt site)) replacement)
          (pools ((N).agentAt site))
      rw [single, Finset.sum_singleton, dite_eq_left site.2] at bound
      simp only [Function.update_self] at bound
      simpa only [add_zero, site] using sub_nonpos.mp bound)
  have spanning : (alternative.map identify.symm).bind limitComponent = alternative := by
    rw [PMF.bind_map]
    change alternative.bind (fun choice => PMF.pure (identify (identify.symm choice))) = alternative
    simp only [Equiv.apply_symm_apply, PMF.bind_pure]
  have optimal := localOptimal (alternative.map identify.symm)
  rw [spanning] at optimal
  exact optimal

end Vegas

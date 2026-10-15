/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePerturbation
import Vegas.Game.PhasePublicCompletion
import GameTheory.Analysis.Protocol.AgentCompletion

/-! # A common native assessment retaining source recipes before exclusion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

open Classical in
/-- One actual native sequence and one common subsequential limit retain the
fully mixed source/slot recipe at every clear decision input. Every decision
after public exclusion is completed optimally for the actual physical payoff.
Clear-site incentive comparisons and the intended joint law are separate. -/
theorem exists_phase_source_assessment_completion (wellFormed : setup.WellFormed)
    (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℕ → ℝ) (positive : ∀ n, 0 < noise n) (small : ∀ n, noise n < 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let fallback : ∀ who, (N).Policy who := fun _ _ => Classical.arbitrary _
    let certificate := (menu).bounded initial horizon scheduler |>.wellFoundedHistories
    let free := Finset.univ.filter fun agent : (N).InformationAgent (N).playedInformation =>
      PhasePublicExclusion setup mode runtime leaks agent.2.1
    let pinned := fun n (agent : (N).InformationAgent (N).playedInformation) =>
      phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed (sourceSequence n) (noise n) (positive n).le (small n).le
          (slotWeight n) (slotNonnegative n) (slotBounded n) agent.1 agent.2.1
    let reference := fun agent : (N).InformationAgent (N).playedInformation =>
      (menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1
    let payoff := fun who (final : (E).History) =>
      phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who
    ∃ (residual : ℕ → Profile ((N).agentForm fallback certificate).sig.mixed)
      (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = (N).agentBehavior (N).playedInformation fallback
        (pinnedTremble free (pinned n) reference (residual n) (noise n) (positive n).le
          (small n).le)) ∧
      (∀ n who (site : (N).InformationSite who),
        ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
          (sequence n).strategy who site.1 = pinned n ((N).agentAt site)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent (N) (sequence n)
        ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent
        ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain ∧
      ∀ who (site : (N).InformationSite who),
        PhasePublicExclusion setup mode runtime leaks site.1 →
          ∀ alternative : (N).BehavioralPolicy who,
            (limit.continuationContext certificate site (payoff who)).value alternative ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who) := by
  intro fallback certificate free pinned reference payoff
  have pinnedFull (n : Nat) (agent : (N).InformationAgent (N).playedInformation)
      (_outside : agent ∉ free) : FullSupport (pinned n agent) :=
    phaseSourcePerturbedStrategy_fullSupport setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (sourceSequence n) (noise n) (positive n) (small n).le
        (slotWeight n) (slotNonnegative n) (slotBounded n) agent.1 agent.2.1
  have referenceFull (agent : (N).InformationAgent (N).playedInformation) :
      FullSupport (reference agent) := by
    intro choice
    let := Fintype.ofFinite ((N).Choice agent.1 agent.2.1)
    exact PMF.mem_support_uniformOfFintype choice
  obtain ⟨residual, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
      consistent, localOptimal⟩ :=
    (N).exists_consistent_free_agent_completion ((menu).decisionRecall initial horizon scheduler)
      fallback certificate payoff free pinned reference pinnedFull referenceFull noise positive
        small vanishes
  refine ⟨residual, sequence, limit, index, assembled, ?_, mixed, bayes, increasing, converges,
    consistent, ?_⟩
  · intro n who site clear
    have outside : (N).agentAt site ∉ free := by
      simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and] using clear
    rw [assembled n]
    exact ((N).agentBehavior_at (N).playedInformation fallback _ ((N).agentAt site)).trans
      (ite_eq_right outside)
  · intro who site excluded alternative
    apply wholePolicyOptimal_of_phasePublicExclusion setup mode runtime leaks
      (menu) initial horizon scheduler certificate payoff limit consistent ?_ who site excluded
        alternative
    intro player later flagged law
    apply localOptimal player later
    simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and] using flagged

end Vegas

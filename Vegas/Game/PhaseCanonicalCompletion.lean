/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceCompletionOutcome
import Vegas.Game.PhaseCanonicalSourceLaw

/-! # Source outcomes of one common completed physical assessment -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat)
  (scheduler : (phaseApplication (serviceRuntime setup mode deadline) leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (sourceLimit : setup.commitRecoveryModel.BehavioralAssessment)
  (sourceConvergence : BehavioralAssessmentConvergesPointwise sourceSequence sourceLimit)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source sourceLimit.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (sourceLimit.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)

local notation "R" => serviceRuntime setup mode deadline
local notation "app" => phaseApplication R leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu R leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu R leaks bounds) (start) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu R leaks bounds) (start) horizon scheduler
local notation "canonical" => phaseSourceStrategy setup mode R leaks bounds wellFormed
  sourceLimit (start) horizon scheduler
local notation "players" => phaseSourcePolicy setup mode R leaks bounds wellFormed sourceLimit
local notation "structural" => setup.decodeBehavioralProfile
  (CommitmentInterface.values setup.program) (setup.openingExtension source)

variable (delay bound : (serviceGraph setup mode).EventId → Nat)
  (asyncService : PhaseService.AsyncContract (serviceRuntime setup mode deadline) leaks
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler delay bound)
  (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
  (values : ∀ event who payload,
    ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

include maximal capacity sourceConvergence copies continuing asyncService timely values

open Classical in
/-- One unchanged completion has its common fully mixed Bayes approximations,
consistent limit and excluded-site continuation optimality, together with the
original source outcomes and uncharged randomized settlement. No clear-site
rationality or sequential-equilibrium conclusion is asserted. -/
theorem exists_phase_source_completion_with_source_law
    [Finite (E).History]
    (noise : ℕ → ℝ) (positive : ∀ n, 0 < noise n) (small : ∀ n, noise n < 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff deposit : Player → ℝ)
    (report : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup mode))) :
    let certificate := ((menu).bounded (start) horizon scheduler).wellFoundedHistories
    let payoff := fun who (final : (E).History) =>
      phaseExclusionBase setup mode R leaks utility excludedPayoff final.state who
    ∃ (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n who (site : (N).InformationSite who),
        ¬ PhasePublicExclusion setup mode R leaks site.1 →
          (sequence n).strategy who site.1 =
            phaseSourcePerturbedStrategy setup mode R leaks bounds (start) horizon scheduler
              wellFormed (sourceSequence n) (noise n) (positive n).le (small n).le
                (slotWeight n) (slotNonnegative n) (slotBounded n) who site.1) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent (N) (sequence n)
        ((menu).decisionRecall (start) horizon scheduler).decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent
        ((menu).decisionRecall (start) horizon scheduler).decisionInformationAntichain ∧
      (∀ who (site : (N).InformationSite who),
        PhasePublicExclusion setup mode R leaks site.1 →
          ∀ alternative : (N).BehavioralPolicy who,
            (limit.continuationContext certificate site (payoff who)).value alternative ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who)) ∧
      (N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory =
        (N).runBehavioralTerminalFrom certificate canonical (E).initHistory ∧
      ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).map
        (fun final => phaseSourceReadout setup mode R leaks final.state) =
          (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map some ∧
      ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).map
        (fun final => (phaseSourceReadout setup mode R leaks final.state,
          phaseExclusionBase setup mode R leaks utility excludedPayoff final.state)) =
        (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map
          (fun terminal => (some terminal, utility terminal)) ∧
      ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).bind
        (fun final =>
          (TerminalAudit.settlement (phaseExclusionBase setup mode R leaks utility excludedPayoff)
            (app).stateTraffic (PhaseCount.audit R leaks report.sample) deposit final.state).map
              (fun payoffs => (phaseSourceReadout setup mode R leaks final.state, payoffs))) =
        (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map
          (fun terminal => (some terminal, utility terminal)) ∧
      ∀ final ∈ ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).support,
        ∃ current : (app).Control, final.state = some current ∧
          current.execution.application.current.excluded = ∅ ∧
          ∀ who, TerminalAudit.charge (app).stateTraffic
            (PhaseCount.audit R leaks report.sample) final.state who = 0 := by
  intro certificate payoff
  have initialEq :
      PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs) = (start) :=
    PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
  have service : PhaseService.AsyncContract R leaks
      (PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs))
        horizon scheduler delay bound := by
    rw [initialEq]
    exact asyncService
  have safe : ∀ (current : (app).Control) (_trace : (E).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅ := by
    have law := phaseSourcePolicy_clear_history setup mode deadline leaks source bounds wellFormed
        sourceLimit copies continuing plan (serviceGraph_revealRelaxedOrdered setup mode) maximal
          horizon scheduler capacity delay bound service.opportunity service.inclusion timely
            values
    rw [initialEq] at law
    exact law
  obtain ⟨sequence, limit, index, recipe, mixed, bayes, increasing, converges, consistent,
      optimal, historyLaw⟩ := exists_phase_source_completion_with_history_law setup mode R leaks
    bounds wellFormed plan maximal horizon scheduler sourceSequence sourceLimit sourceConvergence
      noise positive small vanishes slotWeight slotNonnegative slotBounded slotVanishes safe
        utility excludedPayoff
  refine ⟨sequence, limit, index, recipe, mixed, bayes, increasing, converges, consistent,
    optimal, historyLaw, ?_, ?_, ?_, ?_⟩
  · rw [historyLaw]
    have law := phaseSourceStrategy_async_terminal_source_law setup mode deadline leaks source
      bounds wellFormed sourceLimit copies continuing plan maximal horizon scheduler capacity delay
          bound service timely values
    rw [initialEq] at law
    exact law
  · rw [historyLaw]
    have law := phaseSourceStrategy_async_terminal_source_payoff_law setup mode deadline leaks
      source bounds wellFormed sourceLimit copies continuing plan maximal horizon scheduler
        capacity delay bound service timely values utility excludedPayoff
    rw [initialEq] at law
    exact law
  · rw [historyLaw]
    have law := phaseSourceStrategy_async_terminal_settlement_law setup mode deadline leaks source
      bounds wellFormed sourceLimit copies continuing plan maximal horizon scheduler capacity delay
          bound service timely values utility excludedPayoff deposit report
    rw [initialEq] at law
    exact law
  · have canonicalClear : ∀ final : (E).History,
        final ∈ ((N).runBehavioralTerminalFrom certificate canonical (E).initHistory).support →
          ∃ current : (app).Control, final.state = some current ∧
            current.execution.application.current.excluded = ∅ ∧
            ∀ who, TerminalAudit.charge (app).stateTraffic
              (PhaseCount.audit R leaks report.sample) final.state who = 0 := by
      have law := phaseSourceStrategy_async_terminal_clear_uncharged setup mode deadline leaks
        source bounds wellFormed sourceLimit copies continuing plan maximal horizon scheduler
          capacity delay bound service timely values report
      rw [initialEq] at law
      exact law
    intro final supported
    rw [historyLaw] at supported
    exact canonicalClear final supported

end Vegas

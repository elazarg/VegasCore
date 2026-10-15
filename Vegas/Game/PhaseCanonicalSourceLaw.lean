/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCanonicalSafety
import Vegas.Game.PhaseCompiledBehavioralLaw
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # Original source laws under the physical asynchronous service contract -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (assessment.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat)
  (scheduler : (phaseApplication (serviceRuntime setup mode deadline) leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)

local notation "R" => serviceRuntime setup mode deadline
local notation "P" => phaseApplication R leaks
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan) inputs
local notation "menu" => PhaseCount.onePacketMenu R leaks bounds
local notation "players" => phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
local notation "strategy" => phaseSourceStrategy setup mode R leaks bounds wellFormed
  assessment initial horizon scheduler
local notation "certificate" => BoundedHorizon.wellFoundedHistories
  (ReactiveApplication.ResponseMenu.bounded (PhaseCount.onePacketMenu R leaks bounds)
    initial horizon scheduler)
local notation "structural" => setup.decodeBehavioralProfile
  (CommitmentInterface.values setup.program) (setup.openingExtension source)
local notation "terminalLaw" => InformationModel.runBehavioralTerminalFrom
  (ReactiveApplication.ResponseMenu.information (PhaseCount.onePacketMenu R leaks bounds)
    initial horizon scheduler) certificate strategy
  (ExecutionProtocol.initHistory
    (ReactiveApplication.ResponseMenu.protocol (PhaseCount.onePacketMenu R leaks bounds)
      initial horizon scheduler))

variable (delay bound : (serviceGraph setup mode).EventId → Nat)
  (asyncService : PhaseService.AsyncContract (serviceRuntime setup mode deadline) leaks
    (PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs))
      horizon scheduler delay bound)
  (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
  (values : ∀ event who payload,
    ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "clearHistory" => phaseSourcePolicy_clear_history setup mode deadline leaks source
  bounds wellFormed assessment copies continuing plan
  (serviceGraph_revealRelaxedOrdered setup mode) maximal horizon scheduler capacity delay bound
  asyncService.opportunity asyncService.inclusion timely values

include copies continuing maximal capacity asyncService timely values

/-- The original setup draw stays coupled to the complete physical source
readout under the actual all-history asynchronous service contract. -/
theorem phaseSourcePolicy_async_joint_source_law :
    setup.initialLaw.bind (fun input =>
      ((P).runRounds scheduler players horizon
        (ReactiveApplication.Execution.initial (P)
          (PhaseRuntimeState.initial plan (setup.eventInputs input)))).map
            (fun next => (input, decodeState? (terminalRefs setup.program)
              next.application.current.native.config.store))) =
      setup.initialLaw.bind (fun input =>
        (SourceProgram.run setup.program structural input).map
          (fun final => (input, some final))) := by
  exact phaseSourcePolicy_physical_joint_source_law setup mode R leaks source bounds wellFormed
    assessment copies continuing plan maximal horizon scheduler capacity values clearHistory
      asyncService.completes

/-- Joint physical readout and payoff vectors retain their original private
setup parameter. No product assumption on that parameter is imposed. -/
theorem phaseSourcePolicy_async_joint_payoff_law
    (utility : State L setup.context → State L setup.program.terminalCtx → Player → ℝ) :
    setup.initialLaw.bind (fun input =>
      ((P).runRounds scheduler players horizon
        (ReactiveApplication.Execution.initial (P)
          (PhaseRuntimeState.initial plan (setup.eventInputs input)))).map (fun next =>
            let final := decodeState? (terminalRefs setup.program)
              next.application.current.native.config.store
            (input, final, fun who => final.elim 0 (fun state => utility input state who)))) =
      setup.initialLaw.bind (fun input =>
        (SourceProgram.run setup.program structural input).map
          (fun final => (input, some final, fun who => utility input final who))) := by
  exact phaseSourcePolicy_physical_joint_payoff_law setup mode R leaks source bounds wellFormed
    assessment copies continuing plan maximal horizon scheduler capacity values clearHistory
      asyncService.completes utility

/-- The actual canonical finite strategy terminates with exactly the original
complete typed source law, without a supplied physical safety premise. -/
theorem phaseSourceStrategy_async_terminal_source_law :
    (terminalLaw).map (fun final => phaseSourceReadout setup mode R leaks final.state) =
      (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map some := by
  exact phaseSourceStrategy_terminal_source_law setup mode R leaks source bounds wellFormed
    assessment copies continuing plan maximal horizon scheduler capacity values clearHistory
      asyncService.completes certificate

/-- Typed readout and the permanent-exclusion payoff vector have the original
source joint law under the original physical service contract. -/
theorem phaseSourceStrategy_async_terminal_source_payoff_law
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    (terminalLaw).map (fun final =>
      (phaseSourceReadout setup mode R leaks final.state,
        phaseExclusionBase setup mode R leaks utility excludedPayoff final.state)) =
      (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map
        (fun terminal => (some terminal, utility terminal)) := by
  exact phaseSourceStrategy_terminal_source_payoff_law setup mode R leaks source bounds wellFormed
    assessment copies continuing plan maximal horizon scheduler capacity values clearHistory
      asyncService.completes certificate utility excludedPayoff

/-- Every supported canonical terminal history is clear, and the actual
retained signed-evidence audit charges no player. -/
theorem phaseSourceStrategy_async_terminal_clear_uncharged
    (report : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup mode)))
    (final : ((menu).protocol initial horizon scheduler).History)
    (supported : final ∈ (terminalLaw).support) :
    ∃ current : (P).Control, final.state = some current ∧
      current.execution.application.current.excluded = ∅ ∧
      ∀ who, TerminalAudit.charge (P).stateTraffic
        (PhaseCount.audit R leaks report.sample) final.state who = 0 := by
  obtain ⟨current, atCurrent, clear⟩ := phaseSourceStrategy_terminal_clear setup mode R leaks bounds
    wellFormed assessment plan horizon scheduler clearHistory certificate final supported
  exact ⟨current, atCurrent, clear, fun who => PhaseCount.onePacketMenu_countCharge_zero R leaks
    bounds initial horizon scheduler report final who⟩

/-- The actual randomized count settlement preserves the joint source readout
and realized payoff vector. Zero charge is derived from authentic histories. -/
theorem phaseSourceStrategy_async_terminal_settlement_law
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff deposit : Player → ℝ)
    (report : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup mode))) :
    (terminalLaw).bind (fun final =>
      (TerminalAudit.settlement (phaseExclusionBase setup mode R leaks utility excludedPayoff)
        (P).stateTraffic (PhaseCount.audit R leaks report.sample) deposit final.state).map
          (fun payoffs => (phaseSourceReadout setup mode R leaks final.state, payoffs))) =
      (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map
        (fun terminal => (some terminal, utility terminal)) := by
  rw [← phaseSourceStrategy_async_terminal_source_payoff_law setup mode deadline leaks source
    bounds wellFormed assessment copies continuing plan maximal horizon scheduler capacity delay
      bound asyncService timely values utility excludedPayoff]
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support
  intro final supported
  have clean := (phaseSourceStrategy_async_terminal_clear_uncharged setup mode deadline leaks
    source bounds wellFormed assessment copies continuing plan maximal horizon scheduler capacity
      delay bound asyncService timely values report final supported).choose_spec.2.2
  rw [TerminalAudit.settlement_clean _ _ _ _ _ clean, PMF.pure_map]
  rfl

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCompiledSourceLaw
import Vegas.Game.PhaseExclusionPayoff
import Interaction.ReactiveTerminalEvaluation
import Interaction.ReactiveRoundTrace

/-! # The actual terminal behavioral law of the canonical compiled phase strategy -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
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
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (values : ∀ event who payload,
    ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "P" => phaseApplication runtime leaks
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan) inputs
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "players" => phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
local notation "strategy" => phaseSourceStrategy setup mode runtime leaks bounds wellFormed
  assessment initial horizon scheduler
local notation "structural" => setup.decodeBehavioralProfile
  (CommitmentInterface.values setup.program) (setup.openingExtension source)

include copies continuing maximal capacity values

/-- The terminal history law of the actual finite-menu strategy has the
original complete typed source readout, using the physical completion contract
and the same safety premise as its original scheduler-round law. -/
theorem phaseSourceStrategy_terminal_source_law
    (safe : ∀ (current : (P).Control)
      (_trace : ((menu).protocol initial horizon scheduler).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks initial horizon scheduler)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories) :
    (((menu).information initial horizon scheduler).runBehavioralTerminalFrom certificate strategy
      ((menu).protocol initial horizon scheduler).initHistory).map
        (fun final => phaseSourceReadout setup mode runtime leaks final.state) =
      (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map some := by
  have covered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment
  have evaluated := (menu).terminal_run_restrict_eq_rounds initial horizon scheduler certificate
    players ((menu).admissible_of_covered initial horizon scheduler players covered)
  have projected := congrArg (PMF.map (phaseSourceReadout setup mode runtime leaks)) evaluated
  simp only [PMF.map_comp, Function.comp_def] at projected
  change (((menu).information initial horizon scheduler).runBehavioralTerminalFrom certificate
    strategy ((menu).protocol initial horizon scheduler).initHistory).map
      (fun final => phaseSourceReadout setup mode runtime leaks final.state) = _ at projected
  rw [projected]
  have completed (next : (P).Execution)
      (supported : next ∈ ((P).roundsFrom initial scheduler players horizon).support) :
      next.application.current.native.config.cut.Terminal := by
    obtain ⟨trace⟩ := (menu).trace_roundsFrom initial horizon scheduler players covered horizon
      le_rfl next supported
    have finalTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨0, none, next⟩) := by
      simpa only [Nat.sub_self] using trace
    exact completes ⟨0, none, next⟩
      ((menu).toRawTrace initial horizon scheduler finalTrace) ⟨rfl, rfl⟩
  have decodeLaw := congrArg (PMF.map Prod.snd)
    (phaseSourcePolicy_physical_joint_source_law setup mode runtime leaks source bounds wellFormed
      assessment copies continuing plan maximal horizon scheduler capacity values safe completes)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at decodeLaw
  calc
    _ = ((P).roundsFrom initial scheduler players horizon).map
        (fun next => decodeState? (terminalRefs setup.program)
          next.application.current.native.config.store) := by
      have initialEq : PMF.map (fun value => PhaseRuntimeState.initial plan (encodeInputs value))
          setup.initialLaw = initial := by
        rw [PMF.map_comp]
        rfl
      rw [initialEq]
      apply map_congr_on_support
      intro next supported
      change phaseSourceReadout setup mode runtime leaks (some ⟨0, none, next⟩) = _
      simp only [phaseSourceReadout, Option.bind_some, completed next supported, ↓reduceIte]
    _ = _ := by
      simpa only [ReactiveApplication.roundsFrom, PMF.bind_map, PMF.map_bind,
        Function.comp_def, Setup.eventInputs] using decodeLaw

omit copies continuing maximal capacity values in
/-- Every actual supported terminal history of the represented canonical
strategy is clear whenever its original physical policy is safe. -/
theorem phaseSourceStrategy_terminal_clear
    (safe : ∀ (current : (P).Control)
      (_trace : ((menu).protocol initial horizon scheduler).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (final : ((menu).protocol initial horizon scheduler).History)
    (supported : final ∈ (((menu).information initial horizon scheduler).runBehavioralTerminalFrom
      certificate strategy ((menu).protocol initial horizon scheduler).initHistory).support) :
    ∃ current : (P).Control, final.state = some current ∧
      current.execution.application.current.excluded = ∅ := by
  have covered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment
  have evaluated := (menu).terminal_run_restrict_eq_rounds initial horizon scheduler certificate
    players ((menu).admissible_of_covered initial horizon scheduler players covered)
  have stateSupported : final.state ∈
      (((P).roundsFrom initial scheduler players horizon).map (P).finished).support := by
    rw [← evaluated]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  obtain ⟨next, nextSupported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp stateSupported
  obtain ⟨trace⟩ := (menu).trace_roundsFrom initial horizon scheduler players covered horizon
    le_rfl next nextSupported
  have finalTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨0, none, next⟩) := by
    simpa only [Nat.sub_self] using trace
  obtain ⟨entry, _positive, reached⟩ := Set.mem_iUnion₂.mp
    (PMF.support_bind .. ▸ nextSupported)
  have faithful := ((P).consistentRecall_policyInvariant players).runRounds scheduler horizon
    (ReactiveApplication.Execution.initial (P) entry) next (fun _ => .nil) reached
  exact ⟨⟨0, none, next⟩, same.symm, safe ⟨0, none, next⟩ finalTrace faithful⟩

/-- The actual terminal strategy preserves typed source readout jointly with
its full permanent-exclusion payoff vector. Physical safety is the remaining
operational premise; no payoff-law hypothesis is supplied. -/
theorem phaseSourceStrategy_terminal_source_payoff_law
    (safe : ∀ (current : (P).Control)
      (_trace : ((menu).protocol initial horizon scheduler).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks initial horizon scheduler)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    (((menu).information initial horizon scheduler).runBehavioralTerminalFrom certificate strategy
      ((menu).protocol initial horizon scheduler).initHistory).map
        (fun final => (phaseSourceReadout setup mode runtime leaks final.state,
          phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state)) =
      (setup.initialLaw.bind (SourceProgram.run setup.program structural)).map
        (fun terminal => (some terminal, utility terminal)) := by
  have readout := phaseSourceStrategy_terminal_source_law setup mode runtime leaks source bounds
    wellFormed assessment copies continuing plan maximal horizon scheduler capacity values safe
      completes certificate
  have projected := congrArg (PMF.map (fun result => (result,
    fun who => result.elim 0 (fun terminal => utility terminal who)))) readout
  simp only [PMF.map_comp, Function.comp_def, Option.elim_some] at projected
  rw [← projected]
  apply map_congr_on_support
  intro final supported
  obtain ⟨current, atCurrent, clear⟩ := phaseSourceStrategy_terminal_clear setup mode runtime leaks
    bounds wellFormed assessment plan horizon scheduler safe certificate final supported
  apply congrArg (fun payoffs => (phaseSourceReadout setup mode runtime leaks final.state, payoffs))
  funext who
  rw [atCurrent]
  exact phaseExclusionBase_eq_readout setup mode runtime leaks utility excludedPayoff current who
    (by simp only [clear, Finset.notMem_empty, not_false_eq_true])

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCallbackContinuation
import Interaction.ReactiveStopping
import Interaction.ReactiveRawRoundTrace

/-! # Actual callback continuations through physical attempt boundaries -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "P" => phaseApplication runtime leaks
local notation "M" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

omit [Fintype Player] in
/-- The original physical attempt has ended or the focal player has been
permanently excluded. Full physical history and saved state remain in the
stopped execution. -/
def PhaseAttemptClosed (who : Player) (attempt : CommitAttemptId) (execution : (P).Execution) :
    Prop :=
  who ∈ execution.application.current.excluded ∨ execution.application.attempt ≠ attempt

open Classical in
/-- A unilateral actual callback lottery is followed by the original profile
through its first physical attempt boundary and then through the entire
remaining run. Both original readout and the full base-payoff vector are
preserved; a silent response retains every later opportunity to send. -/
theorem phase_callback_attempt_terminal_outcome
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who)
    (history : (E).History) (who : Player) (remaining : Nat) (execution : (P).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (law : PMF ((M).Choice who ((M).infoOf who history.trace)))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    ((M).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (M).behavioralSignature) profile who
        ((profile who).withLaw ((M).infoOf who history.trace) law)) history).map
        (fun final => (phaseSourceReadout setup mode runtime leaks final.state,
          phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state)) =
      law.bind fun choice =>
        ((P).runUntilHorizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile)
          (PhaseAttemptClosed setup mode runtime leaks who execution.application.attempt) horizon
          (execution.respond (P) who (choice.1.getD ⟨none⟩))).bind fun boundary =>
            ((P).runToHorizon scheduler
              ((menu).decodeProfile initial horizon scheduler profile) horizon boundary).map
                (fun final => (phaseSourceReadout setup mode runtime leaks ((P).finished final),
                  phaseExclusionBase setup mode runtime leaks utility excludedPayoff
                    ((P).finished final))) := by
  classical
  rw [phase_callback_terminal_outcome setup mode runtime leaks menu initial horizon scheduler
    certificate profile history who remaining execution current law utility excludedPayoff,
      PMF.bind_map]
  apply bind_congr_on_support
  intro choice _supported
  dsimp only [Function.comp_def]
  have accounted := (P).raw_trace_horizon initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler (current ▸ history.trace))
  change execution.environmentRecall.length + remaining = horizon at accounted
  rw [(P).finish_eq_runToHorizon scheduler
    ((menu).decodeProfile initial horizon scheduler profile) initial horizon remaining _
      (by rw [(P).respond_environmentRecall]; exact accounted), PMF.map_comp]
  rw [(P).runToHorizon_eq_runUntilHorizon_bind scheduler
    ((menu).decodeProfile initial horizon scheduler profile)
    (PhaseAttemptClosed setup mode runtime leaks who execution.application.attempt)]
  rw [PMF.map_bind]
  rfl

open Classical in
/-- The actual callback value uses the original physical terminal potential
at each stopped execution. In particular the surviving-reset potential is
not replaced by the exclusion payoff or an assumed source value. -/
theorem phase_callback_attempt_base_value
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who)
    (history : (E).History) (who : Player) (remaining : Nat) (execution : (P).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (law : PMF ((M).Choice who ((M).infoOf who history.trace)))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal, |utility terminal who| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) :
    expect ((M).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (M).behavioralSignature) profile who
        ((profile who).withLaw ((M).infoOf who history.trace) law)) history)
      (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
        final.state who) =
      expect law (fun choice => expect
        ((P).runUntilHorizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile)
          (PhaseAttemptClosed setup mode runtime leaks who execution.application.attempt) horizon
          (execution.respond (P) who (choice.1.getD ⟨none⟩)))
        (fun boundary => expect ((P).runToHorizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile) horizon boundary)
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            ((P).finished final) who))) := by
  classical
  rw [phase_callback_base_value setup mode runtime leaks menu initial horizon scheduler
    certificate profile history who remaining execution current law utility excludedPayoff B
      nonnegative utilityBound excludedBound]
  apply expect_congr_on_support
  intro choice _supported
  have accounted := (P).raw_trace_horizon initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler (current ▸ history.trace))
  change execution.environmentRecall.length + remaining = horizon at accounted
  rw [(P).finish_eq_runToHorizon scheduler
    ((menu).decodeProfile initial horizon scheduler profile) initial horizon remaining _
      (by rw [(P).respond_environmentRecall]; exact accounted), expect_map]
  rw [(P).runToHorizon_eq_runUntilHorizon_bind scheduler
    ((menu).decodeProfile initial horizon scheduler profile)
    (PhaseAttemptClosed setup mode runtime leaks who execution.application.attempt)]
  apply expect_bind_tower_bounded (C := B)
  intro final
  dsimp only [Function.comp_def]
  cases state : (P).finished final with
  | none => simpa only [state, phaseExclusionBase, abs_zero] using nonnegative
  | some control =>
      change |if who ∈ control.execution.application.current.excluded then excludedPayoff who
        else (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
          (fun terminal => utility terminal who)| ≤ B
      split_ifs
      · exact excludedBound
      · cases readout : phaseSourceReadout setup mode runtime leaks (some control) with
        | none => simpa using nonnegative
        | some terminal => exact utilityBound terminal

end Vegas

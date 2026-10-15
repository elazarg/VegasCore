/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseExclusionPayoff
import Interaction.ReactiveLocalContinuation

/-! # Actual phase callback deviations with the entire later continuation -/

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

open Classical in
/-- A local lottery at an actual callback is followed by the original full
physical continuation. In particular a silent response retains all later
callbacks, packets, resets, source readouts and exclusion payoffs. -/
theorem phase_callback_terminal_outcome
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
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        ((P).finish initial horizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile)
            (some ⟨remaining, none, execution.respond (P) who response⟩)).map
          (fun final => (phaseSourceReadout setup mode runtime leaks final,
            phaseExclusionBase setup mode runtime leaks utility excludedPayoff final)) := by
  classical
  have bounded := (P).trace_bound initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler history.trace)
  rw [(menu).toRawTrace_length] at bounded
  have enough : (P).rank horizon history.state ≤ 2 * horizon + 1 := by omega
  have responseLaw := (menu).run_local_law_finish initial horizon scheduler profile
    history who remaining execution current law (2 * horizon) enough
  rw [(M).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    ((menu).bounded initial horizon scheduler)]
  calc
    _ = (((M).runBehavioralFrom _ (2 * horizon + 1) history).map History.state).map
        (fun final => (phaseSourceReadout setup mode runtime leaks final,
          phaseExclusionBase setup mode runtime leaks utility excludedPayoff final)) :=
      (PMF.map_comp History.state _ _).symm
    _ = _ := by rw [responseLaw, PMF.map_bind]

open Classical in
/-- The actual focal payoff after a local response lottery integrates the
original whole continuation, including every later chance to send. -/
theorem phase_callback_base_value
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
        ((P).finish initial horizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile)
            (some ⟨remaining, none,
              execution.respond (P) who (choice.1.getD ⟨none⟩)⟩))
        (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          final who)) := by
  classical
  let payoff := fun final =>
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff final who
  have boundedPayoff : ∀ final, |payoff final| ≤ B := by
    intro final
    cases final with
    | none => simpa [payoff, phaseExclusionBase] using nonnegative
    | some control =>
        change |if who ∈ control.execution.application.current.excluded then excludedPayoff who
          else (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
            (fun terminal => utility terminal who)| ≤ B
        split_ifs
        · exact excludedBound
        · cases readout : phaseSourceReadout setup mode runtime leaks (some control) with
          | none => simpa using nonnegative
          | some terminal => exact utilityBound terminal
  have bounded := (P).trace_bound initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler history.trace)
  rw [(menu).toRawTrace_length] at bounded
  have enough : (P).rank horizon history.state ≤ 2 * horizon + 1 := by omega
  have responseLaw := (menu).run_local_law_finish initial horizon scheduler profile
    history who remaining execution current law (2 * horizon) enough
  rw [(M).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    ((menu).bounded initial horizon scheduler)]
  change expect ((M).runBehavioralFrom _ (2 * horizon + 1) history)
    (fun final => payoff final.state) = _
  calc
    _ = expect (((M).runBehavioralFrom _ (2 * horizon + 1) history).map
        (fun final : (E).History => final.state)) payoff :=
      (expect_map (fun final : (E).History => final.state) _ payoff).symm
    _ = _ := by
      rw [responseLaw, expect_bind_tower_bounded _ _ payoff boundedPayoff, expect_map]
      rfl

end Vegas

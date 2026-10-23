/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealServicePayoffs
import Vegas.Pending.PhaseFrontier
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Typed terminal readouts and permanent-exclusion payoffs of phase recovery -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "app" => phaseApplication runtime leaks

/-- Decode the current completed source store. Voided attempt archives remain
physical records and are never substituted for the surviving semantic store. -/
def phaseSourceReadout (state : (app).ProtocolState) :
    Option (State L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.current.native.config
    if config.cut.Terminal then decodeState? (terminalRefs setup.program) config.store else none

/-- The actual excluded set, rather than latent failed commitments, determines
the floor. Unexcluded owners receive their terminal source-store utility. -/
def phaseExclusionBase (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (state : (app).ProtocolState) (who : Player) : ℝ :=
  match state with
  | none => 0
  | some control =>
      if who ∈ control.execution.application.current.excluded then excludedPayoff who else
        (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
          (fun terminal => utility terminal who)

theorem phaseExclusionBase_of_excluded
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (control : (app).Control) (who : Player)
    (excluded : who ∈ control.execution.application.current.excluded) :
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff (some control) who =
      excludedPayoff who := by
  simp only [phaseExclusionBase, ite_eq_left excluded]

theorem phaseExclusionBase_mem_Icc
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff lower upper : Player → ℝ)
    (lower_le : ∀ terminal who, lower who ≤ utility terminal who)
    (le_upper : ∀ terminal who, utility terminal who ≤ upper who)
    (state : (app).ProtocolState) (who : Player) :
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who ∈
      Set.Icc (min 0 (min (excludedPayoff who) (lower who)))
        (max 0 (max (excludedPayoff who) (upper who))) := by
  cases state with
  | none => exact ⟨min_le_left _ _, le_max_left _ _⟩
  | some control =>
      change (if who ∈ control.execution.application.current.excluded then excludedPayoff who
        else (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
          (fun terminal => utility terminal who)) ∈ _
      split_ifs with excluded
      · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
          (le_max_left (excludedPayoff who) (upper who)).trans (le_max_right _ _)⟩
      · cases readout : phaseSourceReadout setup mode runtime leaks (some control) with
        | none => exact ⟨min_le_left _ _, le_max_left _ _⟩
        | some terminal =>
            exact ⟨(min_le_right _ _).trans ((min_le_right _ _).trans (lower_le terminal who)),
              (le_upper terminal who).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- Actual permanent focal exclusion in the current phase state. -/
def PhaseExcluded (who : Player) : (app).ProtocolState → Prop
  | none => False
  | some control => who ∈ control.execution.application.current.excluded

theorem phaseExcluded_transition (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).ProtocolState)
    (joint : Player → Option (app).Action) {who : Player}
    (excluded : PhaseExcluded setup mode runtime leaks who before)
    (reached : after ∈ ((app).transition initial horizon scheduler before joint).support) :
    PhaseExcluded setup mode runtime leaks who after := by
  cases before with
  | none => exact excluded.elim
  | some control =>
      have stays : ∃ next, after = some next := by
        rcases control with ⟨remaining, actor, execution⟩
        cases actor with
        | some who => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
        | none =>
            cases remaining with
            | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
            | succ remaining =>
                obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                obtain ⟨next, _, same⟩ := PMF.support_map .. ▸ moved
                exact ⟨_, same.symm⟩
      obtain ⟨next, rfl⟩ := stays
      exact (phaseApplication_exclusion_monotone runtime leaks).transition initial horizon
        scheduler control next joint reached excluded

section Continuation

variable [Fintype Player]

/-- Actual permanent exclusion fixes every supported terminal payoff under
arbitrary menus, future policies, schedulers, phase advances and retries. -/
theorem phase_excluded_terminal_payoff
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (menu : (app).ResponseMenu) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol initial horizon scheduler).History)
    (excluded : PhaseExcluded setup mode runtime leaks who history.state)
    (final : (menu.protocol initial horizon scheduler).History)
    (supported : final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom
      certificate players history).support) :
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who =
      excludedPayoff who := by
  have retained :=
    (menu.information initial horizon scheduler).runBehavioralTerminalFrom_support_closed
    certificate players (PhaseExcluded setup mode runtime leaks who)
    (fun before joint _ after valid reached =>
      phaseExcluded_transition setup mode runtime leaks initial horizon scheduler
        before after joint valid reached) history excluded final supported
  cases current : final.state with
  | none => rw [current] at retained; exact retained.elim
  | some control =>
      rw [current] at retained
      exact phaseExclusionBase_of_excluded setup mode runtime leaks utility excludedPayoff
        control who retained

theorem phase_excluded_expected_payoff
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (menu : (app).ResponseMenu) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol initial horizon scheduler).History)
    (excluded : PhaseExcluded setup mode runtime leaks who history.state) :
    expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      players history) (fun final =>
        phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who) =
      excludedPayoff who := by
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)
    (phase_excluded_terminal_payoff setup mode runtime leaks utility excludedPayoff menu initial
      horizon scheduler certificate players who history excluded)]
  exact expect_constant _ _

end Continuation
end Vegas

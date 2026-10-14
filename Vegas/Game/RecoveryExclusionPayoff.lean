/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Pending.ExclusionProjection
import Vegas.Pending.ExclusionInvariant

/-! # Fixed utility after permanent runtime exclusion

The recovery utility reads the permanent excluded set before reading a terminal
source outcome. Its excluded branch therefore applies even at a finite horizon
with no terminal source readout. This is a utility statement, not an identification
of automatic graph histories with source histories that omit automatic choices.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Permanent exclusion fixes the utility before the terminal-source readout
branch is evaluated. Before exclusion the ordinary source exclusion utility applies. -/
def recoveryExclusionBase {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (state : (recoveryApplication (runtime setup) leaks).ProtocolState) (who : Player) : ℝ :=
  match state with
  | none => 0
  | some control =>
      if who ∈ control.execution.application.excluded then excludedPayoff who
      else exclusionBase setup parameter utility excludedPayoff leaks
        (some (RecoveryProjection.control (runtime setup) leaks control)) who

/-- The excluded branch applies irrespective of remaining service time. -/
theorem recoveryExclusionBase_of_excluded {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (control : (recoveryApplication (runtime setup) leaks).Control) (who : Player)
    (excluded : who ∈ control.execution.application.excluded) :
    recoveryExclusionBase parameter utility excludedPayoff (some control) who =
      excludedPayoff who :=
  by simp only [recoveryExclusionBase, excluded, ↓reduceIte]

/-- Before exclusion the recovery utility is the native source-readout utility. -/
theorem recoveryExclusionBase_of_not_excluded {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (control : (recoveryApplication (runtime setup) leaks).Control) (who : Player)
    (excluded : who ∉ control.execution.application.excluded) :
    recoveryExclusionBase parameter utility excludedPayoff (some control) who =
      exclusionBase setup parameter utility excludedPayoff leaks
        (some (RecoveryProjection.control (runtime setup) leaks control)) who := by
  simp only [recoveryExclusionBase, excluded, ↓reduceIte]

/-- An initialized protocol state whose owner has permanently been excluded. -/
def RecoveryExcluded (who : Player) :
    (recoveryApplication (runtime setup) leaks).ProtocolState → Prop
  | none => False
  | some control => who ∈ control.execution.application.excluded

/-- Every actual recovery transition keeps all permanent exclusions. -/
theorem recoveryExcluded_transition
    (initial : PMF (RecoveryState (graph setup))) (horizon : Nat)
    (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (before after : (recoveryApplication (runtime setup) leaks).ProtocolState)
    (joint : Player → Option (recoveryApplication (runtime setup) leaks).Action)
    {who : Player} (excluded : RecoveryExcluded (setup := setup) (leaks := leaks) who before)
    (reached : after ∈ ((recoveryApplication (runtime setup) leaks).transition initial horizon
      scheduler before joint).support) :
    RecoveryExcluded (setup := setup) (leaks := leaks) who after := by
  cases before with
  | none => exact excluded.elim
  | some control =>
      have stays : ∃ next, after = some next := by
        rcases control with ⟨remaining, current, execution⟩
        cases current with
        | some who => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
        | none =>
            cases remaining with
            | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
            | succ remaining =>
                obtain ⟨command, _, moved⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                obtain ⟨next, _, same⟩ := PMF.support_map .. ▸ moved
                exact ⟨_, same.symm⟩
      obtain ⟨next, rfl⟩ := stays
      exact (recoveryApplication_exclusion_monotone (runtime setup) leaks).transition initial
        horizon scheduler control next joint reached excluded

section Continuation

variable [Fintype Player]

/-- Every supported terminal continuation pays a permanently excluded owner
its fixed exclusion utility, under arbitrary later player policies. -/
theorem recovery_excluded_exclusionBase {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (recoveryApplication (runtime setup) leaks).ResponseMenu)
    (initial : PMF (RecoveryState (graph setup))) (horizon : Nat)
    (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol initial horizon scheduler).History)
    (excluded : RecoveryExcluded (setup := setup) (leaks := leaks) who history.state) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      players history).support,
      recoveryExclusionBase parameter utility excludedPayoff final.state who = excludedPayoff who :=
    by
  intro final supported
  have remains := (menu.information initial horizon
    scheduler).runBehavioralTerminalFrom_support_closed
    certificate players (RecoveryExcluded (setup := setup) (leaks := leaks) who)
    (fun before joint _ after valid reached =>
      recoveryExcluded_transition initial horizon scheduler before after joint valid reached)
    history excluded final supported
  cases state : final.state with
  | none => rw [state] at remains; exact remains.elim
  | some control =>
      rw [state] at remains
      exact recoveryExclusionBase_of_excluded parameter utility excludedPayoff control who remains

/-- The whole continuation law has the same fixed excluded utility. -/
theorem recovery_excluded_expect_exclusionBase {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (recoveryApplication (runtime setup) leaks).ResponseMenu)
    (initial : PMF (RecoveryState (graph setup))) (horizon : Nat)
    (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol initial horizon scheduler).History)
    (excluded : RecoveryExcluded (setup := setup) (leaks := leaks) who history.state) :
    expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
      players history) (fun final => recoveryExclusionBase parameter utility excludedPayoff
        final.state who) = excludedPayoff who := by
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)
    (recovery_excluded_exclusionBase parameter utility excludedPayoff menu initial horizon scheduler
      certificate players who history excluded)]
  exact expect_constant _ _

end Continuation
end Vegas

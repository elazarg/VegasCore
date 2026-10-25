/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryDebtStoppedBound
import Vegas.Game.RecoveryDebtStoppedReadout

/-! # Native payoff comparison stopped before latent own debt

The comparison uses actual finite recovery policies and the induced native law.
Latent own debt is a clear stopping condition; recovery completion supplies its
fixed continuation payoff. Only foreign exit labels contribute error.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime EventGraphRuntime.RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

open Classical in
/-- Recovery payoff is close to the native law stopped at public exclusion or
latent own debt. Only its foreign first-failure labels contribute to the error. -/
theorem recovery_expect_sub_native_debt_stopped_le_foreign_exit {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (source : BehavioralProfile setup.program)
    (initial : PMF (RecoveryState (graph setup)))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨EventGraphRuntime.State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (horizon : Nat) (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon scheduler)
    (menu : (recoveryApplication (runtime setup) leaks).ResponseMenu)
    (nativeCertificate : ((application setup leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler (runtime setup) leaks scheduler)).WellFoundedHistories)
    (recoveryCertificate : ((recoveryApplication (runtime setup) leaks).protocol initial horizon
      scheduler).WellFoundedHistories)
    (menuCertificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (payoffBounded : ∀ history : (menu.protocol initial horizon scheduler).History,
      |recoveryExclusionBase parameter utility excludedPayoff history.state who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound)
    (history : (menu.protocol initial horizon scheduler).History)
    (current : (recoveryApplication (runtime setup) leaks).Control)
    (state : history.state = some current) (empty : current.execution.application.excluded = ∅) :
    let raw := menu.toRawHistory initial horizon scheduler history
    let clear := fun next (same : raw.state = some next) =>
      (Option.some.inj (state.symm.trans same)) ▸ empty
    let native := (application setup leaks).information (initial.map RecoveryState.native) horizon
      (nativeScheduler (runtime setup) leaks scheduler)
    let nativeStopped := (native.runBehavioralUntil nativeCertificate
      (nativeProfile (runtime setup) leaks initial horizon scheduler
        (fun who => menu.embedPolicy initial horizon scheduler who (profile who)))
      (fun history => ¬ NativeClear (runtime setup) leaks initial horizon scheduler history ∨
        DecodedState setup leaks source (ProtocolState.OwesFailure who setup.program) history.state)
      (nativeHistory (runtime setup) leaks initial horizon scheduler raw clear)).map
        (nativeClassifiedReadout (runtime setup) leaks initial horizon scheduler)
    |expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom menuCertificate
        profile history) (fun final =>
          recoveryExclusionBase parameter utility excludedPayoff final.state who) -
      expect nativeStopped (Sum.elim (fun _ => excludedPayoff who)
        (fun final => if DecodedState setup leaks source
            (ProtocolState.OwesFailure who setup.program) final.state then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who))| ≤
      (2 * bound) * (nativeStopped.toOuterMeasure
        {label | ForeignExclusionLabel who label}).toReal :=
    by
  intro raw clear native nativeStopped
  have estimate := recovery_expect_sub_debt_stopped_le_foreign_exit parameter utility excludedPayoff
    source menu initial horizon scheduler completes menuCertificate profile who nonnegative
    payoffBounded excludedBounded history
  have readout := recovery_debt_stopped_expect_eq_native parameter utility excludedPayoff source
    initial initialized horizon scheduler menu nativeCertificate recoveryCertificate menuCertificate
    profile who history current state empty
  have mass := recovery_debt_foreign_exit_mass_le_native source initial initialized horizon
    scheduler menu nativeCertificate recoveryCertificate menuCertificate profile who history current
    state empty
  dsimp only at estimate
  rw [readout] at estimate
  exact estimate.trans (mul_le_mul_of_nonneg_left mass (by positivity))

end Vegas

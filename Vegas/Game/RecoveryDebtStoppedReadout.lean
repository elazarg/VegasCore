/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryForeignExitComparison
import Vegas.Game.RecoveryDecodedDebt
import Vegas.Pending.ExclusionMenuStopped
import Vegas.Game.AsyncDeviationForeign

/-! # Exact recovery and native debt-stopped utility readouts

The state readout identity requires no recovery completion or service contract.
Only the actual pre-exclusion projection and the existing exclusion/debt floor
are used; arbitrary policies and first-exclusion endpoints are retained.
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
/-- Exact equality of actual stopped utility readouts before first physical
exclusion or focal source debt, with no completion contract. -/
theorem recovery_debt_stopped_expect_eq_native {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (source : BehavioralProfile setup.program)
    (initial : PMF (RecoveryState (graph setup)))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨EventGraphRuntime.State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (horizon : Nat) (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (menu : (recoveryApplication (runtime setup) leaks).ResponseMenu)
    (nativeCertificate : ((application setup leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler (runtime setup) leaks scheduler)).WellFoundedHistories)
    (recoveryCertificate : ((recoveryApplication (runtime setup) leaks).protocol initial horizon
      scheduler).WellFoundedHistories)
    (menuCertificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player)
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
    expect ((menu.information initial horizon scheduler).runBehavioralUntil menuCertificate
      profile (fun final => RecoveryPublicExclusion (setup := setup) (leaks := leaks) final.state ∨
          RecoveryDecodedState (leaks := leaks) source
            (ProtocolState.OwesFailure who setup.program) final.state) history)
      (fun final => if RecoveryPublicExclusion (setup := setup) (leaks := leaks) final.state ∨
          RecoveryDecodedState (leaks := leaks) source
            (ProtocolState.OwesFailure who setup.program) final.state then
        excludedPayoff who else recoveryExclusionBase parameter utility excludedPayoff
          final.state who) =
      expect nativeStopped (Sum.elim (fun _ => excludedPayoff who)
        (fun final => if DecodedState setup leaks source
            (ProtocolState.OwesFailure who setup.program) final.state then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who)) := by
  classical
  intro raw clear native nativeStopped
  let stop := fun next : (menu.protocol initial horizon scheduler).History =>
    RecoveryPublicExclusion (setup := setup) (leaks := leaks) next.state ∨
      RecoveryDecodedState (leaks := leaks) source
        (ProtocolState.OwesFailure who setup.program) next.state
  let stopped := (menu.information initial horizon scheduler).runBehavioralUntil menuCertificate
    profile stop history
  let classify := fun next : (menu.protocol initial horizon scheduler).History =>
    recoveryClassifiedReadout (runtime setup) leaks initial horizon scheduler
      (menu.toRawHistory initial horizon scheduler next)
  let read := Sum.elim (fun _ : Finset Player => excludedPayoff who)
    (fun final : ((application setup leaks).protocol (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler)).History =>
      if DecodedState setup leaks source (ProtocolState.OwesFailure who setup.program)
          final.state then excludedPayoff who else
        exclusionBase setup parameter utility excludedPayoff leaks final.state who)
  let nativeDebt := fun next : ((application setup leaks).protocol
      (initial.map RecoveryState.native) horizon
      (nativeScheduler (runtime setup) leaks scheduler)).History =>
    DecodedState setup leaks source (ProtocolState.OwesFailure who setup.program) next.state
  let recoveryDebt := fun next : ((recoveryApplication (runtime setup) leaks).protocol
      initial horizon scheduler).History =>
    RecoveryDecodedState (leaks := leaks) source
      (ProtocolState.OwesFailure who setup.program) next.state
  have decodedEq (endpoint : (recoveryApplication (runtime setup) leaks).ProtocolState) :
      DecodedState setup leaks source (ProtocolState.OwesFailure who setup.program)
        (protocolState (runtime setup) leaks endpoint) ↔
      RecoveryDecodedState (leaks := leaks) source
        (ProtocolState.OwesFailure who setup.program) endpoint := by
    cases endpoint <;> rfl
  have debtEq (next : (menu.protocol initial horizon scheduler).History)
      (clearNext : RecoveryClear (runtime setup) leaks initial horizon scheduler
        (menu.toRawHistory initial horizon scheduler next)) :
      nativeDebt (nativeHistory (runtime setup) leaks initial horizon scheduler
        (menu.toRawHistory initial horizon scheduler next) clearNext) ↔
          RecoveryDecodedState (leaks := leaks) source
            (ProtocolState.OwesFailure who setup.program) next.state := by
    exact decodedEq next.state
  have publicEq (next : (menu.protocol initial horizon scheduler).History) :
      RecoveryPublicExclusion (setup := setup) (leaks := leaks) next.state ↔
        ¬ RecoveryClear (runtime setup) leaks initial horizon scheduler
          (menu.toRawHistory initial horizon scheduler next) := by
    cases same : next.state with
    | none => simp [RecoveryPublicExclusion, RecoveryClear,
        ReactiveApplication.ResponseMenu.toRawHistory, same]
    | some control =>
      simp only [RecoveryPublicExclusion, RecoveryClear,
        ReactiveApplication.ResponseMenu.toRawHistory, same]
      constructor
      · intro nonempty allClear
        exact nonempty (allClear control rfl)
      · intro notAll empty
        apply notAll
        intro found equal
        cases Option.some.inj equal
        exact empty
  have stopEq : stop = fun next =>
      ¬ RecoveryClear (runtime setup) leaks initial horizon scheduler
          (menu.toRawHistory initial horizon scheduler next) ∨
        recoveryDebt (menu.toRawHistory initial horizon scheduler next) := by
    funext next
    exact propext (or_congr (publicEq next) Iff.rfl)
  have law : nativeStopped = stopped.map classify := by
    dsimp only [nativeStopped, stopped]
    rw [stopEq]
    exact responseMenu_exclusion_or_classified_eq (runtime setup) leaks initial horizon scheduler
      initialized menu profile nativeCertificate recoveryCertificate menuCertificate
      nativeDebt recoveryDebt (fun next _clear => decodedEq next.state)
      history clear
  have valueEq (next : (menu.protocol initial horizon scheduler).History) :
      read (classify next) = if stop next then excludedPayoff who else
        recoveryExclusionBase parameter utility excludedPayoff next.state who := by
    by_cases clearNext : RecoveryClear (runtime setup) leaks initial horizon scheduler
        (menu.toRawHistory initial horizon scheduler next)
    · unfold classify recoveryClassifiedReadout
      rw [dite_eq_left clearNext]
      by_cases owed : RecoveryDecodedState (leaks := leaks) source
          (ProtocolState.OwesFailure who setup.program) next.state
      · have nativeOwed := (debtEq next clearNext).mpr owed
        change (if nativeDebt _ then _ else _) = _
        rw [ite_eq_left nativeOwed, ite_eq_left (Or.inr owed)]
      · have nativeNotOwed := fun found => owed ((debtEq next clearNext).mp found)
        have notStopped : ¬ stop next := by
          rintro (publicExit | debt)
          · exact (publicEq next).mp publicExit clearNext
          · exact owed debt
        change (if nativeDebt _ then _ else _) = _
        rw [ite_eq_right nativeNotOwed, ite_eq_right notStopped]
        change exclusionBase setup parameter utility excludedPayoff leaks
          (protocolState (runtime setup) leaks next.state) who =
            recoveryExclusionBase parameter utility excludedPayoff next.state who
        cases same : next.state with
        | none => rfl
        | some control =>
          have noExclusion : control.execution.application.excluded = ∅ := clearNext control same
          exact (recoveryExclusionBase_of_not_excluded parameter utility excludedPayoff control who
            (by simp [noExclusion])).symm
    · have exited : stop next := Or.inl ((publicEq next).mpr clearNext)
      unfold classify recoveryClassifiedReadout
      rw [dite_eq_right clearNext, ite_eq_left exited]
      rfl
  rw [law, expect_map]
  exact (congrArg (expect stopped) (funext valueEq)).symm

end Vegas

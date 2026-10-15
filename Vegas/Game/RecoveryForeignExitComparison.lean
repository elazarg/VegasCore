/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryForeignExitBound
import Vegas.Pending.ExclusionMenuStopped

/-! # Native stopped payoff comparison with only foreign first-exclusion error

The comparison uses actual finite recovery policies and the induced native law.
Neither a global native service contract nor agreement after exclusion is needed.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime EventGraphRuntime.RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A classified first exit excluding other owners while this owner survives. -/
def ForeignExclusionLabel {History : Type} (who : Player) : Finset Player ⊕ History → Prop
  | .inl excluded => who ∉ excluded
  | .inr _ => False

open Classical in
/-- Recovery payoff is close to the actual native stopped comparison. Only
native first-failure labels not containing the owner contribute to the error. -/
theorem recovery_expect_sub_native_stopped_le_foreign_exit {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
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
    (who : Player) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (payoffBounded : ∀ state : (recoveryApplication (runtime setup) leaks).ProtocolState,
      |recoveryExclusionBase parameter utility excludedPayoff state who| ≤ bound)
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
      (fun history => ¬ NativeClear (runtime setup) leaks initial horizon scheduler history)
      (nativeHistory (runtime setup) leaks initial horizon scheduler raw clear)).map
        (nativeClassifiedReadout (runtime setup) leaks initial horizon scheduler)
    |expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom menuCertificate
        profile history) (fun final =>
          recoveryExclusionBase parameter utility excludedPayoff final.state who) -
      expect nativeStopped (Sum.elim (fun _ => excludedPayoff who)
        (fun final => exclusionBase setup parameter utility excludedPayoff leaks
          final.state who))| ≤
      (2 * bound) * (nativeStopped.toOuterMeasure
        {label | ForeignExclusionLabel who label}).toReal :=
    by
  classical
  intro raw clear native nativeStopped
  let stop := fun next : (menu.protocol initial horizon scheduler).History =>
    RecoveryPublicExclusion (setup := setup) (leaks := leaks) next.state
  let stopped := (menu.information initial horizon scheduler).runBehavioralUntil menuCertificate
    profile stop history
  let classify := fun next : (menu.protocol initial horizon scheduler).History =>
    recoveryClassifiedReadout (runtime setup) leaks initial horizon scheduler
      (menu.toRawHistory initial horizon scheduler next)
  let read := Sum.elim (fun _ : Finset Player => excludedPayoff who)
    (fun final : ((application setup leaks).protocol (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler)).History =>
      exclusionBase setup parameter utility excludedPayoff leaks final.state who)
  have stopEq : stop = fun next => ¬ RecoveryClear (runtime setup) leaks initial horizon scheduler
      (menu.toRawHistory initial horizon scheduler next) := by
    funext next
    apply propext
    cases same : next.state with
    | none => simp [stop, RecoveryPublicExclusion, RecoveryClear,
        ReactiveApplication.ResponseMenu.toRawHistory, same]
    | some control =>
      simp only [stop, RecoveryPublicExclusion, RecoveryClear,
        ReactiveApplication.ResponseMenu.toRawHistory, same]
      constructor
      · intro nonempty allClear
        exact nonempty (allClear control rfl)
      · intro notAll empty
        apply notAll
        intro found equal
        cases Option.some.inj equal
        exact empty
  have law : nativeStopped = stopped.map classify := by
    dsimp only [nativeStopped, stopped]
    rw [stopEq]
    exact responseMenu_exclusion_classified_eq (runtime setup) leaks initial horizon scheduler
      initialized menu profile nativeCertificate recoveryCertificate menuCertificate history clear
  have valueEq (next : (menu.protocol initial horizon scheduler).History) :
      read (classify next) = if stop next then excludedPayoff who else
        recoveryExclusionBase parameter utility excludedPayoff next.state who := by
    have clearIff : RecoveryClear (runtime setup) leaks initial horizon scheduler
        (menu.toRawHistory initial horizon scheduler next) ↔ ¬ stop next := by
      rw [stopEq]
      simp only [not_not]
    by_cases clearNext : RecoveryClear (runtime setup) leaks initial horizon scheduler
        (menu.toRawHistory initial horizon scheduler next)
    · unfold classify recoveryClassifiedReadout
      rw [dite_eq_left clearNext, ite_eq_right (clearIff.mp clearNext)]
      change exclusionBase setup parameter utility excludedPayoff leaks
        (protocolState (runtime setup) leaks next.state) who =
          recoveryExclusionBase parameter utility excludedPayoff next.state who
      cases same : next.state with
      | none => rfl
      | some control =>
        have noExclusion : control.execution.application.excluded = ∅ := clearNext control same
        exact (recoveryExclusionBase_of_not_excluded parameter utility excludedPayoff control who
          (by simp [noExclusion])).symm
    · have exited : stop next := not_not.mp (fun absent => clearNext (clearIff.mpr absent))
      unfold classify recoveryClassifiedReadout
      rw [dite_eq_right clearNext, ite_eq_left exited]
      rfl
  have eventEq : classify ⁻¹' {label | ForeignExclusionLabel who label} =
      {next | stop next ∧ ¬ RecoveryExcluded (setup := setup) (leaks := leaks) who next.state} := by
    ext next
    change ForeignExclusionLabel who (classify next) ↔ _
    unfold classify recoveryClassifiedReadout
    split_ifs with clearNext
    · have notStopped : ¬ stop next := by rw [stopEq]; exact not_not.mpr clearNext
      simp only [ForeignExclusionLabel, Set.mem_ofPred_eq, notStopped, false_and]
    · have exited : stop next := by rw [stopEq]; exact clearNext
      cases same : next.state <;> simp [ForeignExclusionLabel, recoveryFailureOwners,
        RecoveryExcluded, ReactiveApplication.ResponseMenu.toRawHistory, same, exited,
        Set.mem_ofPred_eq]
  have estimate := recovery_expect_sub_stopped_le_foreign_exit parameter utility excludedPayoff
    menu initial horizon scheduler menuCertificate profile who nonnegative payoffBounded
    excludedBounded history
  change |expect _ _ - expect stopped _| ≤
    (2 * bound) * (stopped.toOuterMeasure _).toReal at estimate
  rw [law, expect_map, PMF.toOuterMeasure_map_apply, eventEq]
  change |expect _ _ - expect stopped (read ∘ classify)| ≤ _
  simpa only [Function.comp_def, valueEq] using estimate

end Vegas

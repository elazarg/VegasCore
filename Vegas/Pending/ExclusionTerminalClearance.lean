/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionContinuationLaw
import Interaction.ReactiveResponseEmbedding
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Terminal public failure bounds the first-exclusion coupling error -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "N" => ReactiveApplication.information (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "R" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler
local notation "NP" => ReactiveApplication.protocol (reactiveApplication runtime leaks)
  (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
local notation "RP" => ReactiveApplication.protocol
  (recoveryApplication runtime leaks) initial horizon scheduler

/-- Public native failures persist after a first-exit stop. Thus its exit mass
is exactly the terminal public-failure mass, without a native completion contract. -/
theorem native_exit_mass_eq_terminal_failure_mass
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (N).BehavioralPolicy who)
    (certificate : (NP).WellFoundedHistories) (history : (NP).History) :
    ((((N).runBehavioralUntil certificate profile
      (fun next => ¬ NativeClear runtime leaks initial horizon scheduler next) history).map
        (nativeStoppedReadout runtime leaks initial horizon scheduler)) none).toReal =
      (((N).runBehavioralTerminalFrom certificate profile history).toOuterMeasure
        {next | ¬ NativeClear runtime leaks initial horizon scheduler next}).toReal := by
  classical
  let clear := NativeClear runtime leaks initial horizon scheduler
  let indicator := ({next : (NP).History | ¬ clear next} : Set (NP).History).indicator
    (fun _ => (1 : ℝ))
  have nativeInitialized : ∀ native ∈ (initial.map RecoveryState.native).support,
      ∃ inputs, native = State.initial inputs := by
    intro native member
    obtain ⟨recovery, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    obtain ⟨inputs, rfl⟩ := initialized recovery supported
    exact ⟨inputs, rfl⟩
  have persists : ∀ start : (NP).History, ¬ clear start →
      ∀ final ∈ ((N).runBehavioralTerminalFrom certificate profile start).support,
        ¬ clear final := by
    intro start
    induction start using certificate.induction with
    | _ start ih =>
      intro failed final member
      by_cases ended : (NP).terminal start.state
      · rw [InformationModel.runBehavioralTerminalFrom,
          (NP).randomizedBackwardLaw_of_terminal ended, PMF.mem_support_pure_iff] at member
        exact member ▸ failed
      · rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate profile 1 start,
          PMF.mem_support_bind_iff] at member
        obtain ⟨next, supported, continued⟩ := member
        obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
          (N).mem_support_runBehavioralFrom_one profile ended supported
        apply ih next ⟨joint, legal, realized⟩ ?_ final continued
        exact fun nextClear => failed (native_clear_before_transition runtime leaks
          (initial.map RecoveryState.native) nativeInitialized horizon
          (nativeScheduler runtime leaks scheduler) start.trace joint realized nextClear)
  have bounded : ∀ final, |indicator final| ≤ 1 := by
    intro final
    simp only [indicator, Set.indicator_apply]
    split <;> norm_num
  have tower : expect ((N).runBehavioralTerminalFrom certificate profile history) indicator =
      expect ((N).runBehavioralUntil certificate profile (fun next => ¬ clear next) history)
        indicator := by
    rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate profile
      (fun next => ¬ clear next) history,
      expect_bind_tower_bounded _ _ _ bounded]
    apply expect_congr_on_support
    intro stop member
    by_cases failed : ¬ clear stop
    · have same : expect ((N).runBehavioralTerminalFrom certificate profile stop) indicator = 1 :=
        (expect_congr_on_support fun final supported => by
          simp [indicator, persists stop failed final supported]).trans
            (expect_constant _ 1)
      simpa [indicator, failed] using same
    · have ended := ((N).mem_support_runBehavioralUntil certificate profile
        (fun next => ¬ clear next) history stop member).resolve_left failed
      rw [InformationModel.runBehavioralTerminalFrom,
        (NP).randomizedBackwardLaw_of_terminal ended, expect_pure]
  have stoppedMass :
      ((((N).runBehavioralUntil certificate profile (fun next => ¬ clear next) history).map
        (nativeStoppedReadout runtime leaks initial horizon scheduler)) none).toReal =
      expect ((N).runBehavioralUntil certificate profile (fun next => ¬ clear next) history)
        indicator := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rw [show (nativeStoppedReadout runtime leaks initial horizon scheduler ⁻¹' {none}) =
        {next | ¬ clear next} by
      ext next
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
        nativeStoppedReadout]
      split_ifs <;> simp_all [clear]]
    exact (expect_indicator _ _).symm
  exact stoppedMass.trans (tower.symm.trans (expect_indicator _ _))

/-- Every clear-agreeing joint readout is close in the actual recovery and
native runtimes, with error equal to native terminal public-failure mass. -/
theorem terminal_readout_withinTV_of_native_failure
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (profile : ∀ who, (R).BehavioralPolicy who)
    (nativeCertificate : (NP).WellFoundedHistories)
    (recoveryCertificate : (RP).WellFoundedHistories)
    {Outcome : Type} (nativeReadout : (NP).History → Outcome)
    (recoveryReadout : (RP).History → Outcome)
    (agree : ∀ history (clear : RecoveryClear runtime leaks initial horizon scheduler history),
      recoveryReadout history = nativeReadout
        (nativeHistory runtime leaks initial horizon scheduler history clear))
    (history : (RP).History)
    (clear : RecoveryClear runtime leaks initial horizon scheduler history) :
    let native := nativeHistory runtime leaks initial horizon scheduler history clear
    let players := nativeProfile runtime leaks initial horizon scheduler profile
    PMF.WithinTV
      ((((N).runBehavioralTerminalFrom nativeCertificate players native).toOuterMeasure
        {next | ¬ NativeClear runtime leaks initial horizon scheduler next}).toReal)
      (((R).runBehavioralTerminalFrom recoveryCertificate profile history).map recoveryReadout)
      (((N).runBehavioralTerminalFrom nativeCertificate players native).map nativeReadout) := by
  intro native players
  have exactStop := runBehavioralUntil_exclusion_map_eq runtime leaks initial horizon scheduler
    initialized profile nativeCertificate recoveryCertificate history clear
  have errorEq := congrArg (fun law : PMF (Option (NP).History) => (law none).toReal) exactStop
  have close := terminal_readout_withinTV_of_exclusion runtime leaks initial horizon scheduler
    initialized profile nativeCertificate recoveryCertificate nativeReadout recoveryReadout agree
      history clear
  dsimp only at close
  rw [← errorEq, native_exit_mass_eq_terminal_failure_mass runtime leaks initial horizon scheduler
    initialized players nativeCertificate native] at close
  exact close

/-- Finite recovery response menus retain the initialized raw coupling for
arbitrary state readouts agreeing while no player is excluded. -/
theorem responseMenu_initialized_readout_withinTV_of_native_failure
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    (menu : (runtime.recoveryApplication leaks).ResponseMenu)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    {Outcome : Type} (nativeRead : (runtime.reactiveApplication leaks).ProtocolState → Outcome)
    (recoveryRead : (runtime.recoveryApplication leaks).ProtocolState → Outcome)
    (agree : ∀ state, (∀ current, state = some current →
      current.execution.application.excluded = ∅) →
      recoveryRead state = nativeRead (protocolState runtime leaks state)) :
    PMF.WithinTV
      ((((N).runBehavioral
        (nativeProfile runtime leaks initial horizon scheduler
          (fun who => menu.embedPolicy initial horizon scheduler who (profile who)))
        (2 * horizon + 1)).toOuterMeasure
        {next | ¬ NativeClear runtime leaks initial horizon scheduler next}).toReal)
      (((menu.information initial horizon scheduler).runBehavioral profile (2 * horizon + 1)).map
        (fun final => recoveryRead final.state))
      (((N).runBehavioral
        (nativeProfile runtime leaks initial horizon scheduler
          (fun who => menu.embedPolicy initial horizon scheduler who (profile who)))
        (2 * horizon + 1)).map
        (fun final => nativeRead final.state)) := by
  let players := fun who => menu.embedPolicy initial horizon scheduler who (profile who)
  let projected := nativeProfile runtime leaks initial horizon scheduler players
  let fuel := 2 * horizon + 1
  let nativeBounded := (runtime.reactiveApplication leaks).bounded
    (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
  let recoveryBounded := (runtime.recoveryApplication leaks).bounded initial horizon scheduler
  let nativeCertificate := nativeBounded.wellFoundedHistories
  let recoveryCertificate := recoveryBounded.wellFoundedHistories
  have close := terminal_readout_withinTV_of_native_failure runtime leaks initial horizon scheduler
    initialized players nativeCertificate recoveryCertificate
      (fun final => nativeRead final.state) (fun final => recoveryRead final.state)
      (fun history clear => agree history.state clear)
      (RP).initHistory (by intro current impossible; cases impossible)
  have startEq (clear : RecoveryClear runtime leaks initial horizon scheduler (RP).initHistory) :
      nativeHistory runtime leaks initial horizon scheduler (RP).initHistory clear =
        (NP).initHistory := rfl
  dsimp only at close
  rw [startEq,
    (N).runBehavioralTerminalFrom_initHistory nativeCertificate
      (nativeProfile runtime leaks initial horizon scheduler players) nativeBounded,
    (R).runBehavioralTerminalFrom_initHistory recoveryCertificate players recoveryBounded] at close
  have recoveryLaw := congrArg (fun law : PMF (RP).History =>
    law.map (fun final => recoveryRead final.state))
    (menu.run_embed initial horizon scheduler profile fuel
      (menu.protocol initial horizon scheduler).initHistory)
  rw [PMF.map_comp] at recoveryLaw
  change (((menu.information initial horizon scheduler).runBehavioral profile fuel).map
    (fun final => recoveryRead final.state)) =
      ((R).runBehavioral players fuel).map (fun final => recoveryRead final.state) at recoveryLaw
  rw [← recoveryLaw] at close
  exact close

end Vegas.EventGraphRuntime.RecoveryProjection

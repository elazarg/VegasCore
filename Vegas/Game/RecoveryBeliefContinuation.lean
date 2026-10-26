/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryContinuationComparison

/-! # Recovery continuation error averaged over actual histories -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "RawNative" => ReactiveApplication.protocol (application setup runtime leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)

open Classical in
/-- The actual projected native law stopped at first public exclusion or focal
debt. An already excluded history keeps its existing classified exit label. -/
def nativeDebtStoppedLaw (certificate : (RawNative).WellFoundedHistories)
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player) (history : (RP).History) :
    PMF (Finset Player ⊕ (RawNative).History) :=
  if clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅ then
    (((application setup runtime leaks).information ((Initial).map RecoveryState.native) horizon
      (NativeScheduler)).runBehavioralUntil certificate
      (nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)))
      (fun final => ¬ NativeClear runtime leaks Initial horizon scheduler final ∨
        DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) final.state)
      (nativeHistory runtime leaks Initial horizon scheduler
        ((RMenu).toRawHistory Initial horizon scheduler history) clear)).map
      (nativeClassifiedReadout runtime leaks Initial horizon scheduler)
  else
    PMF.pure (recoveryClassifiedReadout runtime leaks Initial horizon scheduler
      ((RMenu).toRawHistory Initial horizon scheduler history))

open Classical in
/-- Averaging actual recovery payoff error over clear controlled histories
charges only the foreign-exit probability of their concrete stopped native law. -/
theorem recovery_belief_expect_abs_sub_native_debt_stopped_le_foreign_exit
    [Finite (RP).History] {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (recoveryCertificate : ((recoveryApplication runtime leaks).protocol Initial horizon
      scheduler).WellFoundedHistories)
    (menuCertificate : (RP).WellFoundedHistories)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player)
    (payoffBounded : ∀ final : (RP).History,
      |recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff final.state
        focal| ≤ payoffBound)
    (excludedBounded : |excludedPayoff focal| ≤ payoffBound)
    (belief : PMF (RP).History)
    (controlled : ∀ history ∈ belief.support,
      ∃ current : (recoveryApplication runtime leaks).Control,
        history.state = some current ∧ current.execution.application.excluded = ∅) :
    let kernel := nativeDebtStoppedLaw setup runtime leaks bounds horizon scheduler rawCertificate
      profile
      focal
    let read := Sum.elim (fun _ : Finset Player => excludedPayoff focal)
      (fun final : (RawNative).History =>
        if DecodedState setup runtime leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) final.state then excludedPayoff focal
        else exclusionBase setup runtime parameter utility excludedPayoff leaks final.state focal)
    expect belief (fun history =>
      |expect ((R).runBehavioralTerminalFrom menuCertificate profile history)
          (fun final => recoveryExclusionBase (runtime := runtime) parameter utility
            excludedPayoff final.state focal) -
        expect (kernel history) read|) ≤
      (2 * payoffBound) * ((belief.bind kernel).toOuterMeasure
        {label | ForeignExclusionLabel focal label}).toReal := by
  intro kernel read
  let event := {label : Finset Player ⊕ (RawNative).History | ForeignExclusionLabel focal label}
  let mass := fun history => ((kernel history).toOuterMeasure event).toReal
  have pointwise : ∀ history ∈ belief.support,
      |expect ((R).runBehavioralTerminalFrom menuCertificate profile history)
          (fun final => recoveryExclusionBase (runtime := runtime) parameter utility
            excludedPayoff final.state focal) -
        expect (kernel history) read| ≤ (2 * payoffBound) * mass history := by
    intro history supported
    obtain ⟨current, state, empty⟩ := controlled history supported
    have clear : ∀ next, history.state = some next →
        next.execution.application.excluded = ∅ := by
      intro next same
      cases Option.some.inj (state.symm.trans same)
      exact empty
    have estimate := recovery_expect_sub_native_debt_stopped_le_foreign_exit (runtime := runtime)
      parameter utility
      excludedPayoff (failureProfile setup.program) Initial (initialLaw_initialized setup) horizon
      scheduler completes (RMenu) rawCertificate recoveryCertificate menuCertificate profile focal
        nonnegative payoffBounded excludedBounded history current state empty
    simpa only [kernel, mass, nativeDebtStoppedLaw, dite_eq_left clear, read, event] using estimate
  have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  rw [expect_const_mul] at averaged
  refine averaged.trans (le_of_eq (congrArg (fun value => (2 * payoffBound) * value) ?_))
  let indicator := fun label => @ite ℝ (label ∈ event) (Classical.propDecidable _) 1 0
  have inner : mass = fun history => expect (kernel history) indicator := by
    funext history
    exact (expect_indicator (kernel history) event).symm
  have indicatorBounded : ∀ label, |indicator label| ≤ 1 := fun label => by
    dsimp only [indicator]
    split <;> norm_num
  rw [inner, ← expect_bind_tower_bounded belief kernel indicator indicatorBounded]
  exact expect_indicator (belief.bind kernel) event

end Vegas.RecoveryOnePacket

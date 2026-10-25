/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryInitializedLaw
import Vegas.Game.RecoveryContinuationComparison
import Vegas.Pending.ExclusionTerminalClearance

/-! # Initialized laws of the actual common recovery strategy -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

private theorem initialized_state_law_prior_eq
    {Player : Type} [DecidableEq Player] [Fintype Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information first horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) {Outcome : Type} (readout : app.ProtocolState → Outcome) :
    ((menu.information first horizon scheduler).runBehavioral profile fuel).map
        (fun final => readout final.state) =
      ((menu.information second horizon scheduler).runBehavioral
        (fun who input => (profile who input).map (Equiv.cast (congrArg
          (fun initial => (menu.information initial horizon scheduler).Choice who input) same)))
        fuel).map (fun final => readout final.state) := by
  subst second
  simp only [Equiv.cast_refl, Equiv.coe_refl, PMF.map_id]

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "RawN" => ReactiveApplication.information (application setup leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "RawR" => ReactiveApplication.information
  (recoveryApplication (runtime setup) leaks) Initial horizon scheduler
local notation "RawNP" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "RawRP" => ReactiveApplication.protocol
  (recoveryApplication (runtime setup) leaks) Initial horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

/-- Embedding the actual recovery policy, projecting it, and changing the prior
retain every initialized finite-menu native state law exactly. -/
theorem sourceNativeProfile_initialized_state_law
    (profile : ∀ who, (R).BehavioralPolicy who) (fuel : Nat)
    {Outcome : Type} (readout : (application setup leaks).ProtocolState → Outcome) :
    ((RawN).runBehavioral
      (nativeProfile (runtime setup) leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who))) fuel).map
        (fun final => readout final.state) =
      ((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler profile)
        fuel).map (fun final => readout final.state) := by
  let genericInitial := PMF.map RecoveryState.native Initial
  let genericProfile := boundedNativeProfile (runtime setup) leaks bounds Initial horizon scheduler
    profile
  have rawLaw := (NMenu).run_embed genericInitial horizon (NativeScheduler) genericProfile fuel
    ((NMenu).protocol genericInitial horizon (NativeScheduler)).initHistory
  have profiles : (fun who => (NMenu).embedPolicy genericInitial horizon (NativeScheduler) who
      (genericProfile who)) =
      nativeProfile (runtime setup) leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)) := by
    funext who
    exact boundedNativeProfile_embed (runtime setup) leaks bounds Initial horizon scheduler
      profile who
  rw [profiles] at rawLaw
  have rawRead := congrArg (fun law : PMF (RawNP).History =>
    law.map (fun final => readout final.state)) rawLaw
  rw [PMF.map_comp] at rawRead
  have prior := initialized_state_law_prior_eq (NMenu) (initialLaw_native setup) horizon
    (NativeScheduler) genericProfile fuel readout
  have profileCast : (fun who input => (genericProfile who input).map (Equiv.cast (congrArg
      (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((NMenu).information initial horizon (NativeScheduler)).Choice who input)
          (initialLaw_native setup)))) =
      sourceNativeProfile setup leaks bounds horizon scheduler profile := by
    funext who input
    exact (sourceNativeProfile_eq_cast setup leaks bounds horizon scheduler profile who input).symm
  have replaced := congrArg (fun players : ∀ who, (N).BehavioralPolicy who =>
    ((N).runBehavioral players fuel).map (fun final => readout final.state)) profileCast
  exact rawRead.symm.trans (prior.trans replaced)

/-- Raw projection and canonical finite native play retain the same terminal
public-failure mass at every finite horizon. -/
theorem sourceNativeProfile_initialized_failure_mass_eq
    (profile : ∀ who, (R).BehavioralPolicy who) (fuel : Nat) :
    (((RawN).runBehavioral
      (nativeProfile (runtime setup) leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)))
        fuel).toOuterMeasure
         {next | ¬ NativeClear (runtime setup) leaks Initial horizon scheduler next}).toReal =
      (((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler profile)
        fuel).toOuterMeasure {next | ¬ Clear next.state}).toReal := by
  classical
  let projected := nativeProfile (runtime setup) leaks Initial horizon scheduler
    (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who))
  have states := sourceNativeProfile_initialized_state_law setup leaks bounds horizon scheduler
    profile fuel id
  have failureEq :
      (((RawN).runBehavioral projected fuel).toOuterMeasure
        {next | ¬ NativeClear (runtime setup) leaks Initial horizon scheduler next}).toReal =
      (((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler profile)
        fuel).toOuterMeasure {next | ¬ Clear next.state}).toReal := by
    have same : {next : (RawNP).History |
        ¬ NativeClear (runtime setup) leaks Initial horizon scheduler next} =
        History.state ⁻¹' {state | ¬ Clear state} := by
      ext next
      exact not_congr (nativeClear_iff_stateInvariant (runtime setup) leaks Initial horizon
        scheduler next)
    rw [same, ← PMF.toOuterMeasure_map_apply]
    change (PMF.toOuterMeasure
      (((RawN).runBehavioral projected fuel).map (fun final => id final.state))
        {state | ¬ Clear state}).toReal = _
    rw [states, PMF.toOuterMeasure_map_apply]
    rfl
  exact failureEq

/-- The actual initialized finite recovery and native-projection joint laws
are close by exactly the native projection's terminal public-failure mass. -/
theorem recovery_initialized_projection_withinTV
    (profile : ∀ who, (R).BehavioralPolicy who)
    {Outcome : Type} (nativeRead : (application setup leaks).ProtocolState → Outcome)
    (recoveryRead : (recoveryApplication (runtime setup) leaks).ProtocolState → Outcome)
    (agree : ∀ state, (∀ current, state = some current →
      current.execution.application.excluded = ∅) →
      recoveryRead state = nativeRead (protocolState (runtime setup) leaks state)) :
    PMF.WithinTV
      ((((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler profile)
        (2 * horizon + 1)).toOuterMeasure {next | ¬ Clear next.state}).toReal)
      (((R).runBehavioral profile (2 * horizon + 1)).map (fun final => recoveryRead final.state))
      (((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler profile)
        (2 * horizon + 1)).map (fun final => nativeRead final.state)) := by
  have close := responseMenu_initialized_readout_withinTV_of_native_failure (runtime setup) leaks
    Initial horizon scheduler (initialLaw_initialized setup) (RMenu) profile nativeRead recoveryRead
      agree
  rw [sourceNativeProfile_initialized_failure_mass_eq setup leaks bounds horizon scheduler profile
    (2 * horizon + 1),
    sourceNativeProfile_initialized_state_law setup leaks bounds horizon scheduler
      profile (2 * horizon + 1) nativeRead] at close
  exact close


variable [Fintype ((ReactiveApplication.ResponseMenu.protocol (Recovery.onePacketMenu (runtime
    setup) leaks bounds) (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState
    (graph setup))) (initialLaw setup)) horizon scheduler)).History]
  [(application setup leaks).FiniteNature (initialLaw setup) ((nativeScheduler (runtime setup)
    leaks scheduler))]
  [∀ who, DecidableEq (((model setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler)).InfoState
    who)]
  (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
  (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
  (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
  (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
  {slots : Nat}
  (weights : ℕ → ∀ p, PMF (Part setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler slots p)) (n : ℕ)
  (fallback : ∀ who, ((model setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler)).Policy
    who) (strategy : ∀ who, ((model setup leaks bounds (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).BehavioralPolicy who)
  (assembled : strategy = ((model setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).agentBehavior ((model setup leaks bounds (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).playedInformation fallback
    (fun agent => (weights n (pool setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler agent)).bind
      (component setup leaks bounds (PMF.map (fun native => (RecoveryState.mk native ∅ :
    RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler (sequence n) (scale n)
        (positive n).le (le_one n) agent)))
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)
include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- Actual common recovery strategies retain initialized honest native play;
only the original completion weights are used. -/
theorem sourceNativeProfile_dominatesHonestFrom_initialized
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) (slotRetention (scale n))
      (sourceNativeProfile setup leaks bounds horizon scheduler strategy) (NP).initHistory := by
  classical
  have retained := nativeComparison_dominatesHonestFrom_initialized setup leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights n opportunity
      inclusion timely completes certificate
  intro fuel history reached who choice
  have lower := retained fuel history reached who choice
  by_cases running : ¬ (NP).terminal history.state
  · have clear : Clear history.state := by
      cases current : history.state with
      | none => trivial
      | some control =>
        obtain ⟨point, decoded, intended⟩ := recovery_honest_initialized_intended
          (initialLaw_initialized setup) (initialLaw_native setup) opportunity inclusion timely
          completes wellFormed covers capacity (sequence n) certificate fuel history reached control
            current
        exact exclusionEvidence_of_decodedIntended
          ((NMenu).toRawTrace (initialLaw setup) horizon (NativeScheduler)
            (current ▸ history.trace)) decoded intended
    have valid : ∀ control, history.state = some control →
        ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) := by
      intro control current
      rw [current] at clear
      exact clear
    rw [nativeComparisonStrategy_eq_projection_at_clear setup leaks bounds horizon scheduler
      sequence scale positive le_one weights n fallback strategy assembled history.trace valid
        running who] at lower
    exact lower
  · have ended := not_not.mp running
    have inactive : ¬ (NP).active history.state who := by
      cases current : history.state with
      | none => rw [current] at ended; exact ended.elim
      | some control =>
        change control.actor ≠ some who
        rw [current] at ended
        change control.remaining = 0 ∧ control.actor = none at ended
        simp [ended.2]
    rw [← (N).behavioral_eq_of_not_active
      (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n who) (sourceNativeProfile setup leaks bounds horizon scheduler strategy who)
        history.trace
          inactive]
    exact lower

include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- Actual native projection of common recovery play has only the retained
honest mass available for a public failure, including at initialization. -/
theorem sourceNativeProfile_initialized_failure_mass_le :
    (((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler strategy)
      (2 * horizon + 1)).toOuterMeasure {history | ¬ Clear history.state}).toReal ≤
      (Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - slotRetention (scale n)) := by
  classical
  let certificate := ((NMenu).bounded (initialLaw setup) horizon
    (NativeScheduler)).wellFoundedHistories
  let honest := honestProfile setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
    (sequence n)
  have dominates := sourceNativeProfile_dominatesHonestFrom_initialized setup leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights n fallback strategy
      assembled opportunity inclusion timely completes certificate
  have close := onePacket_withinTV_honest setup leaks bounds (initialLaw setup) horizon
    (NativeScheduler) (sequence n) (slotRetention_nonneg (positive n).le (le_one n))
    (slotRetention_le_one (positive n).le (le_one n)) _ dominates (2 * horizon + 1)
  have honestClear : (((N).runBehavioral honest (2 * horizon + 1)).toOuterMeasure
      {history | ¬ Clear history.state}).toReal = 0 := by
    rw [← expect_indicator]
    trans expect ((N).runBehavioral honest (2 * horizon + 1)) (fun _ => (0 : ℝ))
    · apply expect_congr_on_support
      intro history member
      have clear : Clear history.state := by
        cases current : history.state with
        | none => trivial
        | some control =>
          obtain ⟨point, decoded, intended⟩ := recovery_honest_initialized_intended
            (initialLaw_initialized setup) (initialLaw_native setup) opportunity inclusion timely
            completes wellFormed covers capacity (sequence n) certificate (2 * horizon + 1)
              history member control current
          exact exclusionEvidence_of_decodedIntended
            ((NMenu).toRawTrace (initialLaw setup) horizon (NativeScheduler)
              (current ▸ history.trace)) decoded intended
      simp [clear]
    · exact expect_zero _
  have bound := close.symm {history | ¬ Clear history.state}
  rw [honestClear, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at bound
  exact bound

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- The initialized joint typed-readout and realized base-payoff law of the
actual common recovery strategy approaches its original intended source law. -/
theorem recovery_initialized_readout_withinTV :
    PMF.WithinTV (2 * ((Fintype.card Player * (2 * horizon + 1) : ℕ) *
      (1 - slotRetention (scale n))))
      (((R).runBehavioral strategy (2 * horizon + 1)).map (fun final =>
        (sourceReadout setup leaks (protocolState (runtime setup) leaks final.state),
          recoveryExclusionBase parameter utility excludedPayoff final.state)))
      ((setup.intendedModel.runBehavioral (sequence n).strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  classical
  let fuel := 2 * horizon + 1
  let certificate := ((NMenu).bounded (initialLaw setup) horizon
    (NativeScheduler)).wellFoundedHistories
  have close := recovery_initialized_projection_withinTV setup leaks bounds horizon scheduler
    strategy
    (fun state => (sourceReadout setup leaks state,
      exclusionBase setup parameter utility excludedPayoff leaks state))
    (fun state => (sourceReadout setup leaks (protocolState (runtime setup) leaks state),
      recoveryExclusionBase parameter utility excludedPayoff state)) (by
        intro state clear
        refine Prod.ext rfl ?_
        funext who
        cases state with
        | none => rfl
        | some control =>
          exact recoveryExclusionBase_of_not_excluded parameter utility excludedPayoff control who
            (by simp [clear control rfl]))
  have boundedClose := close.mono (sourceNativeProfile_initialized_failure_mass_le setup leaks
    bounds horizon scheduler wellFormed covers capacity sequence scale positive le_one weights n
      fallback strategy assembled opportunity inclusion timely completes)
  have honestLaw := recovery_honest_initialized_readout_law (initialLaw_initialized setup)
    (initialLaw_native setup) opportunity inclusion timely completes wellFormed covers capacity
      (sequence n) certificate
  rw [(N).runBehavioralTerminalFrom_initHistory certificate
    (honestProfile setup leaks bounds (initialLaw setup) horizon (NativeScheduler) (sequence n))
      ((NMenu).bounded (initialLaw setup) horizon (NativeScheduler))] at honestLaw
  have nativeClose := onePacket_readout_exclusion_withinTV setup leaks bounds (initialLaw setup)
    horizon (NativeScheduler) parameter utility excludedPayoff (sequence n) (sequence n).strategy
    (instructionCount setup.program + 1) fuel honestLaw
      (slotRetention_nonneg (positive n).le (le_one n))
      (slotRetention_le_one (positive n).le (le_one n))
      (sourceNativeProfile setup leaks bounds horizon scheduler strategy)
      (sourceNativeProfile_dominatesHonestFrom_initialized setup leaks bounds horizon scheduler
        wellFormed covers capacity sequence scale positive le_one weights n fallback strategy
          assembled opportunity inclusion timely completes certificate)
  simpa only [fuel, two_mul] using boundedClose.trans nativeClose

include wellFormed covers capacity opportunity inclusion timely completes in
/-- A common completion sequence has a uniform vanishing initialized joint-law
error against the same original source assessment sequence. -/
theorem recovery_initialized_lawApproximation
    (strategies : ℕ → ∀ who, (R).BehavioralPolicy who)
    (allAssembled : ∀ n, strategies n = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (vanishing : Filter.Tendsto scale Filter.atTop (nhds 0)) :
    ∃ lawError : ℕ → ℝ, Filter.Tendsto lawError Filter.atTop (nhds 0) ∧
      ∀ n outcome,
        |((((R).runBehavioral (strategies n) (2 * horizon + 1)).map (fun final =>
            (sourceReadout setup leaks (protocolState (runtime setup) leaks final.state),
              recoveryExclusionBase parameter utility excludedPayoff final.state)))
                outcome).toReal -
          (((setup.intendedModel.runBehavioral (sequence n).strategy
            (instructionCount setup.program + 1)).map
            (intendedReadoutExclusion setup parameter utility excludedPayoff)) outcome).toReal| ≤
          lawError n := by
  refine ⟨fun n => 2 * ((Fintype.card Player * (2 * horizon + 1) : ℕ) *
    (1 - slotRetention (scale n))), ?_, fun n outcome => ?_⟩
  · have retained := tendsto_slotRetention vanishing
    have difference := (tendsto_const_nhds (x := (1 : ℝ))).sub retained
    have converges := (difference.const_mul
      ((Fintype.card Player * (2 * horizon + 1) : ℕ) : ℝ)).const_mul 2
    simpa using converges
  · exact (recovery_initialized_readout_withinTV setup leaks bounds horizon scheduler wellFormed
      covers capacity sequence scale positive le_one weights n fallback (strategies n)
      (allAssembled n) opportunity inclusion timely completes parameter utility
        excludedPayoff).apply
        outcome

end Vegas.RecoveryOnePacket

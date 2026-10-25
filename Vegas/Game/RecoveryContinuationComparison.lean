/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonStopped
import Vegas.Game.RecoveryForeignFailureBound
import Vegas.Game.RecoveryDebtStoppedComparison
import Vegas.Game.RecoveryNativePrior
import GameTheory.Protocol.PolicyRandomization
import Vegas.Game.AsyncDeviationForeign

/-! # Actual recovery continuation error from rare foreign first exclusions -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection


private theorem history_restate {Player : Type} {T : ExecutionProtocol Player}
    (history : T.History) {state : T.State} (same : history.state = state) :
    (⟨state, same ▸ history.trace⟩ : T.History) = history := by
  cases history
  cases same
  rfl

private theorem history_cast_raw {Player : Type} [DecidableEq Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler) (history : (menu.protocol first horizon scheduler).History) :
    menu.toRawHistory second horizon scheduler
        (Equiv.cast (congrArg (fun initial => (menu.protocol initial horizon scheduler).History)
          same) history) =
      Equiv.cast (congrArg (fun initial => (app.protocol initial horizon scheduler).History) same)
        (menu.toRawHistory first horizon scheduler history) := by
  subst second
  rfl

private theorem stateEventUntil_prior_eq {Player : Type} [DecidableEq Player] [Fintype Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler)
    (firstCertificate : (menu.protocol first horizon scheduler).WellFoundedHistories)
    (secondCertificate : (menu.protocol second horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information first horizon scheduler).BehavioralPolicy who)
    (stop event : app.ProtocolState → Prop)
    (history : (menu.protocol first horizon scheduler).History) :
    (((menu.information first horizon scheduler).runBehavioralUntil firstCertificate profile
      (fun next => stop next.state) history).toOuterMeasure {next | event next.state}).toReal =
      (((menu.information second horizon scheduler).runBehavioralUntil secondCertificate
        (fun who input => (profile who input).map (Equiv.cast (congrArg
          (fun initial => (menu.information initial horizon scheduler).Choice who input) same)))
        (fun next => stop next.state)
        (Equiv.cast (congrArg (fun initial => (menu.protocol initial horizon scheduler).History)
          same) history)).toOuterMeasure {next | event next.state}).toReal := by
  subst second
  simp only [Equiv.cast_refl, Equiv.coe_refl, PMF.map_id]
  rfl

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
  (MessageBounds.onePacketMenu (runtime setup) leaks bounds) (initialLaw setup) horizon
  (NativeScheduler)

/-- The genuine finite native projection of any entire actual clear recovery
history at the canonical source prior. -/
def nativeClearHistory (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) : (NP).History :=
  Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol initial horizon (NativeScheduler)).History) (initialLaw_native setup))
    (exists_nativeBoundedHistory (runtime setup) leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler history clear).choose

/-- The finite projection retains the exact realized projected raw history. -/
theorem nativeClearHistory_raw (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler)
        (nativeClearHistory setup leaks bounds horizon scheduler history clear) =
      Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
          (initialLaw_native setup))
        (nativeHistory (runtime setup) leaks Initial horizon scheduler
          ((RMenu).toRawHistory Initial horizon scheduler history) clear) := by
  unfold nativeClearHistory
  rw [history_cast_raw (NMenu) (initialLaw_native setup) horizon (NativeScheduler)]
  exact congrArg _ (exists_nativeBoundedHistory (runtime setup) leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler history clear).choose_spec


/-- Exact raw projection uniquely identifies the finite native start used by
the continuation estimate, regardless of the projection's chosen witnesses. -/
theorem nativeClearHistory_eq_of_raw (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (native : (NP).History)
    (same : (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) native =
      Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
          (initialLaw_native setup))
        (nativeHistory (runtime setup) leaks Initial horizon scheduler
          ((RMenu).toRawHistory Initial horizon scheduler history) clear)) :
    nativeClearHistory setup leaks bounds horizon scheduler history clear = native :=
  (NMenu).toRawHistory_injective (initialLaw setup) horizon (NativeScheduler)
    ((nativeClearHistory_raw setup leaks bounds horizon scheduler history clear).trans same.symm)

/-- Replacing a whole actual recovery policy commutes with canonical projection. -/
theorem sourceNativeProfile_update
    (profile : ∀ who, (R).BehavioralPolicy who)
    (focal : Player) (alternative : (R).BehavioralPolicy focal) :
    sourceNativeProfile setup leaks bounds horizon scheduler
      (Profile.update (sig := (R).behavioralSignature) profile focal alternative) =
      Profile.update (sig := (N).behavioralSignature)
        (sourceNativeProfile setup leaks bounds horizon scheduler profile) focal
        (fun input => (alternative (liftInformation (runtime setup) leaks input)).map
          (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler focal input)) := by
  funext who input
  by_cases same : who = focal
  · subst who
    simp only [sourceNativeProfile, Profile.update_same]
  · simp only [sourceNativeProfile, Profile.update_of_ne _ _ same]

/-- Canonical finite projection preserves the complete projected control state. -/
theorem nativeClearHistory_state (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    (nativeClearHistory setup leaks bounds horizon scheduler history clear).state =
      protocolState (runtime setup) leaks history.state := by
  have raw := nativeClearHistory_raw setup leaks bounds horizon scheduler history clear
  have states := congrArg History.state raw
  have castState {first second : PMF (EventGraphRuntime.State (graph setup))}
      (same : first = second)
      (found : ((application setup leaks).protocol first horizon (NativeScheduler)).History) :
      (Equiv.cast (congrArg (fun initial =>
        ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
          same) found).state = found.state := by
    subst second
    rfl
  exact states.trans (castState (initialLaw_native setup) _)

local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

open Classical in
/-- The raw native continuation induced by the actual recovery
profile inherits the common comparison's foreign first-exit rate. -/
theorem projected_foreign_exit_mass_le_rank [Fintype (RP).History]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [∀ who, DecidableEq ((R).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (focal : Player) (alternative : (R).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : (NP).WellFoundedHistories)
    (rawCertificate : ((application setup leaks).protocol ((Initial).map RecoveryState.native)
      horizon (NativeScheduler)).WellFoundedHistories)
    (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (current : (recoveryApplication (runtime setup) leaks).Control)
    (state : history.state = some current)
    (event : (graph setup).EventId)
    (turn : current.execution.application.native.publicView.ownTurn? focal = some event)
    (regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal
      (nativeClearHistory setup leaks bounds horizon scheduler history clear).trace) :
    let native := (application setup leaks).information ((Initial).map RecoveryState.native)
      horizon (NativeScheduler)
    let updated := Profile.update (sig := (R).behavioralSignature) strategy focal alternative
    let raw := (RMenu).toRawHistory Initial horizon scheduler history
    let law := native.runBehavioralUntil rawCertificate
      (nativeProfile (runtime setup) leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (updated who)))
      (fun final => ¬ ClearState final.state ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) final.state)
      (nativeHistory (runtime setup) leaks Initial horizon scheduler raw clear)
    (law.toOuterMeasure {final | ¬ ClearState final.state ∧
      focal ∉ nativeFailureOwners (runtime setup) leaks final.state}).toReal ≤
        ((scale n) ^ 2 + scale n) * (application setup leaks).rank horizon
          (protocolState (runtime setup) leaks history.state) := by
  intro native updated raw law
  let genericInitial := (Initial).map RecoveryState.native
  let genericModel := (NMenu).information genericInitial horizon (NativeScheduler)
  let genericProfile := boundedNativeProfile (runtime setup) leaks bounds Initial horizon scheduler
    updated
  let genericStart := (exists_nativeBoundedHistory (runtime setup) leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler history clear).choose
  have rawStart : (NMenu).toRawHistory genericInitial horizon (NativeScheduler) genericStart =
      nativeHistory (runtime setup) leaks Initial horizon scheduler raw clear :=
    (exists_nativeBoundedHistory (runtime setup) leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler history clear).choose_spec
  let genericCertificate : ((NMenu).protocol genericInitial horizon
      (NativeScheduler)).WellFoundedHistories :=
    Eq.mpr (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol initial horizon (NativeScheduler)).WellFoundedHistories)
        (initialLaw_native setup)) certificate
  let stop : (application setup leaks).ProtocolState → Prop := fun final =>
    ¬ ClearState final ∨ DecodedState setup leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) final
  let exits : (application setup leaks).ProtocolState → Prop := fun final =>
    ¬ ClearState final ∧ focal ∉ nativeFailureOwners (runtime setup) leaks final
  have rawLaw := (NMenu).runBehavioralUntil_embed genericInitial horizon (NativeScheduler)
    rawCertificate genericCertificate genericProfile (fun final => stop final.state) genericStart
  have profiles :
      (fun who => (NMenu).embedPolicy genericInitial horizon (NativeScheduler) who
        (genericProfile who)) =
      nativeProfile (runtime setup) leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (updated who)) := by
    funext who
    exact boundedNativeProfile_embed (runtime setup) leaks bounds Initial horizon scheduler
      updated who
  rw [profiles, rawStart] at rawLaw
  have rawMass :
      (law.toOuterMeasure {final | exits final.state}).toReal =
        ((genericModel.runBehavioralUntil genericCertificate genericProfile
          (fun final => stop final.state) genericStart).toOuterMeasure
            {final | exits final.state}).toReal := by
    have measured := congrArg
      (fun probability : PMF (((application setup leaks).protocol genericInitial horizon
          (NativeScheduler)).History) =>
        (probability.toOuterMeasure {final | exits final.state}).toReal) rawLaw
    refine measured.symm.trans ?_
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  have priorMass := stateEventUntil_prior_eq (NMenu) (initialLaw_native setup) horizon
    (NativeScheduler) genericCertificate certificate genericProfile stop exits genericStart
  have profileCast :
      (fun who input => (genericProfile who input).map (Equiv.cast (congrArg
        (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
          ((NMenu).information initial horizon (NativeScheduler)).Choice who input)
            (initialLaw_native setup)))) =
        sourceNativeProfile setup leaks bounds horizon scheduler updated := by
    funext who input
    exact (sourceNativeProfile_eq_cast setup leaks bounds horizon scheduler updated who input).symm
  have replaceProfile := congrArg
    (fun profile : ∀ who, (N).BehavioralPolicy who =>
      (((N).runBehavioralUntil certificate profile (fun final => stop final.state)
        (Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
          ((NMenu).protocol initial horizon (NativeScheduler)).History)
            (initialLaw_native setup)) genericStart)).toOuterMeasure
              {final | exits final.state}).toReal) profileCast
  have priorMass' := priorMass.trans replaceProfile
  let projected := nativeClearHistory setup leaks bounds horizon scheduler history clear
  let nativeCurrent := RecoveryProjection.control (runtime setup) leaks current
  have projectedState : projected.state = some nativeCurrent :=
    (nativeClearHistory_state setup leaks bounds horizon scheduler history clear).trans
      (congrArg (protocolState (runtime setup) leaks) state)
  let trace : (NP).Trace (some nativeCurrent) := projectedState ▸ projected.trace
  have reconstructed : (⟨some nativeCurrent, trace⟩ : (NP).History) = projected :=
    history_restate projected projectedState
  have regularTransport {first second : (NP).State} (same : first = second)
      (trace : (NP).Trace first)
      (holds : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal trace) :
      RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal
        (same ▸ trace) := by
    cases same
    exact holds
  have projectedRegular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n)
      focal trace := regularTransport projectedState projected.trace regular
  have nativeState : protocolState (runtime setup) leaks history.state = some nativeCurrent :=
    congrArg (protocolState (runtime setup) leaks) state
  have valid := nativeHistory_record (runtime setup) leaks Initial (initialLaw_initialized setup)
    horizon scheduler ((RMenu).toRawTrace Initial horizon scheduler history.trace) clear
      nativeCurrent nativeState
  let alternativeNative : (N).BehavioralPolicy focal := fun input =>
    (alternative (liftInformation (runtime setup) leaks input)).map
      (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler focal input)
  have rate := nativeComparison_foreign_exit_mass_le_rank setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n focal alternativeNative
    opportunity inclusion timely certificate (fun _ => False) nativeCurrent trace event turn valid
      projectedRegular
  simp only [or_false] at rate
  rw [reconstructed] at rate
  have sameLaw := nativeComparison_stopped_update_eq setup leaks bounds horizon scheduler sequence
    scale positive le_one weights n fallback strategy assembled certificate focal alternativeNative
    (fun final => DecodedState setup leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) final.state) projected
  have sameMass := congrArg
    (fun probability : PMF (NP).History =>
      (probability.toOuterMeasure {final | exits final.state}).toReal) sameLaw
  have rate' := sameMass.symm.trans_le rate
  have projectedUpdate := sourceNativeProfile_update setup leaks bounds horizon scheduler strategy
    focal alternative
  change sourceNativeProfile setup leaks bounds horizon scheduler updated = _ at projectedUpdate
  have updateMass := congrArg
    (fun profile : ∀ who, (N).BehavioralPolicy who =>
      (((N).runBehavioralUntil certificate profile (fun final => stop final.state)
        projected).toOuterMeasure {final | exits final.state}).toReal) projectedUpdate
  have actualRate := updateMass.trans_le rate'
  have rankEq : (application setup leaks).rank horizon (some nativeCurrent) =
      (application setup leaks).rank horizon (protocolState (runtime setup) leaks history.state) :=
    congrArg ((application setup leaks).rank horizon) nativeState.symm
  have boundEq := congrArg (fun rank : Nat => ((scale n) ^ 2 + scale n) * (rank : ℝ)) rankEq
  exact rawMass.trans_le (priorMass'.trans_le (actualRate.trans_eq boundEq))

omit [Fintype Player] in
private theorem nativeClear_iff_stateInvariant
    (history : ((application setup leaks).protocol ((Initial).map RecoveryState.native)
      horizon (NativeScheduler)).History) :
    NativeClear (runtime setup) leaks Initial horizon scheduler history ↔
      ClearState history.state := by
  unfold NativeClear
  cases state : history.state with
  | none => simp [ReactiveApplication.stateInvariant]
  | some current =>
    constructor
    · intro holds
      exact holds current rfl
    · intro valid found equal
      cases Option.some.inj equal
      exact valid


end Vegas.RecoveryOnePacket

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonStopped
import Vegas.Game.RecoveryForeignFailureBound
import Vegas.Game.RecoveryDebtStoppedComparison
import Vegas.Game.RecoveryNativeHistory
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
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu runtime leaks bounds) (initialLaw setup) horizon
  (NativeScheduler)

local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

open Classical in
/-- The raw native continuation induced by the actual recovery
profile inherits the common comparison's foreign first-exit rate. -/
theorem projected_foreign_exit_mass_le_rank [Fintype (RP).History]
    [(recoveryApplication runtime leaks).FiniteNature Initial scheduler]
    [∀ who, DecidableEq ((R).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler
        agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (focal : Player) (alternative : (R).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (certificate : (NP).WellFoundedHistories)
    (rawCertificate : ((application setup runtime leaks).protocol ((Initial).map
      RecoveryState.native)
      horizon (NativeScheduler)).WellFoundedHistories)
    (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (current : (recoveryApplication runtime leaks).Control)
    (state : history.state = some current)
    (event : (graph setup).EventId)
    (turn : current.execution.application.native.publicView.ownTurn? focal = some event)
    (regular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) focal
      (nativeClearHistory setup runtime leaks bounds horizon scheduler history clear).trace) :
    let native := (application setup runtime leaks).information ((Initial).map RecoveryState.native)
      horizon (NativeScheduler)
    let updated := Profile.update (sig := (R).behavioralSignature) strategy focal alternative
    let raw := (RMenu).toRawHistory Initial horizon scheduler history
    let law := native.runBehavioralUntil rawCertificate
      (nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (updated who)))
      (fun final => ¬ ClearState final.state ∨
        DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) final.state)
      (nativeHistory runtime leaks Initial horizon scheduler raw clear)
    (law.toOuterMeasure {final | ¬ ClearState final.state ∧
      focal ∉ nativeFailureOwners runtime leaks final.state}).toReal ≤
        ((scale n) ^ 2 + scale n) * (application setup runtime leaks).rank horizon
          (protocolState runtime leaks history.state) := by
  intro native updated raw law
  let genericInitial := (Initial).map RecoveryState.native
  let genericModel := (NMenu).information genericInitial horizon (NativeScheduler)
  let genericProfile := boundedNativeProfile runtime leaks bounds Initial horizon scheduler
    updated
  let genericStart := (exists_nativeBoundedHistory runtime leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler history clear).choose
  have rawStart : (NMenu).toRawHistory genericInitial horizon (NativeScheduler) genericStart =
      nativeHistory runtime leaks Initial horizon scheduler raw clear :=
    (exists_nativeBoundedHistory runtime leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler history clear).choose_spec
  let genericCertificate : ((NMenu).protocol genericInitial horizon
      (NativeScheduler)).WellFoundedHistories :=
    Eq.mpr (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol initial horizon (NativeScheduler)).WellFoundedHistories)
        (initialLaw_native setup)) certificate
  let stop : (application setup runtime leaks).ProtocolState → Prop := fun final =>
    ¬ ClearState final ∨ DecodedState setup runtime leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) final
  let exits : (application setup runtime leaks).ProtocolState → Prop := fun final =>
    ¬ ClearState final ∧ focal ∉ nativeFailureOwners runtime leaks final
  have rawLaw := (NMenu).runBehavioralUntil_embed genericInitial horizon (NativeScheduler)
    rawCertificate genericCertificate genericProfile (fun final => stop final.state) genericStart
  have profiles :
      (fun who => (NMenu).embedPolicy genericInitial horizon (NativeScheduler) who
        (genericProfile who)) =
      nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (updated who)) := by
    funext who
    exact boundedNativeProfile_embed runtime leaks bounds Initial horizon scheduler
      updated who
  rw [profiles, rawStart] at rawLaw
  have rawMass :
      (law.toOuterMeasure {final | exits final.state}).toReal =
        ((genericModel.runBehavioralUntil genericCertificate genericProfile
          (fun final => stop final.state) genericStart).toOuterMeasure
            {final | exits final.state}).toReal := by
    have measured := congrArg
      (fun probability : PMF (((application setup runtime leaks).protocol genericInitial horizon
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
        sourceNativeProfile setup runtime leaks bounds horizon scheduler updated := by
    funext who input
    exact (sourceNativeProfile_eq_cast setup runtime leaks bounds horizon scheduler updated who
      input).symm
  have replaceProfile := congrArg
    (fun profile : ∀ who, (N).BehavioralPolicy who =>
      (((N).runBehavioralUntil certificate profile (fun final => stop final.state)
        (Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
          ((NMenu).protocol initial horizon (NativeScheduler)).History)
            (initialLaw_native setup)) genericStart)).toOuterMeasure
              {final | exits final.state}).toReal) profileCast
  have priorMass' := priorMass.trans replaceProfile
  let projected := nativeClearHistory setup runtime leaks bounds horizon scheduler history clear
  let nativeCurrent := RecoveryProjection.control runtime leaks current
  have projectedState : projected.state = some nativeCurrent :=
    (nativeClearHistory_state setup runtime leaks bounds horizon scheduler history clear).trans
      (congrArg (protocolState runtime leaks) state)
  let trace : (NP).Trace (some nativeCurrent) := projectedState ▸ projected.trace
  have reconstructed : (⟨some nativeCurrent, trace⟩ : (NP).History) = projected :=
    history_restate projected projectedState
  have regularTransport {first second : (NP).State} (same : first = second)
      (trace : (NP).Trace first)
      (holds : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
        focal trace) :
      RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) focal
        (same ▸ trace) := by
    cases same
    exact holds
  have projectedRegular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler)
    (sequence n)
      focal trace := regularTransport projectedState projected.trace regular
  have nativeState : protocolState runtime leaks history.state = some nativeCurrent :=
    congrArg (protocolState runtime leaks) state
  have valid := nativeHistory_record runtime leaks Initial (initialLaw_initialized setup)
    horizon scheduler ((RMenu).toRawTrace Initial horizon scheduler history.trace) clear
      nativeCurrent nativeState
  let alternativeNative : (N).BehavioralPolicy focal := fun input =>
    (alternative (liftInformation runtime leaks input)).map
      (sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler focal input)
  have rate := nativeComparison_foreign_exit_mass_le_rank setup runtime leaks bounds horizon
    scheduler
    wellFormed covers capacity sequence scale positive le_one weights n focal alternativeNative
    opportunity inclusion timely certificate (fun _ => False) nativeCurrent trace event turn valid
      projectedRegular
  simp only [or_false] at rate
  rw [reconstructed] at rate
  have sameLaw := nativeComparison_stopped_update_eq setup runtime leaks bounds horizon scheduler
    sequence
    scale positive le_one weights n fallback strategy assembled certificate focal alternativeNative
    (fun final => DecodedState setup runtime leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) final.state) projected
  have sameMass := congrArg
    (fun probability : PMF (NP).History =>
      (probability.toOuterMeasure {final | exits final.state}).toReal) sameLaw
  have rate' := sameMass.symm.trans_le rate
  have projectedUpdate := sourceNativeProfile_update setup runtime leaks bounds horizon scheduler
    strategy
    focal alternative
  change sourceNativeProfile setup runtime leaks bounds horizon scheduler updated = _
    at projectedUpdate
  have updateMass := congrArg
    (fun profile : ∀ who, (N).BehavioralPolicy who =>
      (((N).runBehavioralUntil certificate profile (fun final => stop final.state)
        projected).toOuterMeasure {final | exits final.state}).toReal) projectedUpdate
  have actualRate := updateMass.trans_le rate'
  have rankEq : (application setup runtime leaks).rank horizon (some nativeCurrent) =
      (application setup runtime leaks).rank horizon (protocolState runtime leaks history.state) :=
    congrArg ((application setup runtime leaks).rank horizon) nativeState.symm
  have boundEq := congrArg (fun rank : Nat => ((scale n) ^ 2 + scale n) * (rank : ℝ)) rankEq
  exact rawMass.trans_le (priorMass'.trans_le (actualRate.trans_eq boundEq))

omit [Fintype Player] in
private theorem nativeClear_iff_stateInvariant
    (history : ((application setup runtime leaks).protocol ((Initial).map RecoveryState.native)
      horizon (NativeScheduler)).History) :
    NativeClear runtime leaks Initial horizon scheduler history ↔
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

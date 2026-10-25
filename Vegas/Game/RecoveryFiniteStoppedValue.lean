/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryValueTransport

/-! # The finite-menu value of the actual native debt-stopped projection -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

private theorem expect_stateUntil_prior_eq {Player : Type} [DecidableEq Player] [Fintype Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler)
    (firstCertificate : (menu.protocol first horizon scheduler).WellFoundedHistories)
    (secondCertificate : (menu.protocol second horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information first horizon scheduler).BehavioralPolicy who)
    (stop : app.ProtocolState → Prop) (payoff : app.ProtocolState → ℝ)
    (history : (menu.protocol first horizon scheduler).History) :
    expect ((menu.information first horizon scheduler).runBehavioralUntil firstCertificate profile
      (fun next => stop next.state) history) (fun next => payoff next.state) =
      expect ((menu.information second horizon scheduler).runBehavioralUntil secondCertificate
        (fun who input => (profile who input).map (Equiv.cast (congrArg
          (fun initial => (menu.information initial horizon scheduler).Choice who input) same)))
        (fun next => stop next.state)
        (Equiv.cast (congrArg (fun initial => (menu.protocol initial horizon scheduler).History)
          same) history)) (fun next => payoff next.state) := by
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
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

open Classical in
/-- The concrete raw classified projection has exactly its finite-menu stopped
payoff, including first public failures and focal latent debt. -/
theorem nativeDebtStoppedValue_eq_finite_continuation
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player) (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) final.state
    nativeDebtStoppedValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        rawCertificate profile focal history =
      expect ((N).runBehavioralUntil certificate
        (sourceNativeProfile setup leaks bounds horizon scheduler profile) stopped
        (nativeClearHistory setup leaks bounds horizon scheduler history clear))
        (fun final => if stopped final then excludedPayoff focal else
          exclusionBase setup parameter utility excludedPayoff leaks final.state focal) := by
  intro stopped
  let genericInitial := (Initial).map RecoveryState.native
  let genericModel := (NMenu).information genericInitial horizon (NativeScheduler)
  let genericProfile := boundedNativeProfile (runtime setup) leaks bounds Initial horizon scheduler
    profile
  let genericStart := (exists_nativeBoundedHistory (runtime setup) leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler history clear).choose
  have rawStart := (exists_nativeBoundedHistory (runtime setup) leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler history clear).choose_spec
  let genericCertificate : ((NMenu).protocol genericInitial horizon
      (NativeScheduler)).WellFoundedHistories :=
    Eq.mpr (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol initial horizon (NativeScheduler)).WellFoundedHistories)
        (initialLaw_native setup)) certificate
  let stop : (application setup leaks).ProtocolState → Prop := fun state => ¬ Clear state ∨
    DecodedState setup leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) state
  let payoff : (application setup leaks).ProtocolState → ℝ := fun state =>
    if stop state then excludedPayoff focal else
      exclusionBase setup parameter utility excludedPayoff leaks state focal
  have clearIff (final : (RawNative).History) :
      NativeClear (runtime setup) leaks Initial horizon scheduler final ↔ Clear final.state := by
    unfold NativeClear
    cases state : final.state with
    | none => simp [ReactiveApplication.stateInvariant]
    | some current =>
        constructor
        · intro holds
          exact holds current rfl
        · intro holds found same
          cases Option.some.inj same
          exact holds
  have stopEq : (fun final : (RawNative).History =>
      ¬ NativeClear (runtime setup) leaks Initial horizon scheduler final ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) final.state) =
      (fun final => stop final.state) := by
    funext final
    exact propext (or_congr (not_congr (clearIff final)) Iff.rfl)
  have readEq (final : (RawNative).History) :
      Sum.elim (fun _ : Finset Player => excludedPayoff focal)
        (fun ending : (RawNative).History =>
          if DecodedState setup leaks (failureProfile setup.program)
              (ProtocolState.OwesFailure focal setup.program) ending.state then excludedPayoff focal
          else exclusionBase setup parameter utility excludedPayoff leaks ending.state focal)
        (nativeClassifiedReadout (runtime setup) leaks Initial horizon scheduler final) =
          payoff final.state := by
    by_cases clearFinal : NativeClear (runtime setup) leaks Initial horizon scheduler final
    · have valid := (clearIff final).mp clearFinal
      simp only [nativeClassifiedReadout, ite_eq_left clearFinal, Sum.elim_inr, payoff, stop,
        not_true_eq_false, valid, false_or]
    · have invalid : ¬ Clear final.state := fun valid => clearFinal ((clearIff final).mpr valid)
      simp only [nativeClassifiedReadout, ite_eq_right clearFinal, Sum.elim_inl, payoff, stop,
        invalid, not_false_eq_true, true_or, ite_true]
  unfold nativeDebtStoppedValue nativeDebtStoppedLaw
  rw [dite_eq_left clear, expect_map, stopEq]
  conv_lhs =>
    arg 2
    intro final
    rw [Function.comp_apply]
    rw [readEq final]
  have rawLaw := (NMenu).runBehavioralUntil_embed genericInitial horizon (NativeScheduler)
    rawCertificate genericCertificate genericProfile (fun final => stop final.state) genericStart
  have profiles : (fun who => (NMenu).embedPolicy genericInitial horizon (NativeScheduler) who
      (genericProfile who)) =
      nativeProfile (runtime setup) leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)) := by
    funext who
    exact boundedNativeProfile_embed (runtime setup) leaks bounds Initial horizon scheduler
      profile who
  rw [profiles, rawStart] at rawLaw
  have rawValue := congrArg (fun law : PMF (RawNative).History =>
    expect law (fun final => payoff final.state)) rawLaw
  rw [expect_map] at rawValue
  rw [← rawValue]
  have prior := expect_stateUntil_prior_eq (NMenu) (initialLaw_native setup) horizon
    (NativeScheduler) genericCertificate certificate genericProfile stop payoff genericStart
  have profileCast : (fun who input => (genericProfile who input).map (Equiv.cast (congrArg
      (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((NMenu).information initial horizon (NativeScheduler)).Choice who input)
          (initialLaw_native setup)))) =
      sourceNativeProfile setup leaks bounds horizon scheduler profile := by
    funext who input
    exact (sourceNativeProfile_eq_cast setup leaks bounds horizon scheduler profile who input).symm
  have replaceProfile := congrArg (fun policies : ∀ who, (N).BehavioralPolicy who =>
    expect ((N).runBehavioralUntil certificate policies (fun next => stop next.state)
      (Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((NMenu).protocol initial horizon (NativeScheduler)).History)
          (initialLaw_native setup)) genericStart)) (fun next => payoff next.state)) profileCast
  exact prior.trans replaceProfile

end Vegas.RecoveryOnePacket

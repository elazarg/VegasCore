/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryFiniteStoppedValue
import GameTheory.Protocol.PolicyRandomization

/-! # Exact same-witness stopped values after local recovery deviations -/

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
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup runtime leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

/-- Projecting one replaced recovery decision law replaces exactly the
corresponding complete native information value. -/
theorem sourceNativeProfile_update_withLaw
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player)
    (input : (application setup runtime leaks).Info)
    (law : PMF ((R).Choice focal (liftInformation runtime leaks input))) :
    sourceNativeProfile setup runtime leaks bounds horizon scheduler
      (Profile.update (sig := (R).behavioralSignature) profile focal
        ((profile focal).withLaw (liftInformation runtime leaks input) law)) =
      Profile.update (sig := (N).behavioralSignature)
        (sourceNativeProfile setup runtime leaks bounds horizon scheduler profile) focal
        ((sourceNativeProfile setup runtime leaks bounds horizon scheduler profile focal).withLaw
          input
          (law.map
            (sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler focal input)))
              := by
  funext who other
  by_cases playerEq : who = focal
  · subst who
    by_cases inputEq : other = input
    · subst other
      simp only [sourceNativeProfile, Profile.update_same, BehavioralPolicy.withLaw_self]
    · have liftedNe : liftInformation runtime leaks other ≠
          liftInformation runtime leaks input := fun equal => inputEq (by
        have projected := congrArg (RecoveryProjection.information runtime leaks) equal
        simpa only [information_liftInformation] using projected)
      simp only [sourceNativeProfile, Profile.update_same,
        BehavioralPolicy.withLaw_of_ne (M := R) (profile focal)
          (liftInformation runtime leaks input) law liftedNe,
        BehavioralPolicy.withLaw_of_ne _ _ _ inputEq]
  · simp only [sourceNativeProfile, Profile.update_of_ne _ _ playerEq]

private theorem stopped_eq_of_clear_laws
    (certificate : (NP).WellFoundedHistories)
    (first second : ∀ who, (N).BehavioralPolicy who) (extraStop : (NP).History → Prop)
    (agree : ∀ history : (NP).History, Clear history.state → ¬ (NP).terminal history.state →
      ∀ who, first who ((N).infoOf who history.trace) =
        second who ((N).infoOf who history.trace)) (start : (NP).History) :
    (N).runBehavioralUntil certificate first
        (fun history => ¬ Clear history.state ∨ extraStop history) start =
      (N).runBehavioralUntil certificate second
        (fun history => ¬ Clear history.state ∨ extraStop history) start := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  by_cases halted : ¬ Clear history.state ∨ extraStop history
  · rw [(N).runBehavioralUntil_of_stopped certificate first halted,
      (N).runBehavioralUntil_of_stopped certificate second halted]
  by_cases terminal : (NP).terminal history.state
  · rw [(N).runBehavioralUntil_of_terminal certificate first terminal,
      (N).runBehavioralUntil_of_terminal certificate second terminal]
  have clear : Clear history.state := not_not.mp (fun denied => halted (Or.inl denied))
  have stepEq : (N).runBehavioralFrom first 1 history =
      (N).runBehavioralFrom second 1 history := by
    rw [(N).runBehavioralFrom_succ_of_not_terminal first 0 terminal,
      (N).runBehavioralFrom_succ_of_not_terminal second 0 terminal,
      (N).behavioralJoint_congr history.trace terminal (agree history clear terminal)]
    rfl
  rw [(N).runBehavioralUntil_of_running certificate first halted terminal,
    (N).runBehavioralUntil_of_running certificate second halted terminal, stepEq]
  apply bind_congr_on_support
  intro next member
  exact ih next ((N).mem_support_runBehavioralFrom_one second terminal member).1

/-- The baseline and every local deviation use exactly the same native stopped
law as their actual recovery projection, until exclusion or an additional stop. -/
theorem nativeComparison_stopped_localLaw_eq [Fintype (RP).History]
  [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
  [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
  (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
  (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
  {slots : Nat}
  (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
  (n : ℕ) (fallback : ∀ who, (R).Policy who) (strategy : ∀ who, (R).BehavioralPolicy who)
  (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
    (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
      (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
        (positive n).le (le_one n) agent)))
    (certificate : (NP).WellFoundedHistories) (focal : Player)
    (input : (application setup runtime leaks).Info) (law : PMF ((N).Choice focal input))
    (extraStop : (NP).History → Prop) (start : (NP).History) :
    (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature)
          (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
            positive
            le_one weights n) focal
          ((nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
            positive
            le_one weights n focal).withLaw input law))
        (fun history => ¬ Clear history.state ∨ extraStop history) start =
      (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature)
          (sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy) focal
          ((sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy focal).withLaw
            input law))
        (fun history => ¬ Clear history.state ∨ extraStop history) start := by
  apply stopped_eq_of_clear_laws
  intro history clear running who
  have valid : ∀ control, history.state = some control →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) := by
    intro control state
    rw [state] at clear
    exact clear
  have same := nativeComparisonStrategy_eq_projection_at_clear setup runtime leaks bounds horizon
    scheduler
    sequence scale positive le_one weights n fallback strategy assembled history.trace valid
      running who
  by_cases playerEq : who = focal
  · subst who
    rw [Profile.update_same, Profile.update_same]
    by_cases inputEq : (N).infoOf focal history.trace = input
    · rw [inputEq, BehavioralPolicy.withLaw_self, BehavioralPolicy.withLaw_self]
    · rw [BehavioralPolicy.withLaw_of_ne _ _ _ inputEq,
        BehavioralPolicy.withLaw_of_ne _ _ _ inputEq]
      exact same
  · rw [Profile.update_of_ne _ _ playerEq, Profile.update_of_ne _ _ playerEq]
    exact same

open Classical in
/-- The raw surrogate of a genuine local recovery deviation is the finite
same-witness native comparison value, with its full local law preserved. -/
theorem nativeDebtStoppedValue_localLaw_eq_comparison [Fintype (RP).History]
  [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
  [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
  (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
  (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
  {slots : Nat}
  (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
  (n : ℕ) (fallback : ∀ who, (R).Policy who) (strategy : ∀ who, (R).BehavioralPolicy who)
  (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
    (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
      (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
        (positive n).le (le_one n) agent)))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories) (focal : Player)
    (input : (application setup runtime leaks).Info)
    (law : PMF ((R).Choice focal (liftInformation runtime leaks input)))
    (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) final.state
    nativeDebtStoppedValue setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff
        rawCertificate (Profile.update (sig := (R).behavioralSignature) strategy focal
          ((strategy focal).withLaw (liftInformation runtime leaks input) law)) focal
        history =
      expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature)
          (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
            positive
            le_one weights n) focal
          ((nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
            positive
            le_one weights n focal).withLaw input
            (law.map (sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler focal
              input))))
        stopped (nativeClearHistory setup runtime leaks bounds horizon scheduler history clear))
        (fun final => if stopped final then excludedPayoff focal else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state focal) :=
            by
  intro stopped
  rw [nativeDebtStoppedValue_eq_finite_continuation setup runtime leaks bounds horizon
    scheduler parameter
    utility excludedPayoff rawCertificate certificate _ focal history clear,
    sourceNativeProfile_update_withLaw ]
  rw [nativeComparison_stopped_localLaw_eq setup runtime leaks bounds horizon scheduler sequence
    scale
    positive le_one weights n fallback strategy assembled certificate focal input _
    (fun final => DecodedState setup runtime leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) final.state)]



end Vegas.RecoveryOnePacket

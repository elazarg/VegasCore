/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonBelief
import Vegas.Pending.ExclusionBoundedInformationHistory

/-! # Finite comparison-history laws of actual recovery beliefs

The complete clear-fiber projection takes values in genuine bounded native
histories. Its law is exactly the same-weight native comparison belief.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
  Interaction

private theorem informationHistory_cast_raw
    {Player : Type} [DecidableEq Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Player) (input : app.Info)
    (history : (menu.information first horizon scheduler).InformationHistory who input) :
    menu.toRawHistory second horizon scheduler
        ((Equiv.cast (congrArg (fun initial =>
          (menu.information initial horizon scheduler).InformationHistory who input) same))
          history).1 =
      Equiv.cast (congrArg (fun initial => (app.protocol initial horizon scheduler).History) same)
        (menu.toRawHistory first horizon scheduler history.1) := by
  subst second
  rfl

private theorem informationHistory_cast_state
    {Player : Type} [DecidableEq Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Player) (input : app.Info)
    (history : (menu.information first horizon scheduler).InformationHistory who input) :
    ((Equiv.cast (congrArg (fun initial =>
      (menu.information initial horizon scheduler).InformationHistory who input) same))
        history).1.state = history.1.state := by
  subst second
  rfl

open SourceProgram GameTheory.Protocol.InformationModel EventGraphRuntime RecoveryProjection

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
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

variable (who : Player) (reference : (application setup leaks).Control)
  (active : reference.actor = some who)
  (valid : ExclusionEvidence 0 ∅ (RecoveryState.mk reference.execution.application ∅))
  (nativeDecision : (onePacketModel setup leaks bounds (initialLaw setup) horizon
    (nativeScheduler (runtime setup) leaks scheduler)).IsDecisionInfo who
      ((application setup leaks).observe who (some reference)))
  (recoveryDecision : (model setup leaks bounds
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).IsDecisionInfo who
        (liftInformation (runtime setup) leaks
          ((application setup leaks).observe who (some reference))))

local notation "Input" => ReactiveApplication.observe (application setup leaks) who (some reference)
local notation "NSite" => Subtype.mk (p := InformationModel.IsDecisionInfo (N) who) (Input)
  nativeDecision
local notation "RSite" => Subtype.mk (p := InformationModel.IsDecisionInfo (R) who)
  (liftInformation (runtime setup) leaks (Input)) recoveryDecision

/-- An entire actual clear recovery information history projects to an actual
finite native history at the canonical compiled initial law. -/
def comparisonInformationHistory
    (history : (R).InformationHistory who RSite.1) :
    (N).InformationHistory who NSite.1 :=
  Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).information initial horizon (NativeScheduler)).InformationHistory who (Input))
        (initialLaw_native setup))
    (boundedInformationHistory (runtime setup) leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler who reference active valid
      (Eq.mpr (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((NMenu).information initial horizon (NativeScheduler)).IsDecisionInfo who (Input))
          (initialLaw_native setup)) nativeDecision) recoveryDecision history)


/-- Finite projection retains every realized predecessor and projected action
of the existing complete raw-history projection. -/
theorem comparisonInformationHistory_raw
    (history : (R).InformationHistory who RSite.1) :
    (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler)
        (comparisonInformationHistory setup leaks bounds horizon scheduler who reference active
          valid nativeDecision recoveryDecision history).1 =
      Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
          (initialLaw_native setup))
        (informationHistoryEquiv (runtime setup) leaks Initial (initialLaw_initialized setup)
          horizon scheduler who reference active valid
          ((RMenu).rawInformationHistory Initial horizon scheduler who RSite history)).1 := by
  unfold comparisonInformationHistory
  rw [informationHistory_cast_raw (NMenu) (initialLaw_native setup) horizon (NativeScheduler) who
    (Input), boundedInformationHistory_raw]

/-- Projection retains the complete native state, not just its public record. -/
theorem comparisonInformationHistory_state
    (history : (R).InformationHistory who RSite.1) :
    (comparisonInformationHistory setup leaks bounds horizon scheduler who reference active valid
      nativeDecision recoveryDecision history).1.state =
        protocolState (runtime setup) leaks history.1.state := by
  unfold comparisonInformationHistory
  exact (informationHistory_cast_state (NMenu) (initialLaw_native setup) horizon (NativeScheduler)
    who (Input) _).trans (boundedInformationHistory_state (runtime setup) leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler who reference active valid _ recoveryDecision
        history)

/-- Complete finite recovery beliefs have exactly the same projected law as
the native comparison assessment using the unchanged completion weights. -/
theorem recovery_belief_eq_comparisonInformationHistory [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ player, DecidableEq ((R).InfoState player)]
    [∀ player, DecidableEq ((N).InfoState player)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ player, (R).Policy player)
    (assessment : (R).BehavioralAssessment)
    (assembled : assessment.strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : BehavioralAssessment.IsBayesConsistent (R) assessment
      ((RMenu).decisionInformationAntichain Initial horizon scheduler)) :
    (assessment.belief who RSite).map
      (comparisonInformationHistory setup leaks bounds horizon scheduler who reference active valid
        nativeDecision recoveryDecision) =
      (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n).belief who NSite := by
  let embed := fun history : (N).InformationHistory who NSite.1 =>
    (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) history.1
  have injective : Function.Injective embed := by
    intro first second equal
    exact Subtype.ext ((NMenu).toRawHistory_injective (initialLaw setup) horizon (NativeScheduler)
      equal)
  apply pmf_map_injective injective
  rw [PMF.map_comp]
  have composed : embed ∘
      comparisonInformationHistory setup leaks bounds horizon scheduler who reference active valid
        nativeDecision recoveryDecision = fun history =>
      Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
          (initialLaw_native setup))
        (informationHistoryEquiv (runtime setup) leaks Initial (initialLaw_initialized setup)
          horizon scheduler who reference active valid
          ((RMenu).rawInformationHistory Initial horizon scheduler who RSite history)).1 := by
    funext history
    change (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) _ = _
    rw [comparisonInformationHistory,
      informationHistory_cast_raw (NMenu) (initialLaw_native setup) horizon (NativeScheduler) who
        (Input), boundedInformationHistory_raw]
  rw [composed]
  exact recovery_belief_eq_nativeComparison setup leaks bounds horizon scheduler sequence scale
    positive le_one weights n fallback assessment assembled bayes who reference active valid
      nativeDecision recoveryDecision

end Vegas.RecoveryOnePacket

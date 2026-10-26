/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeClearReach

/-! # Clear-fiber Bayes laws of the native comparison

Every history in a publicly clear full-information fiber is clear. Exact trace
weights therefore identify the information mass and its normalized posterior.
-/

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
local notation "NMenu" => bounds.onePacketMenu runtime leaks

/-- Every actual native history at a clear full-information site has a clear
public completion record, including histories with zero behavioral mass. -/
theorem nativeInformationFiber_record (who : Player)
    (reference : (application setup runtime leaks).Control) (active : reference.actor = some who)
    (valid : ExclusionEvidence 0 ∅ (RecoveryState.mk reference.execution.application ∅))
    (site : (N).InformationSite who)
    (seen : site.1 = (application setup runtime leaks).observe who (some reference))
    (history : (N).InformationHistory who site.1) :
    ∀ current, history.1.state = some current →
      ExclusionEvidence 0 ∅ (RecoveryState.mk current.execution.application ∅) := by
  let genericPrior : ((NMenu).protocol ((Initial).map RecoveryState.native) horizon
      (NativeScheduler)).Trace history.1.state :=
    Eq.mpr (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol law horizon (NativeScheduler)).Trace history.1.state)
      (initialLaw_native setup)) history.1.trace
  have observed : (application setup runtime leaks).observe who history.1.state =
      (application setup runtime leaks).observe who (some reference) :=
    ((NMenu).info (initialLaw setup) horizon (NativeScheduler) who history.1.trace).symm.trans
      (history.2.trans seen)
  exact informationFiber_record runtime leaks Initial (initialLaw_initialized setup) horizon
    scheduler who reference active valid
    ((NMenu).toRawHistory ((Initial).map RecoveryState.native) horizon (NativeScheduler)
      ⟨history.1.state, genericPrior⟩) observed

/-- The original comparison and actual recovery completion have exactly the
same native information-event mass at a complete clear site. -/
theorem informationMass_nativeComparison_of_clear [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
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
    (who : Player) (reference : (application setup runtime leaks).Control)
    (active : reference.actor = some who)
    (valid : ExclusionEvidence 0 ∅ (RecoveryState.mk reference.execution.application ∅))
    (site : (N).InformationSite who)
    (seen : site.1 = (application setup runtime leaks).observe who (some reference)) :
    (N).informationMass (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
      sequence
      scale positive le_one weights n) who site =
      (N).informationMass (sourceNativeProfile setup runtime leaks bounds horizon scheduler
        strategy)
        who site := by
  unfold InformationModel.informationMass
  apply tsum_congr
  intro history
  exact historyReachWeight_nativeComparison_of_clear setup runtime leaks bounds horizon scheduler
    sequence
    scale positive le_one weights n fallback strategy assembled history.1.trace
    (nativeInformationFiber_record setup runtime leaks bounds horizon scheduler who reference
      active valid
      site seen history)

/-- The actual comparison assessment normalizes precisely the projected
recovery trace weights at every complete clear native site. -/
theorem nativeComparison_bayes_formula_of_clear [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
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
    (who : Player) (reference : (application setup runtime leaks).Control)
    (active : reference.actor = some who)
    (valid : ExclusionEvidence 0 ∅ (RecoveryState.mk reference.execution.application ∅))
    (site : (N).InformationSite who)
    (seen : site.1 = (application setup runtime leaks).observe who (some reference))
    (history : (N).InformationHistory who site.1) :
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n).belief who site history =
      (N).historyReachWeight (sourceNativeProfile setup runtime leaks bounds horizon scheduler
        strategy)
          history.1 /
        (N).informationMass (sourceNativeProfile setup runtime leaks bounds horizon scheduler
          strategy)
          who site := by
  have posterior := (nativeComparisonSequence_bayes setup runtime leaks bounds horizon scheduler
    sequence
    scale positive le_one weights n) who site
      ((N).informationMass_pos_of_fullSupport _ (nativeComparisonStrategy_fullSupport setup
        runtime leaks
        bounds horizon scheduler sequence scale positive le_one weights n) who site) history
  change (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
    positive
    le_one weights n).belief who site history =
      (N).historyReachWeight (nativeComparisonStrategy setup runtime leaks bounds horizon
        scheduler sequence
        scale positive le_one weights n) history.1 /
        (N).informationMass (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
          sequence
          scale positive le_one weights n) who site at posterior
  rw [historyReachWeight_nativeComparison_of_clear setup runtime leaks bounds horizon scheduler
    sequence
    scale positive le_one weights n fallback strategy assembled history.1.trace
      (nativeInformationFiber_record setup runtime leaks bounds horizon scheduler who reference
        active valid
        site seen history),
    informationMass_nativeComparison_of_clear setup runtime leaks bounds horizon scheduler
      sequence scale
      positive le_one weights n fallback strategy assembled who reference active valid site seen]
    at posterior
  exact posterior

end Vegas.RecoveryOnePacket

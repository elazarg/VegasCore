/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativeMixture

/-! # Native comparison strategies on actual clear inputs

The completed recovery strategy and its same-weight native comparison induce
the same concrete packet laws at represented clear decision inputs.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

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

/-- The same assembled recovery weights induce exactly the native comparison
action law at every represented clear site. -/
theorem nativeComparisonStrategy_at_clear [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
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
    {who : Player} (site : (N).InformationSite who)
    (decision : (R).IsDecisionInfo who (liftInformation (runtime setup) leaks site.1)) :
    (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive le_one
      weights n who site.1).map Subtype.val =
      (strategy who (liftInformation (runtime setup) leaks site.1)).map
        (fun choice => choice.1.map (action (runtime setup) leaks)) := by
  rw [nativeComparisonStrategy, (N).agentBehavior_at (N).playedInformation
    (onePacketFallback setup leaks bounds horizon (NativeScheduler)) _ ((N).agentAt site)]
  rw [assembled, (R).agentBehavior_at (R).playedInformation fallback _
    ((R).agentAt ⟨liftInformation (runtime setup) leaks site.1, decision⟩)]
  exact nativeComparisonMixture_at_clear setup leaks bounds horizon scheduler (sequence n)
    (scale n) (positive n).le (le_one n) (weights n) site decision

/-- The canonical finite native projection of an arbitrary recovery strategy. -/
def sourceNativeProfile (strategy : ∀ who, (R).BehavioralPolicy who) :
    ∀ who, (N).BehavioralPolicy who := fun who input =>
  (strategy who (liftInformation (runtime setup) leaks input)).map
    (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input)

/-- Canonical projection preserves the actual optional native packet law. -/
theorem sourceNativeProfile_map_val (strategy : ∀ who, (R).BehavioralPolicy who)
    (who : Player) (input : (application setup leaks).Info) :
    (sourceNativeProfile setup leaks bounds horizon scheduler strategy who input).map Subtype.val =
      (strategy who (liftInformation (runtime setup) leaks input)).map
        (fun choice => choice.1.map (action (runtime setup) leaks)) :=
  sourceNativeChoiceEquiv_map_val setup leaks bounds horizon scheduler who input _

end Vegas.RecoveryOnePacket

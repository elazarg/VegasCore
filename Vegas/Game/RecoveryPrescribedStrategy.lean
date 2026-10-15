/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPrescribedMixture

/-! # Prescribed laws of assembled recovery profiles

The actual free/keyed completion assembly retains the prescribed law at every
forced nonlate decision, independently of its pool weights.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (RecoveryState (graph setup)))
  (horizon : Nat) (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "R" => model setup leaks bounds initial horizon scheduler
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) initial horizon scheduler

/-- The assembled recovery strategy has the prescribed projected law at a
forced nonlate site. -/
theorem assembledStrategy_projected_of_forced_nonlate [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds initial horizon scheduler slots p))
    (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights (pool setup leaks bounds initial horizon scheduler agent)).bind
        (component setup leaks bounds initial horizon scheduler assessment scale nonnegative
          le_one agent)))
    {who : Player} (site : (R).InformationSite who)
    (forced : ForcedAgent setup leaks bounds initial horizon scheduler ((R).agentAt site))
    (nonlate : ¬ KeyedAgent setup leaks bounds initial horizon scheduler ((R).agentAt site)) :
    (strategy who site.1).map
        (boundedRecoveryChoiceEquiv (runtime setup) leaks bounds initial horizon scheduler who
          site.1 forced.1).symm =
      slotPrescribedComponent setup leaks bounds (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) assessment scale nonnegative le_one who
        (RecoveryProjection.information (runtime setup) leaks site.1) := by
  rw [assembled, (R).agentBehavior_at (R).playedInformation fallback _ ((R).agentAt site)]
  exact component_mixture_projected_of_forced_nonlate setup leaks bounds initial horizon scheduler
    assessment scale nonnegative le_one ((R).agentAt site) forced nonlate
    (weights (pool setup leaks bounds initial horizon scheduler ((R).agentAt site)))

end Vegas.RecoveryOnePacket

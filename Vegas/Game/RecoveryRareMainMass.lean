/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPrescribedMixture
import Vegas.Game.OnePacketRareMainMass

/-! # Rare foreign responses under the actual recovery component law -/

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
local notation "N" => onePacketModel setup leaks bounds (initial.map RecoveryState.native) horizon
  (nativeScheduler (runtime setup) leaks scheduler)

/-- At a forced nonlate recovery site, every projected response event disjoint
from source-main support has total probability at most square plus scale under
any common mixture of the actual components. -/
theorem component_mixture_event_le_of_disjoint_main [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (R).InformationAgent (R).playedInformation)
    (forced : ForcedAgent setup leaks bounds initial horizon scheduler agent)
    (nonlate : ¬ KeyedAgent setup leaks bounds initial horizon scheduler agent)
    (weights : PMF (Part setup leaks bounds initial horizon scheduler slots
      (pool setup leaks bounds initial horizon scheduler agent)))
    (event : Set ((N).Choice agent.1
      (RecoveryProjection.information (runtime setup) leaks agent.2.1)))
    (disjoint : Disjoint
      (honestChoice setup leaks bounds (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) assessment agent.1
        (RecoveryProjection.information (runtime setup) leaks agent.2.1)).support event) :
    ((weights.bind (component setup leaks bounds initial horizon scheduler assessment scale
      nonnegative le_one agent)).toOuterMeasure
        ((boundedRecoveryChoiceEquiv (runtime setup) leaks bounds initial horizon scheduler agent.1
          agent.2.1 forced.1).symm ⁻¹' event)).toReal ≤ scale ^ 2 + scale := by
  have projected := component_mixture_projected_of_forced_nonlate setup leaks bounds initial horizon
    scheduler assessment scale nonnegative le_one agent forced nonlate weights
  have transported := congrArg (fun law => (law.toOuterMeasure event).toReal) projected
  rw [PMF.toOuterMeasure_map_apply] at transported
  rw [transported]
  exact slotTrembledChoice_event_le_of_disjoint_main setup leaks bounds
    (initial.map RecoveryState.native) horizon (nativeScheduler (runtime setup) leaks scheduler)
    nonnegative le_one agent.1 (RecoveryProjection.information (runtime setup) leaks agent.2.1)
    _ _ _ event disjoint

end Vegas.RecoveryOnePacket

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryOnePacketComponents
import Vegas.Pending.ExclusionUniformLaw

/-! # Recovery component laws at clear inputs

The same source assessment, tremble scale, and late option define the native
and recovery operational laws. Their choice relabeling also preserves the free
uniform tremble, so singleton weights can be transported without a new witness.
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

local notation "RModel" => model setup leaks bounds initial horizon scheduler
local notation "RProtocol" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) initial horizon scheduler
local notation "NMenu" => MessageBounds.onePacketMenu (runtime setup) leaks bounds

/-- A prescribed recovery component projects to the same prescribed native
component at the projected input. -/
theorem prescribedComponent_projected [Fintype (RProtocol).History]
    [∀ who, DecidableEq ((RModel).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (RModel).InformationAgent (RModel).playedInformation)
    (clear : ClearInput (runtime setup) leaks agent.2.1) :
    (prescribedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
      le_one agent).map
        (boundedRecoveryChoiceEquiv (runtime setup) leaks bounds initial horizon scheduler agent.1
          agent.2.1 clear).symm =
      slotPrescribedComponent setup leaks bounds (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) assessment scale nonnegative le_one
        agent.1 (RecoveryProjection.information (runtime setup) leaks agent.2.1) := by
  exact boundedRecoveryLaw_projected (runtime setup) leaks bounds initial horizon scheduler
    agent.1 agent.2.1 clear _

/-- A keyed recovery component projects to the native component with the same
source assessment and late option. -/
theorem keyedComponent_projected [Fintype (RProtocol).History]
    [∀ who, DecidableEq ((RModel).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (RModel).InformationAgent (RModel).playedInformation)
    (clear : ClearInput (runtime setup) leaks agent.2.1) (option : LateOption slots) :
    (keyedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
      le_one agent option).map
        (boundedRecoveryChoiceEquiv (runtime setup) leaks bounds initial horizon scheduler agent.1
          agent.2.1 clear).symm =
      lateComponent setup leaks bounds (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) assessment scale nonnegative le_one
        agent.1 (RecoveryProjection.information (runtime setup) leaks agent.2.1) option := by
  exact boundedRecoveryLaw_projected (runtime setup) leaks bounds initial horizon scheduler
    agent.1 agent.2.1 clear _

/-- The free recovery component projects to the native uniform tremble of the
corresponding individual choice. -/
theorem freeLaw_projected [Fintype (RProtocol).History]
    [∀ who, DecidableEq ((RModel).InfoState who)]
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (RModel).InformationAgent (RModel).playedInformation)
    (clear : ClearInput (runtime setup) leaks agent.2.1)
    (choice : (RModel).Choice agent.1 agent.2.1) :
    (freeLaw setup leaks bounds initial horizon scheduler scale nonnegative le_one agent choice).map
        (boundedRecoveryChoiceEquiv (runtime setup) leaks bounds initial horizon scheduler agent.1
          agent.2.1 clear).symm =
      mix scale nonnegative le_one
        ((NMenu).uniformPolicy (initial.map RecoveryState.native) horizon
          (nativeScheduler (runtime setup) leaks scheduler) agent.1
            (RecoveryProjection.information (runtime setup) leaks agent.2.1))
        (PMF.pure ((boundedRecoveryChoiceEquiv (runtime setup) leaks bounds initial horizon
          scheduler agent.1 agent.2.1 clear).symm choice)) := by
  rw [freeLaw, mix_map, PMF.pure_map, uniformPolicy_projected]

end Vegas.RecoveryOnePacket

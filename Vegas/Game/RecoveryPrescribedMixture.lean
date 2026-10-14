/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryComponentProjection

/-! # Prescribed mixtures at forced nonlate recovery decisions

All parts induce the same prescribed law at a forced decision outside the
late-delivery region. Therefore arbitrary completion weights preserve that law.
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

/-- A forced nonlate decision has the prescribed component for every part. -/
theorem component_eq_prescribed_of_forced_nonlate [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (R).InformationAgent (R).playedInformation)
    (forced : ForcedAgent setup leaks bounds initial horizon scheduler agent)
    (nonlate : ¬ KeyedAgent setup leaks bounds initial horizon scheduler agent)
    (part : Part setup leaks bounds initial horizon scheduler slots
      (pool setup leaks bounds initial horizon scheduler agent)) :
    component setup leaks bounds initial horizon scheduler assessment scale nonnegative le_one
        agent part =
      prescribedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one agent := by
  have notFree : ¬ FreeAgent setup leaks bounds initial horizon scheduler agent :=
    fun absent => absent forced
  have notOwned : ¬ ownedKeyed (FreeAgent setup leaks bounds initial horizon scheduler)
      (KeyedAgent setup leaks bounds initial horizon scheduler) agent :=
    fun owned => nonlate owned.1
  obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free (Opt := LateOption slots)
    (freeLaw setup leaks bounds initial horizon scheduler scale nonnegative le_one)
    (prescribedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
      le_one)
    (keyedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
      le_one) notFree
  exact (same part).trans (keyedComponent_of_not_keyed _ _ notOwned (identify part))

/-- Completion weights cannot change a forced nonlate decision's prescribed law. -/
theorem component_mixture_eq_prescribed_of_forced_nonlate [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (R).InformationAgent (R).playedInformation)
    (forced : ForcedAgent setup leaks bounds initial horizon scheduler agent)
    (nonlate : ¬ KeyedAgent setup leaks bounds initial horizon scheduler agent)
    (weights : PMF (Part setup leaks bounds initial horizon scheduler slots
      (pool setup leaks bounds initial horizon scheduler agent))) :
    weights.bind (component setup leaks bounds initial horizon scheduler assessment scale
      nonnegative le_one agent) =
      prescribedComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one agent := by
  have same : component setup leaks bounds initial horizon scheduler assessment (slots := slots)
      scale nonnegative
      le_one agent = fun _ => prescribedComponent setup leaks bounds initial horizon scheduler
        assessment scale nonnegative le_one agent := by
    funext part
    exact component_eq_prescribed_of_forced_nonlate setup leaks bounds initial horizon scheduler
      assessment scale nonnegative le_one agent forced nonlate part
  rw [same, PMF.bind_const]

/-- The common prescribed mixture at a forced nonlate clear decision projects
to the original slot-prescribed native law. -/
theorem component_mixture_projected_of_forced_nonlate [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (R).InformationAgent (R).playedInformation)
    (forced : ForcedAgent setup leaks bounds initial horizon scheduler agent)
    (nonlate : ¬ KeyedAgent setup leaks bounds initial horizon scheduler agent)
    (weights : PMF (Part setup leaks bounds initial horizon scheduler slots
      (pool setup leaks bounds initial horizon scheduler agent))) :
    (weights.bind (component setup leaks bounds initial horizon scheduler assessment scale
      nonnegative le_one agent)).map
        (boundedRecoveryChoiceEquiv (runtime setup) leaks bounds initial horizon scheduler agent.1
          agent.2.1 forced.1).symm =
      slotPrescribedComponent setup leaks bounds (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) assessment scale nonnegative le_one
        agent.1 (RecoveryProjection.information (runtime setup) leaks agent.2.1) := by
  rw [component_mixture_eq_prescribed_of_forced_nonlate setup leaks bounds initial horizon scheduler
    assessment scale nonnegative le_one agent forced nonlate weights]
  exact prescribedComponent_projected setup leaks bounds initial horizon scheduler assessment scale
    nonnegative le_one agent forced.1

end Vegas.RecoveryOnePacket

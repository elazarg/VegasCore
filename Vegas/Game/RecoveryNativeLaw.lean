/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativeComparison
import GameTheory.Math.Probability.Support

/-! # Native action laws of clear recovery components

Canonical source initial laws identify actual clear component laws with the
original native laws on optional packet actions.
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

private theorem nativeChoice_cast_val (who : Player)
    (input : (application setup leaks).Info)
    {first second : PMF (EventGraphRuntime.State (graph setup))} (same : first = second)
    (choice : ((bounds.onePacketMenu (runtime setup) leaks).information first horizon
      (NativeScheduler)).Choice who input) :
    (Equiv.cast (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
      ((bounds.onePacketMenu (runtime setup) leaks).information law horizon
        (NativeScheduler)).Choice who input) same) choice).1 = choice.1 := by
  subst second
  rfl

/-- The canonical source choice equivalence projects the actual optional action. -/
theorem sourceNativeChoiceEquiv_val (who : Player)
    (input : (application setup leaks).Info)
    (choice : (R).Choice who (liftInformation (runtime setup) leaks input)) :
    (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input choice).1 =
      choice.1.map (action (runtime setup) leaks) := by
  unfold sourceNativeChoiceEquiv
  rw [Equiv.trans_apply, nativeChoice_cast_val setup leaks bounds horizon scheduler who input
    (initialLaw_native setup)]
  rfl

private theorem nativeLaw_map_val (who : Player) (input : (application setup leaks).Info)
    (law : ∀ initial : PMF (EventGraphRuntime.State (graph setup)),
      PMF (((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
        (NativeScheduler)).Choice who input))
    {first second : PMF (EventGraphRuntime.State (graph setup))} (same : first = second) :
    (law first).map Subtype.val = (law second).map Subtype.val := by
  subst second
  rfl

/-- Prescribed recovery laws retain their exact native action distribution at
complete clear inputs. -/
theorem prescribedComponent_native [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (R).InformationAgent (R).playedInformation)
    (clear : ClearInput (runtime setup) leaks agent.2.1) :
    (prescribedComponent setup leaks bounds Initial horizon scheduler assessment scale nonnegative
      le_one agent).map (fun choice => choice.1.map (action (runtime setup) leaks)) =
      (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
        assessment scale nonnegative le_one agent.1
        (RecoveryProjection.information (runtime setup) leaks agent.2.1)).map Subtype.val := by
  exact (boundedRecoveryLaw_map_val (runtime setup) leaks bounds Initial horizon scheduler
    agent.1 agent.2.1 clear _).trans
      (nativeLaw_map_val setup leaks bounds horizon scheduler agent.1
        (RecoveryProjection.information (runtime setup) leaks agent.2.1)
        (fun initial => slotPrescribedComponent setup leaks bounds initial horizon
          (NativeScheduler) assessment scale nonnegative le_one agent.1
          (RecoveryProjection.information (runtime setup) leaks agent.2.1))
        (initialLaw_native setup))

/-- Keyed recovery laws retain the same late option and native action law. -/
theorem keyedComponent_native [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (R).InformationAgent (R).playedInformation)
    (clear : ClearInput (runtime setup) leaks agent.2.1) (option : LateOption slots) :
    (keyedComponent setup leaks bounds Initial horizon scheduler assessment scale nonnegative
      le_one agent option).map (fun choice => choice.1.map (action (runtime setup) leaks)) =
      (lateComponent setup leaks bounds (initialLaw setup) horizon (NativeScheduler) assessment
        scale nonnegative le_one agent.1
        (RecoveryProjection.information (runtime setup) leaks agent.2.1) option).map
          Subtype.val := by
  exact (boundedRecoveryLaw_map_val (runtime setup) leaks bounds Initial horizon scheduler
    agent.1 agent.2.1 clear _).trans
      (nativeLaw_map_val setup leaks bounds horizon scheduler agent.1
        (RecoveryProjection.information (runtime setup) leaks agent.2.1)
        (fun initial => lateComponent setup leaks bounds initial horizon (NativeScheduler)
          assessment scale nonnegative le_one agent.1
          (RecoveryProjection.information (runtime setup) leaks agent.2.1) option)
        (initialLaw_native setup))

/-- Canonical source lifting preserves the uniform finite-menu reference. -/
theorem uniformPolicy_sourceNative (who : Player) (input : (application setup leaks).Info) :
    ((Recovery.onePacketMenu (runtime setup) leaks bounds).uniformPolicy Initial horizon scheduler
      who (liftInformation (runtime setup) leaks input)).map
        (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input) =
      ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
        (NativeScheduler) who input) := by
  let := Fintype.ofFinite ((R).Choice who (liftInformation (runtime setup) leaks input))
  let := Fintype.ofFinite ((N).Choice who input)
  change (PMF.uniformOfFintype _).map _ = PMF.uniformOfFintype _
  classical
  ext target
  let equivalent := sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input
  obtain ⟨source, rfl⟩ := equivalent.surjective target
  rw [pmf_map_apply_of_injective _ equivalent.injective]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr equivalent]

/-- Mapping a canonical source choice law and then forgetting legality preserves
the concrete projected optional-action distribution. -/
theorem sourceNativeChoiceEquiv_map_val (who : Player)
    (input : (application setup leaks).Info)
    (law : PMF ((R).Choice who (liftInformation (runtime setup) leaks input))) :
    (law.map (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who input)).map
        Subtype.val =
      law.map (fun choice => choice.1.map (action (runtime setup) leaks)) := by
  rw [PMF.map_comp]
  congr 1
  funext choice
  exact sourceNativeChoiceEquiv_val setup leaks bounds horizon scheduler who input choice

/-- The free recovery tremble is the native free tremble of its projected choice. -/
theorem freeLaw_sourceNative [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (decision : (R).IsDecisionInfo agent.1 (liftInformation (runtime setup) leaks agent.2.1))
    (choice : (R).Choice agent.1 (liftInformation (runtime setup) leaks agent.2.1)) :
    (freeLaw setup leaks bounds Initial horizon scheduler scale nonnegative le_one
      ((R).agentAt ⟨liftInformation (runtime setup) leaks agent.2.1, decision⟩) choice).map
        (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler agent.1 agent.2.1) =
      unforcedLaw setup leaks bounds horizon (NativeScheduler) scale nonnegative le_one agent
        (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler agent.1 agent.2.1
          choice) := by
  unfold freeLaw unforcedLaw
  rw [mix_map, PMF.pure_map, uniformPolicy_sourceNative]

end Vegas.RecoveryOnePacket

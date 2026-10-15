/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionLocalSeedProduct
import Interaction.ReactiveSchedulerFinishSeed

/-! # Actual recovery continuations from filtered local seed beliefs -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (RecoveryState graph))
  (inputs : PMF graph.Inputs) (horizon : Nat)
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side))

local notation "native" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder
    (LocalSeedController.initialMemory (values false) (values true))
local notation "nativeMixture" => ReactiveApplication.schedulerMixture native
  (independentProduct laws) family
local notation "recoveryMixture" => ReactiveApplication.schedulerMixture
  (runtime.recoveryApplication leaks) (independentProduct laws)
    (fun values => liftScheduler runtime leaks (family values))
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler recoveryMixture
local notation "NativeMenu" => MessageBounds.onePacketMenu runtime leaks bounds
local notation "NativeModel" => ReactiveApplication.ResponseMenu.information
  NativeMenu (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler)
local notation "SeedModel" => ReactiveApplication.ResponseMenu.information
  NativeMenu (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler nativeMixture)
local notation "RecoveryModel" => ReactiveApplication.ResponseMenu.information
  (Recovery.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "nativeModelAt" draw:max schedule:max =>
  ReactiveApplication.ResponseMenu.information NativeMenu draw horizon schedule

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (LocalSeedController.initialMemory (values false) (values true)))))))]

local notation "nativeSiteAt" reference:max decision:max => Subtype.mk
  (p := InformationModel.IsDecisionInfo NativeModel owner)
  (ReactiveApplication.observe native owner (some reference)) decision
local notation "recoverySiteAt" reference:max decision:max => Subtype.mk
  (p := InformationModel.IsDecisionInfo RecoveryModel owner)
  (liftInformation runtime leaks
    (ReactiveApplication.observe native owner (some reference))) decision

/-- The actual complete recovery continuation law at a clear decision starts
from the locally filtered original seed and the same full residual state.
The remaining player policies are common across original scheduler seeds. -/
theorem clear_bayesBelief_finish_seeded
    (initialized : ∀ state ∈ initial.support, ∃ setup,
      state = (⟨State.initial setup, ∅⟩ : RecoveryState graph))
    (initialEq : initial.map RecoveryState.native = inputs.map State.initial)
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (reference : (native).Control) (active : reference.actor = some owner)
    (valid : PublicExclusionRecord (⟨reference.execution.application, ∅⟩ : RecoveryState graph))
    (nativeDecision : (NativeModel).IsDecisionInfo owner
      ((native).observe owner (some reference)))
    (recoveryDecision : (RecoveryModel).IsDecisionInfo owner
      (liftInformation runtime leaks ((native).observe owner (some reference))))
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (positive : 0 < (NativeModel).informationMass
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) owner
        (nativeSiteAt reference nativeDecision))
    (ready : reference.execution.application.publicView.EventReady event)
    (unmissed : reference.execution.application.publicView.missedBindingBy owner = false)
    (players : Player → (runtime.recoveryApplication leaks).Policy) :
    ∃ (log : List (LocalSeedEntry graph (native).Command))
      (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (residual : PMF ((runtime.recoveryApplication leaks).ProtocolState ×
        ((side : {side : Bool // side ≠ false}) → A side))),
      (∀ current, some current ∈
          (((RecoveryModel).bayesBelief profile owner (recoverySiteAt reference recoveryDecision)
            ((Recovery.onePacketMenu runtime leaks bounds).decisionInformationAntichain initial
              horizon scheduler owner (recoverySiteAt reference recoveryDecision))
            (by
              rw [bounded_informationMass_liftedInformationSite runtime leaks bounds initial
                initialized horizon scheduler owner reference active valid nativeDecision
                  recoveryDecision profile]
              exact positive)).map (fun history => history.1.state)).support →
        ∀ values ∈ ((recoveryMixture).posterior current.execution.environmentRecall).support,
          (controller.replay remainder
            (LocalSeedController.initialMemory (values false) (values true))
              (current.execution.environmentRecall.map (environmentEntry runtime leaks))).log =
                log) ∧
      (((RecoveryModel).bayesBelief profile owner (recoverySiteAt reference recoveryDecision)
        ((Recovery.onePacketMenu runtime leaks bounds).decisionInformationAntichain initial horizon
          scheduler owner (recoverySiteAt reference recoveryDecision))
        (by
          rw [bounded_informationMass_liftedInformationSite runtime leaks bounds initial initialized
            horizon scheduler owner reference active valid nativeDecision recoveryDecision profile]
          exact positive)).bind fun history =>
            (runtime.recoveryApplication leaks).finish initial horizon scheduler players
              history.1.state) =
        ((laws false).filter {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply} localPositive).bind fun localSeed =>
            residual.bind fun remaining =>
              (runtime.recoveryApplication leaks).finish initial horizon
                (liftScheduler runtime leaks
                  (family ((Equiv.piSplitAt false A).symm (localSeed, remaining.2))))
                players remaining.1 := by
  classical
  obtain ⟨log, localPositive, residual, recovered, product⟩ :=
    clear_bayesBelief_seed_product runtime leaks bounds initial inputs horizon controller
      remainder laws initialized initialEq ordered domainEq owned reference active valid
        nativeDecision recoveryDecision profile positive ready unmissed
  refine ⟨log, localPositive, residual, recovered, ?_⟩
  let follow := fun result : A false ×
      ((runtime.recoveryApplication leaks).ProtocolState ×
        ((side : {side : Bool // side ≠ false}) → A side)) =>
    (runtime.recoveryApplication leaks).finish initial horizon
      (liftScheduler runtime leaks
        (family ((Equiv.piSplitAt false A).symm (result.1, result.2.2))))
      players result.2.1
  have transferred := congrArg (fun law => law.bind follow) product
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, follow] at transferred
  rw [← transferred]
  apply bind_congr_on_support _
  intro history _
  have joint := congrArg (PMF.map Prod.fst)
    (ReactiveApplication.schedulerMixture_finish_joint (runtime.recoveryApplication leaks)
      (independentProduct laws) (fun values => liftScheduler runtime leaks (family values))
        initial horizon players history.1.state)
  simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
    PMF.bind_const, PMF.bind_pure] at joint
  have merged (values : (side : Bool) → A side) :
      (Equiv.piSplitAt false A).symm
        (values false, fun side : {side : Bool // side ≠ false} => values side) = values :=
    (Equiv.piSplitAt false A).symm_apply_apply values
  simp only [merged]
  convert joint.symm using 1
  cases stateEq : history.1.state <;> rfl

end Vegas.EventGraphRuntime.RecoveryProjection

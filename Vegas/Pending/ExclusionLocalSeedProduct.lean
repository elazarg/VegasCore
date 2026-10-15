/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionSchedulerSeed
import Vegas.Pending.ExclusionSeedBelief
import Vegas.Pending.ExclusionBoundedProfile
import Vegas.Pending.ReactiveSeedBayesProduct

/-! # Local seed filtering under projected recovery profiles -/

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

private theorem seed_product_at_equal_laws
    (nativeInitial : PMF (native).State) (nativeSchedule : (native).Scheduler)
    (sameInitial : nativeInitial = inputs.map State.initial)
    (sameSchedule : nativeSchedule = (nativeMixture).scheduler)
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (nativeModelAt nativeInitial nativeSchedule).BehavioralPolicy who)
    (site : (nativeModelAt nativeInitial nativeSchedule).InformationSite owner)
    (positive : 0 < (nativeModelAt nativeInitial nativeSchedule).informationMass profile owner site)
    (past : List (native).PlayerEntry) (view : (native).PlayerView)
    (siteInfo : site.1 = some (past, view))
    (ready : view.application.publicView.EventReady event)
    (unmissed : view.application.publicView.missedBindingBy owner = false) :
    ∃ (log : List (LocalSeedEntry graph (native).Command))
      (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (residual : PMF ((native).ProtocolState ×
        ((side : {side : Bool // side ≠ false}) → A side))),
      (∀ current, some current ∈
          (((nativeModelAt nativeInitial nativeSchedule).bayesBelief profile owner site
            ((NativeMenu).decisionInformationAntichain nativeInitial horizon nativeSchedule
              owner site) positive).map (fun history => history.1.state)).support →
        ∀ values ∈ ((nativeMixture).posterior current.execution.environmentRecall).support,
          (controller.replay remainder
            (LocalSeedController.initialMemory (values false) (values true))
              current.execution.environmentRecall).log = log) ∧
      ((((nativeModelAt nativeInitial nativeSchedule).bayesBelief profile owner site
        ((NativeMenu).decisionInformationAntichain nativeInitial horizon nativeSchedule owner site)
        positive).map (β := (native).ProtocolState) (fun history => history.1.state)).bind
          fun state =>
            (match state with
            | none => independentProduct laws
            | some current => (nativeMixture).posterior current.execution.environmentRecall).map
              fun values : (side : Bool) → A side => (values false,
                (state, fun side : {side : Bool // side ≠ false} => values side))) =
        ((laws false).filter {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply} localPositive).bind fun localSeed =>
            residual.map (Prod.mk localSeed) := by
  subst nativeInitial nativeSchedule
  obtain ⟨log, localPositive, residual, recovered, product⟩ :=
    controller.bayesBelief_seed_product remainder laws bounds inputs horizon ordered domainEq
      owned profile site positive past view siteInfo ready unmissed
  exact ⟨log, localPositive, residual, recovered, product⟩

/-- The locally filtered seed product applies to the concretely projected
recovery profile under the actual lifted persistent scheduler mixture. -/
theorem projected_bayesBelief_seed_product
    (initialEq : initial.map RecoveryState.native = inputs.map State.initial)
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (site : (NativeModel).InformationSite owner)
    (positive : 0 < (NativeModel).informationMass
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) owner site)
    (past : List (native).PlayerEntry) (view : (native).PlayerView)
    (siteInfo : site.1 = some (past, view))
    (ready : view.application.publicView.EventReady event)
    (unmissed : view.application.publicView.missedBindingBy owner = false) :
    ∃ (log : List (LocalSeedEntry graph (native).Command))
      (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (residual : PMF ((native).ProtocolState ×
        ((side : {side : Bool // side ≠ false}) → A side))),
      (∀ current, some current ∈
          (((NativeModel).bayesBelief
            (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile)
            owner site ((NativeMenu).decisionInformationAntichain
              (initial.map RecoveryState.native) horizon
                (nativeScheduler runtime leaks scheduler) owner site) positive).map
                  (fun history => history.1.state)).support →
        ∀ values ∈ ((nativeMixture).posterior current.execution.environmentRecall).support,
          (controller.replay remainder
            (LocalSeedController.initialMemory (values false) (values true))
              current.execution.environmentRecall).log = log) ∧
      ((((NativeModel).bayesBelief
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) owner site
        ((NativeMenu).decisionInformationAntichain (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) owner site) positive).map
            (β := (native).ProtocolState) (fun history => history.1.state)).bind fun state =>
              (match state with
              | none => independentProduct laws
              | some current => (nativeMixture).posterior current.execution.environmentRecall).map
                fun values : (side : Bool) → A side => (values false,
                  (state, fun side : {side : Bool // side ≠ false} => values side))) =
        ((laws false).filter {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply} localPositive).bind fun localSeed =>
            residual.map (Prod.mk localSeed) := by
  classical
  have schedulerEq : nativeScheduler runtime leaks scheduler = (nativeMixture).scheduler := by
    rw [schedulerMixture_liftScheduler_scheduler, nativeScheduler_liftScheduler]
  exact seed_product_at_equal_laws (runtime := runtime) (leaks := leaks) (bounds := bounds)
    (inputs := inputs) (horizon := horizon) (controller := controller)
    (remainder := remainder) (laws := laws)
    (initial.map RecoveryState.native) (nativeScheduler runtime leaks scheduler) initialEq
      schedulerEq ordered domainEq owned
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile)
          site positive past view siteInfo ready unmissed

local notation "nativeSiteAt" reference:max decision:max => Subtype.mk
  (p := InformationModel.IsDecisionInfo NativeModel owner)
  (ReactiveApplication.observe native owner (some reference)) decision
local notation "recoverySiteAt" reference:max decision:max => Subtype.mk
  (p := InformationModel.IsDecisionInfo RecoveryModel owner)
  (liftInformation runtime leaks
    (ReactiveApplication.observe native owner (some reference))) decision

/-- At an actual clear recovery decision, the locally filtered original seed
is independent of the full recovery control and every other seed coordinate. -/
theorem clear_bayesBelief_seed_product
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
    (unmissed : reference.execution.application.publicView.missedBindingBy owner = false) :
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
            (match history.1.state with
            | none => independentProduct laws
            | some current => (recoveryMixture).posterior current.execution.environmentRecall).map
              (β := A false × ((runtime.recoveryApplication leaks).ProtocolState ×
                ((side : {side : Bool // side ≠ false}) → A side)))
              (fun values : (side : Bool) → A side => (values false,
                (history.1.state, fun side : {side : Bool // side ≠ false} => values side)))) =
        ((laws false).filter {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply} localPositive).bind fun localSeed =>
            residual.map (Prod.mk localSeed) := by
  classical
  have observed : (native).observe owner (some reference) =
      some (reference.execution.recall owner, reference.execution.observe native owner) := by
    simp only [ReactiveApplication.observe, active, ↓reduceIte]
  obtain ⟨log, localPositive, nativeResidual, recovered, product⟩ :=
    projected_bayesBelief_seed_product runtime leaks bounds initial inputs horizon controller
      remainder laws initialEq ordered domainEq owned profile
        (nativeSiteAt reference nativeDecision) positive
          (reference.execution.recall owner) (reference.execution.observe native owner)
            observed ready unmissed
  have transferred := bounded_bayesBelief_seededState runtime leaks bounds initial initialized
    horizon (independentProduct laws) family owner reference active valid nativeDecision
      recoveryDecision profile positive
  have split := congrArg (PMF.map fun result :
      (runtime.recoveryApplication leaks).ProtocolState × ((side : Bool) → A side) =>
    (result.2 false, (result.1, fun side : {side : Bool // side ≠ false} => result.2 side)))
      transferred
  have lifted := congrArg (PMF.map fun result :
      A false × ((native).ProtocolState × ((side : {side : Bool // side ≠ false}) → A side)) =>
    (result.1, (liftProtocolState runtime leaks result.2.1, result.2.2))) product
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at split lifted
  let residual := nativeResidual.map fun result =>
    (liftProtocolState runtime leaks result.1, result.2)
  refine ⟨log, localPositive, residual, ?_, ?_⟩
  · intro current supported values valueSupport
    have transported := bounded_bayesBelief_projectedState runtime leaks bounds initial
      initialized horizon scheduler owner reference active valid nativeDecision recoveryDecision
        profile positive
    have projectedSupport := (PMF.mem_support_map_iff
      (protocolState runtime leaks) _ _).mpr ⟨some current, supported, rfl⟩
    rw [PMF.map_comp] at projectedSupport
    have nativeSupported := (congrArg
      (fun law : PMF (native).ProtocolState =>
        protocolState runtime leaks (some current) ∈ law.support) transported).mp projectedSupport
    have nativeValueSupport : values ∈
        ((nativeMixture).posterior
          (current.execution.environmentRecall.map (environmentEntry runtime leaks))).support := by
      exact (congrArg (fun law : PMF ((side : Bool) → A side) => values ∈ law.support)
        (schedulerMixture_liftScheduler_posterior runtime leaks (independentProduct laws)
          family current.execution.environmentRecall)).mp valueSupport
    exact recovered (control runtime leaks current) nativeSupported values nativeValueSupport
  · have combined := split.trans lifted
    simp only [residual, PMF.map_comp, Function.comp_def]
    convert combined using 1
    apply bind_congr_on_support _
    intro history _
    cases stateEq : history.1.state <;> rfl

end Vegas.EventGraphRuntime.RecoveryProjection

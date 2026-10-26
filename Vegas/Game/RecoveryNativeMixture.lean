/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeLaw
import Vegas.Game.RecoveryPrescribedMixture

/-! # The native comparison law at actual clear decisions

The comparison uses the original recovery completion weights at every
represented clear site. Equality concerns those sites only.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection


private theorem mixture_of_free {ι : Type} {T : ExecutionProtocol ι}
    {M : InformationModel T} [Fintype T.History] [∀ who, DecidableEq (M.InfoState who)]
    {Key Opt : Type} {free keyed : M.InformationAgent M.playedInformation → Prop}
    {key : M.InformationAgent M.playedInformation → Key}
    (weights : ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
    (freeLaw : ∀ agent : M.InformationAgent M.playedInformation,
      M.Choice agent.1 agent.2.1 → PMF (M.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : M.InformationAgent M.playedInformation,
      PMF (M.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : M.InformationAgent M.playedInformation,
      Opt → PMF (M.Choice agent.1 agent.2.1))
    {agent : M.InformationAgent M.playedInformation} (isFree : free agent) :
    (weights (freeKeyedPool free keyed key agent)).bind
        (freeKeyedComponent freeLaw prescribed keyedLaw agent) =
      (weights (.inl ⟨agent, isFree⟩)).bind (freeLaw agent) := by
  unfold freeKeyedComponent
  rw [freeKeyedPool_of_free isFree]
  apply congrArg (fun kernel : M.Choice agent.1 agent.2.1 → PMF (M.Choice agent.1 agent.2.1) =>
    (weights (.inl ⟨agent, isFree⟩)).bind kernel)
  funext choice
  exact dite_eq_left rfl

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

/-- At any represented clear decision the same pool weights induce the same
optional native action law. -/
theorem nativeComparisonMixture_at_clear [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    {who : Player} (site : (N).InformationSite who)
    (decision : (R).IsDecisionInfo who (liftInformation runtime leaks site.1)) :
    ((nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt
          site))).bind
      (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) assessment scale
        nonnegative
        le_one ((N).agentAt site))).map Subtype.val =
      ((weights (pool setup runtime leaks bounds Initial horizon scheduler
        ((R).agentAt ⟨liftInformation runtime leaks site.1, decision⟩))).bind
          (component setup runtime leaks bounds Initial horizon scheduler assessment scale
            nonnegative
            le_one ((R).agentAt ⟨liftInformation runtime leaks site.1, decision⟩))).map
              (fun choice => choice.1.map (action runtime leaks)) := by
  classical
  let nativeAgent := (N).agentAt site
  let recoveryAgent := (R).agentAt ⟨liftInformation runtime leaks site.1, decision⟩
  have sameInput : RecoveryProjection.information runtime leaks recoveryAgent.2.1 =
      nativeAgent.2.1 := information_liftInformation runtime leaks site.1
  have freeIff : Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler) nativeAgent ↔
      FreeAgent setup runtime leaks bounds Initial horizon scheduler recoveryAgent := by
    change (¬ Vegas.forcedAgent (runtime := runtime) _ _ _ _ who site.1) ↔
      (¬ ForcedAgent setup runtime leaks bounds Initial horizon scheduler recoveryAgent)
    exact not_congr (forcedAgent_iff_at_liftedSite setup runtime leaks bounds horizon scheduler
      site.1
      decision)
  have lateIff : LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon
      (NativeScheduler) nativeAgent ↔
        KeyedAgent setup runtime leaks bounds Initial horizon scheduler recoveryAgent := by
    change LateDelivery setup runtime leaks who site.1 ↔
      LateDelivery setup runtime leaks who (RecoveryProjection.information runtime leaks
        (liftInformation runtime leaks site.1))
    rw [information_liftInformation]
  by_cases nativeFree : Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler)
    nativeAgent
  · have recoveryFree := freeIff.mp nativeFree
    have nativeMix : (nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) nativeAgent)).bind
          (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) assessment scale
            nonnegative le_one nativeAgent) =
        (nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
          (.inl ⟨nativeAgent, nativeFree⟩)).bind
            (unforcedLaw setup runtime leaks bounds horizon (NativeScheduler) scale nonnegative
              le_one
              nativeAgent) :=
      mixture_of_free _ _ _ _ nativeFree
    have recoveryMix : (weights (pool setup runtime leaks bounds Initial horizon scheduler
        recoveryAgent)).bind (component setup runtime leaks bounds Initial horizon scheduler
          assessment
          scale nonnegative le_one recoveryAgent) =
        (weights (.inl ⟨recoveryAgent, recoveryFree⟩)).bind
          (freeLaw setup runtime leaks bounds Initial horizon scheduler scale nonnegative le_one
            recoveryAgent) :=
      mixture_of_free _ _ _ _ recoveryFree
    have freeWeights : nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (.inl ⟨nativeAgent, nativeFree⟩) =
        (weights (.inl ⟨recoveryAgent, recoveryFree⟩)).map
          (sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler who site.1) := by
      have nativeDecision : (R).IsDecisionInfo nativeAgent.1
          (liftInformation runtime leaks nativeAgent.2.1) := decision
      simp only [nativeComparisonWeights, id_eq, dite_eq_left nativeDecision]
      rfl
    change ((nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
      (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) nativeAgent)).bind
        (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) assessment scale
          nonnegative le_one nativeAgent)).map Subtype.val =
      ((weights (pool setup runtime leaks bounds Initial horizon scheduler recoveryAgent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler assessment scale nonnegative
          le_one recoveryAgent)).map _
    rw [nativeMix, recoveryMix, freeWeights, PMF.bind_map, PMF.map_bind, PMF.map_bind]
    congr 1
    funext choice
    have projected := freeLaw_sourceNative setup runtime leaks bounds horizon scheduler scale
      nonnegative
      le_one nativeAgent decision choice
    have values := congrArg (fun law => law.map Subtype.val) projected
    exact (sourceNativeChoiceEquiv_map_val setup runtime leaks bounds horizon scheduler
      nativeAgent.1
      nativeAgent.2.1 _).symm.trans values |>.symm
  · have recoveryNotFree : ¬ FreeAgent setup runtime leaks bounds Initial horizon scheduler
        recoveryAgent := fun free => nativeFree (freeIff.mpr free)
    have recoveryForced : ForcedAgent setup runtime leaks bounds Initial horizon scheduler
        recoveryAgent := Classical.not_not.mp recoveryNotFree
    by_cases late : LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon
        (NativeScheduler) nativeAgent
    · have nativeOwned : ownedKeyed (Vegas.FreeAgent setup runtime leaks bounds horizon
        (NativeScheduler))
          (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon
            (NativeScheduler))
          nativeAgent := ⟨late, nativeFree⟩
      have recoveryOwned : ownedKeyed (FreeAgent setup runtime leaks bounds Initial horizon
        scheduler)
          (KeyedAgent setup runtime leaks bounds Initial horizon scheduler) recoveryAgent :=
        ⟨lateIff.mp late, recoveryNotFree⟩
      have keyEq : agentKey setup runtime leaks bounds Initial horizon scheduler recoveryAgent =
          agentLateKey setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler)
            nativeAgent := congrArg (lateKey setup runtime leaks who) sameInput
      have represented : agentLateKey setup runtime leaks bounds (initialLaw setup) horizon
          (NativeScheduler) nativeAgent ∈ Set.range
            (fun agent : {agent : (R).InformationAgent (R).playedInformation //
              ownedKeyed (FreeAgent setup runtime leaks bounds Initial horizon scheduler)
                (KeyedAgent setup runtime leaks bounds Initial horizon scheduler) agent} =>
                  agentKey setup runtime leaks bounds Initial horizon scheduler agent.1) :=
        ⟨⟨recoveryAgent, recoveryOwned⟩, keyEq⟩
      have nativeMixRaw := Vegas.freeKeyedMixture_of_keyed
        (nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights)
        (unforcedLaw setup runtime leaks bounds horizon (NativeScheduler) scale nonnegative le_one)
        (fun agent => slotPrescribedComponent setup runtime leaks bounds (initialLaw setup) horizon
          (NativeScheduler) assessment scale nonnegative le_one agent.1 agent.2.1)
        (fun agent option => lateComponent setup runtime leaks bounds (initialLaw setup) horizon
          (NativeScheduler) assessment scale nonnegative le_one agent.1 agent.2.1 option)
        nativeFree nativeOwned
      have recoveryMixRaw := Vegas.freeKeyedMixture_of_keyed weights
        (freeLaw setup runtime leaks bounds Initial horizon scheduler scale nonnegative le_one)
        (prescribedComponent setup runtime leaks bounds Initial horizon scheduler assessment scale
          nonnegative le_one)
        (keyedComponent setup runtime leaks bounds Initial horizon scheduler assessment scale
          nonnegative
          le_one) recoveryNotFree recoveryOwned
      have nativeMix : (nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
          (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) nativeAgent)).bind
            (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) assessment
              scale
              nonnegative le_one nativeAgent) =
          (nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
            (.inr (some ⟨agentLateKey setup runtime leaks bounds (initialLaw setup) horizon
              (NativeScheduler) nativeAgent, ⟨nativeAgent, nativeOwned⟩, rfl⟩))).bind
                (fun option => lateComponent setup runtime leaks bounds (initialLaw setup) horizon
                  (NativeScheduler) assessment scale nonnegative le_one nativeAgent.1
                  nativeAgent.2.1 option) := nativeMixRaw
      have recoveryMix : (weights (pool setup runtime leaks bounds Initial horizon scheduler
          recoveryAgent)).bind (component setup runtime leaks bounds Initial horizon scheduler
            assessment
            scale nonnegative le_one recoveryAgent) =
          (weights (.inr (some ⟨agentKey setup runtime leaks bounds Initial horizon scheduler
            recoveryAgent,
            ⟨recoveryAgent, recoveryOwned⟩, rfl⟩))).bind
              (keyedComponent setup runtime leaks bounds Initial horizon scheduler assessment scale
                nonnegative le_one recoveryAgent) := recoveryMixRaw
      change ((nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) nativeAgent)).bind
          (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) assessment scale
            nonnegative le_one nativeAgent)).map Subtype.val =
        ((weights (pool setup runtime leaks bounds Initial horizon scheduler recoveryAgent)).bind
          (component setup runtime leaks bounds Initial horizon scheduler assessment scale
            nonnegative
            le_one recoveryAgent)).map _
      rw [nativeMix, recoveryMix]
      simp only [nativeComparisonWeights, dite_eq_left represented]
      have weightsEq : weights (.inr (some ⟨agentLateKey setup runtime leaks bounds (initialLaw
        setup)
          horizon (NativeScheduler) nativeAgent, represented⟩)) =
          weights (.inr (some ⟨agentKey setup runtime leaks bounds Initial horizon scheduler
            recoveryAgent,
            ⟨⟨recoveryAgent, recoveryOwned⟩, rfl⟩⟩)) := by
        congr 3
        exact Subtype.ext keyEq.symm
      rw [weightsEq, PMF.map_bind, PMF.map_bind]
      congr 1
      funext option
      have projected := (keyedComponent_native setup runtime leaks bounds horizon scheduler
        assessment
        scale nonnegative le_one recoveryAgent recoveryForced.1 option).symm
      exact Eq.mp (congrArg (fun input : (application setup runtime leaks).Info =>
        (lateComponent setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler)
          assessment
          scale nonnegative le_one who input option).map Subtype.val =
          (keyedComponent setup runtime leaks bounds Initial horizon scheduler assessment scale
            nonnegative
            le_one recoveryAgent option).map
              (fun choice => choice.1.map (action runtime leaks))) sameInput) projected
    · have nativeNotOwned : ¬ ownedKeyed
          (Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler))
          (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon
            (NativeScheduler))
          nativeAgent := fun owned => late owned.1
      have recoveryNonlate : ¬ KeyedAgent setup runtime leaks bounds Initial horizon scheduler
          recoveryAgent := fun keyed => late (lateIff.mpr keyed)
      have nativeMixRaw := Vegas.freeKeyedMixture_of_not_keyed
        (nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights)
        (unforcedLaw setup runtime leaks bounds horizon (NativeScheduler) scale nonnegative le_one)
        (fun agent => slotPrescribedComponent setup runtime leaks bounds (initialLaw setup) horizon
          (NativeScheduler) assessment scale nonnegative le_one agent.1 agent.2.1)
        (fun agent option => lateComponent setup runtime leaks bounds (initialLaw setup) horizon
          (NativeScheduler) assessment scale nonnegative le_one agent.1 agent.2.1 option)
        nativeFree nativeNotOwned
      have recoveryMix := component_mixture_eq_prescribed_of_forced_nonlate setup runtime leaks
        bounds
        Initial horizon scheduler assessment scale nonnegative le_one recoveryAgent
        recoveryForced
        recoveryNonlate (weights (pool setup runtime leaks bounds Initial horizon scheduler
          recoveryAgent))
      have nativeMix : (nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
          (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) nativeAgent)).bind
            (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) assessment
              scale
              nonnegative le_one nativeAgent) =
          slotPrescribedComponent setup runtime leaks bounds (initialLaw setup) horizon
            (NativeScheduler)
            assessment scale nonnegative le_one nativeAgent.1 nativeAgent.2.1 := nativeMixRaw
      change ((nativeComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (onePacketPool setup runtime leaks bounds horizon (NativeScheduler) nativeAgent)).bind
          (onePacketComponent setup runtime leaks bounds horizon (NativeScheduler) assessment scale
            nonnegative le_one nativeAgent)).map Subtype.val =
        ((weights (pool setup runtime leaks bounds Initial horizon scheduler recoveryAgent)).bind
          (component setup runtime leaks bounds Initial horizon scheduler assessment scale
            nonnegative
            le_one recoveryAgent)).map _
      rw [nativeMix, recoveryMix]
      have projected := (prescribedComponent_native setup runtime leaks bounds horizon scheduler
        assessment scale nonnegative le_one recoveryAgent recoveryForced.1).symm
      exact Eq.mp (congrArg (fun input : (application setup runtime leaks).Info =>
        (slotPrescribedComponent setup runtime leaks bounds (initialLaw setup) horizon
          (NativeScheduler)
          assessment scale nonnegative le_one who input).map Subtype.val =
          (prescribedComponent setup runtime leaks bounds Initial horizon scheduler assessment scale
            nonnegative le_one recoveryAgent).map
              (fun choice => choice.1.map (action runtime leaks))) sameInput) projected

end Vegas.RecoveryOnePacket

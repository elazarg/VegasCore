/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativeDebt

/-! # Native prefix classes from actual recovery decisions -/

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
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

open Classical in
/-- Every forced debt-free nonlate actual recovery site gives the corresponding
native prefix site and all three native agent classifications. -/
theorem exists_nativePrefixSite [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ player, DecidableEq ((R).InfoState player)]
    [∀ player, DecidableEq ((N).InfoState player)]
    {who : Player} (site : (R).InformationSite who)
    (notFree : ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (nonlate : ¬ KeyedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site)) :
    ∃ nativeSite : (N).InformationSite who,
      nativeSite.1 = RecoveryProjection.information (runtime setup) leaks site.1 ∧
      liftInformation (runtime setup) leaks nativeSite.1 = site.1 ∧
      ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt nativeSite) ∧
      ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt nativeSite) ∧
      ¬ ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
        ((N).agentAt nativeSite) := by
  have forced : ForcedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) :=
    Classical.not_not.mp notFree
  obtain ⟨genericSite, seen, _forcedIff⟩ := exists_nativeInformationSite_of_clear setup leaks bounds
    Initial (initialLaw_initialized setup) horizon scheduler site forced.1
  have genericDecision :
      ((NMenu).information ((Initial).map RecoveryState.native) horizon
        (NativeScheduler)).IsDecisionInfo who
          (RecoveryProjection.information (runtime setup) leaks site.1) :=
    seen ▸ genericSite.2
  have nativeDecision : (N).IsDecisionInfo who
      (RecoveryProjection.information (runtime setup) leaks site.1) :=
    Eq.mp (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).information initial horizon (NativeScheduler)).IsDecisionInfo who
        (RecoveryProjection.information (runtime setup) leaks site.1))
          (initialLaw_native setup)) genericDecision
  let nativeSite : (N).InformationSite who :=
    ⟨RecoveryProjection.information (runtime setup) leaks site.1, nativeDecision⟩
  have lifted : liftInformation (runtime setup) leaks nativeSite.1 = site.1 := forced.1
  have recoveryDecision : (R).IsDecisionInfo who
      (liftInformation (runtime setup) leaks nativeSite.1) := lifted.symm ▸ site.2
  have sites :
      (⟨liftInformation (runtime setup) leaks nativeSite.1, recoveryDecision⟩ :
        (R).InformationSite who) = site := Subtype.ext lifted
  refine ⟨nativeSite, rfl, lifted, ?_, ?_, ?_⟩
  · intro free
    apply notFree
    have recovered := freeAgent_of_nativeFree setup leaks bounds horizon scheduler
      ((N).agentAt nativeSite) free recoveryDecision
    exact Eq.mp (congrArg (fun current : (R).InformationSite who =>
      FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt current)) sites) recovered
  · intro owing
    apply notOwing
    have recovered := owingAgent_of_nativeOwing_at_liftedSite setup leaks bounds horizon scheduler
      nativeSite recoveryDecision owing
    exact Eq.mp (congrArg (fun current : (R).InformationSite who =>
      OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt current)) sites)
        recovered
  · intro keyed
    exact nonlate keyed.1

end Vegas.RecoveryOnePacket

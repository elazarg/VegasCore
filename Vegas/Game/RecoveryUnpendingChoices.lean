/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativePrefixSites
import Vegas.Game.RecoveryNonLateChoices

/-! # Unpending choices at actual recovery information sites

At clear nonlate sites without source debt, an empty pending event leaves one
legal response. Every local replacement therefore preserves the whole policy
and has zero gain under the original recovery assessment.
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

variable
  [Fintype ((Recovery.onePacketMenu (runtime setup) leaks bounds).protocol
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).History]
  [(application setup leaks).FiniteNature (initialLaw setup)
    (nativeScheduler (runtime setup) leaks scheduler)]
  [∀ who, DecidableEq ((model setup leaks bounds
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).InfoState who)]

/-- The actual recovery menu is a singleton at an unpending clear nonlate
information site without latent source debt. -/
theorem choice_eq_of_unpending_notOwing (wellFormed : setup.WellFormed)
    {who : Player} (site : (R).InformationSite who)
    (notFree : ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (nonlate : ¬ KeyedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    {past : List (recoveryApplication (runtime setup) leaks).PlayerEntry}
    {view : (recoveryApplication (runtime setup) leaks).PlayerView}
    (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup leaks who
      (RecoveryProjection.information (runtime setup) leaks site.1) = none)
    (first second : (R).Choice who site.1) : first = second := by
  classical
  obtain ⟨nativeSite, seen, lifted, _nativeNotFree, nativeNotOwing, _nativeNonlate⟩ :=
    exists_nativePrefixSite setup leaks bounds horizon scheduler site notFree notOwing nonlate
  let equivalent : (R).Choice who site.1 ≃ (N).Choice who nativeSite.1 :=
    (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm)).trans
      (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who nativeSite.1)
  have atNative : nativeSite.1 = some
      (past.map (RecoveryProjection.playerEntry (runtime setup) leaks),
        RecoveryProjection.playerView (runtime setup) leaks view) := by
    rw [seen, atSite]
    rfl
  have nativeUnpending : pendingEvent setup leaks who nativeSite.1 = none := seen.symm ▸ unpending
  apply equivalent.injective
  apply Subtype.ext
  exact (Vegas.choice_eq_silence_of_unpending_notOwing wellFormed nativeSite nativeNotOwing
    atNative nativeUnpending (equivalent first)).trans
      (Vegas.choice_eq_silence_of_unpending_notOwing wellFormed nativeSite nativeNotOwing
        atNative nativeUnpending (equivalent second)).symm

/-- Any local recovery law at an unpending clear nonlate debt-free site
preserves the entire behavioral policy. -/
theorem withLaw_eq_self_of_unpending_notOwing (wellFormed : setup.WellFormed)
    {who : Player} (site : (R).InformationSite who)
    (notFree : ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (nonlate : ¬ KeyedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    {past : List (recoveryApplication (runtime setup) leaks).PlayerEntry}
    {view : (recoveryApplication (runtime setup) leaks).PlayerView}
    (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup leaks who
      (RecoveryProjection.information (runtime setup) leaks site.1) = none)
    (policy : (R).BehavioralPolicy who) (law : PMF ((R).Choice who site.1)) :
    policy.withLaw site.1 law = policy := by
  classical
  obtain ⟨choice, _⟩ := law.support_nonempty
  have unique := choice_eq_of_unpending_notOwing setup leaks bounds horizon scheduler wellFormed
    site notFree notOwing nonlate atSite unpending
  have oneLaw : ∀ measure : PMF ((R).Choice who site.1), measure = PMF.pure choice := by
    intro measure
    calc
      measure = measure.map id := (PMF.map_id measure).symm
      _ = measure.map (fun _ => choice) :=
        congrArg (fun f => measure.map f) (funext (fun other => unique other choice))
      _ = PMF.pure choice := PMF.map_const _ _
  rw [(oneLaw law).trans (oneLaw (policy site.1)).symm]
  exact BehavioralPolicy.withLaw_eq_self _ _

end Vegas.RecoveryOnePacket

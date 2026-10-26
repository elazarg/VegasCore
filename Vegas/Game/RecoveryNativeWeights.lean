/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryClearDecisionSites
import Vegas.Game.OnePacketCertificateDischarge
import Vegas.Pending.ExclusionFiniteNature

/-! # Native comparison weights from the recovery completion witness

Represented singleton and late-key pools use the original recovery weights.
Other native pools receive arbitrary valid weights. The construction asserts no
native optimality or equilibrium property.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

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
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu runtime leaks bounds) (initialLaw setup) horizon
  (NativeScheduler)

omit [Fintype Player] in
theorem initialLaw_native : (Initial).map RecoveryState.native = initialLaw setup := by
  rw [PMF.map_comp]
  exact PMF.map_id _

omit [Fintype Player] in
/-- The canonical recovery prior starts from native initial configurations with no exclusions. -/
theorem initialLaw_initialized (state : RecoveryState (graph setup))
    (supported : state ∈ (Initial).support) :
    ∃ inputs, state =
      (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)) := by
  obtain ⟨native, nativeSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  change native ∈ (setup.initialLaw.map
    (fun draw => State.initial (graph := graph setup) (setup.eventInputs draw))).support
    at nativeSupported
  obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp nativeSupported
  exact ⟨setup.eventInputs draw, rfl⟩

omit [Fintype Player] in
/-- Actual recovery finite nature supplies the original native finiteness
instance at the compiled source initial law. -/
instance sourceNativeFiniteNature
    [(recoveryApplication runtime leaks).FiniteNature Initial scheduler] :
    (application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler) := by
  have finite := nativeSchedulerFiniteNature runtime leaks Initial scheduler
  simpa only [initialLaw_native setup] using finite

/-- At a represented native input, canonical recovery lifting preserves and
reflects the forced region of the original native initial law. -/
theorem forcedAgent_iff_at_liftedSite [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)] {who : Player}
    (input : (application setup runtime leaks).Info)
    (decision : (R).IsDecisionInfo who (liftInformation runtime leaks input)) :
    Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw setup)
      horizon
        (NativeScheduler) who input ↔
      ForcedAgent setup runtime leaks bounds Initial horizon scheduler
        ((R).agentAt ⟨liftInformation runtime leaks input, decision⟩) := by
  let site : (R).InformationSite who :=
    ⟨liftInformation runtime leaks input, decision⟩
  obtain ⟨nativeSite, seen, matching⟩ := exists_nativeInformationSite_of_clear setup runtime leaks
    bounds
    Initial (initialLaw_initialized setup) horizon scheduler site
    (clearInput_lift runtime leaks input)
  have nativeInput : nativeSite.1 = input :=
    seen.trans (information_liftInformation runtime leaks input)
  have original :
      Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks)
          ((Initial).map RecoveryState.native) horizon (NativeScheduler) who input ↔
        ForcedAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site) := by
    simpa only [nativeInput] using matching
  exact Eq.mp (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
    Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) law horizon
        (NativeScheduler) who input ↔
      ForcedAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site))
    (initialLaw_native setup)) original

/-- Canonical source lifting transports a recovery choice to the original native menu. -/
def sourceNativeChoiceEquiv (who : Player) (input : (application setup runtime leaks).Info) :
    (R).Choice who (liftInformation runtime leaks input) ≃ (N).Choice who input :=
  (boundedChoiceEquiv runtime leaks bounds Initial horizon scheduler who input).trans
    (Equiv.cast (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
      ((bounds.onePacketMenu runtime leaks).information law horizon
        (NativeScheduler)).Choice who input) (initialLaw_native setup)))

/-- A native free agent represented by an actual canonical recovery decision
is free in the recovery completion as well. -/
theorem freeAgent_of_nativeFree [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (agent : (N).InformationAgent (N).playedInformation)
    (unforced : Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler) agent)
    (decision : (R).IsDecisionInfo agent.1
      (liftInformation runtime leaks agent.2.1)) :
    FreeAgent setup runtime leaks bounds Initial horizon scheduler
      ((R).agentAt ⟨liftInformation runtime leaks agent.2.1, decision⟩) := by
  intro forced
  have notForced := unforced
  change ¬ Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
    setup) horizon
    (NativeScheduler) agent.1 agent.2.1 at notForced
  exact notForced ((forcedAgent_iff_at_liftedSite setup runtime leaks bounds horizon scheduler
    agent.2.1 decision).mpr forced)

open Classical in
/-- Extend the same recovery completion weights to all native comparison pools.
Only pools absent from the actual clear recovery game receive arbitrary weights. -/
def nativeComparisonWeights [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    {slots : Nat} (weights : ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler
      slots p)) :
    ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon (NativeScheduler) slots p)
  | .inl owner => by
      change PMF ((N).Choice owner.1.1 owner.1.2.1)
      by_cases decision : (R).IsDecisionInfo owner.1.1
          (liftInformation runtime leaks owner.1.2.1)
      · let site : (R).InformationSite owner.1.1 :=
          ⟨liftInformation runtime leaks owner.1.2.1, decision⟩
        let agent := (R).agentAt site
        have free : FreeAgent setup runtime leaks bounds Initial horizon scheduler agent :=
          freeAgent_of_nativeFree setup runtime leaks bounds horizon scheduler owner.1 owner.2
            decision
        have prior : PMF ((R).Choice owner.1.1
            (liftInformation runtime leaks owner.1.2.1)) :=
          weights (.inl ⟨agent, free⟩)
        exact prior.map fun choice =>
          sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler owner.1.1
            owner.1.2.1 choice
      · exact PMF.pure (Classical.arbitrary _)
  | .inr none => PMF.pure ()
  | .inr (some key) =>
      if represented : key.1 ∈ Set.range
          (fun agent : {agent : (R).InformationAgent (R).playedInformation //
            ownedKeyed (FreeAgent setup runtime leaks bounds Initial horizon scheduler)
              (KeyedAgent setup runtime leaks bounds Initial horizon scheduler) agent} =>
            agentKey setup runtime leaks bounds Initial horizon scheduler agent.1) then
        weights (.inr (some ⟨key.1, represented⟩))
      else PMF.pure (Classical.arbitrary _)

end Vegas.RecoveryOnePacket

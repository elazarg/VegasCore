/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePolicyRun
import Interaction.ReactiveConsistentHistory
import Vegas.Pending.PhaseServiceContract

/-! # Actual clear physical preimages of consistent native histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Every genuine consistent native history has an actual clear counted physical
preimage. It is obtained from the original execution laws, not a supplied replay. -/
theorem exists_clear_physical_of_native_consistent (bounds : MessageBounds graph)
  (ordered : graph.RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
  (players : Player → (P).Policy) (nativePlayers : Player → (N).Policy)
  (covered : ∀ (who : Player) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (response : (P).Action), response ∈ (players who past view).support →
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
  (safe : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    (∀ who, (players who).Consistent (current.execution.recall who)) →
      current.execution.application.current.excluded = ∅)
  (agreement : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    current.execution.application.current.excluded = ∅ →
    (∀ who, (players who).Consistent (current.execution.recall who)) →
    (∀ who, (nativePlayers who).Consistent
      ((execution runtime leaks plan current.execution).recall who)) →
    ∀ who, current.actor = some who → nativePlayers who
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      nativePolicy runtime leaks plan (players who)
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who))
    {current : (N).Control}
    (trace : ((N).protocol (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)).Trace (some current))
    (consistent : ∀ who, (nativePlayers who).Consistent (current.execution.recall who)) :
    ∃ (physical : (P).Control)
      (_physicalTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some physical)),
      (∀ who, (players who).Consistent (physical.execution.recall who)) ∧
      physical.execution.application.current.excluded = ∅ ∧
      current = control runtime leaks plan physical := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let nativeInitial := inputs.map State.initial
  let imageScheduler := nativeScheduler runtime leaks plan scheduler
  obtain ⟨paired, first, second, valid⟩ := exists_paired_behavioral_run_of_local_agreement
    runtime leaks plan bounds ordered maximal inputs horizon scheduler players nativePlayers
      covered safe agreement trace.length
  have originalSupported := (N).history_mem_support_runBehavioral_of_consistent
    nativeInitial horizon imageScheduler nativePlayers trace (fun _ same => by
      cases Option.some.inj same
      exact consistent)
  have nativeSupported : some current ∈ (paired.map Prod.fst).support := by
    rw [first, InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨⟨some current, trace⟩, originalSupported, rfl⟩
  obtain ⟨⟨nativeState, physicalState⟩, pairedSupported, same⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp nativeSupported
  change nativeState = some current at same
  subst nativeState
  have projected := (valid (some current, physicalState) pairedSupported).1
  cases physicalState with
  | none => cases projected
  | some physical =>
      have physicalSupported : some physical ∈
          (((menu.information initial horizon scheduler).runBehavioralFrom
            (fun who => menu.restrictPolicy initial horizon scheduler who (players who))
              trace.length (menu.protocol initial horizon scheduler).initHistory).map
                History.state).support := by
        rw [← second]
        exact (PMF.mem_support_map_iff _ _ _).mpr
          ⟨(some current, some physical), pairedSupported, rfl⟩
      rw [menu.run_restrict_control_steps initial horizon scheduler players
        (menu.admissible_of_covered initial horizon scheduler players covered)] at physicalSupported
      obtain ⟨physicalTrace, faithful⟩ := supported_control_play runtime leaks plan bounds inputs
        horizon scheduler players covered trace.length (some physical) physicalSupported
      change some current = some (control runtime leaks plan physical) at projected
      exact ⟨physical, physicalTrace, faithful physical rfl,
        safe physical physicalTrace (faithful physical rfl), Option.some.inj projected⟩

/-- Physical clearance rules out every owned public failure on an actual native
history consistent with the matched prescribed profile. -/
theorem not_publicFailure_of_native_consistent (bounds : MessageBounds graph)
  (ordered : graph.RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
  (players : Player → (P).Policy) (nativePlayers : Player → (N).Policy)
  (covered : ∀ (who : Player) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (response : (P).Action), response ∈ (players who past view).support →
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
  (safe : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    (∀ who, (players who).Consistent (current.execution.recall who)) →
      current.execution.application.current.excluded = ∅)
  (agreement : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    current.execution.application.current.excluded = ∅ →
    (∀ who, (players who).Consistent (current.execution.recall who)) →
    (∀ who, (nativePlayers who).Consistent
      ((execution runtime leaks plan current.execution).recall who)) →
    ∀ who, current.actor = some who → nativePlayers who
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      nativePolicy runtime leaks plan (players who)
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who))
    {current : (N).Control}
    (trace : ((N).protocol (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)).Trace (some current))
    (consistent : ∀ who, (nativePlayers who).Consistent (current.execution.recall who))
    (event : graph.EventId) (owner : Player) (acting : graph.actor? event = some owner) :
    ¬current.execution.application.PublicFailure event := by
  obtain ⟨physical, physicalTrace, _faithful, clear, same⟩ :=
    exists_clear_physical_of_native_consistent runtime leaks plan bounds ordered maximal inputs
      horizon scheduler players nativePlayers covered safe agreement trace consistent
  intro failed
  rw [same] at failed
  change physical.execution.application.current.native.PublicFailure event at failed
  have record := clear_publicRecord runtime leaks plan bounds inputs horizon scheduler
    physicalTrace clear
  have excluded := (record.excluded owner).mpr ⟨event, acting, failed⟩
  rw [clear] at excluded
  exact Finset.notMem_empty owner excluded


/-- Completion is needed only at actual histories consistent with the matched
native profile. The physical contract retains its all-legal-history scope. -/
theorem terminal_of_native_consistent (bounds : MessageBounds graph)
  (ordered : graph.RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
  (players : Player → (P).Policy) (nativePlayers : Player → (N).Policy)
  (covered : ∀ (who : Player) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (response : (P).Action), response ∈ (players who past view).support →
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
  (safe : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    (∀ who, (players who).Consistent (current.execution.recall who)) →
      current.execution.application.current.excluded = ∅)
  (agreement : ∀ (current : (P).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
    current.execution.application.current.excluded = ∅ →
    (∀ who, (players who).Consistent (current.execution.recall who)) →
    (∀ who, (nativePlayers who).Consistent
      ((execution runtime leaks plan current.execution).recall who)) →
    ∀ who, current.actor = some who → nativePlayers who
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      nativePolicy runtime leaks plan (players who)
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who))
    (completes : PhaseService.CompletesPlay runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler)
    {current : (N).Control}
    (trace : ((N).protocol (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)).Trace (some current))
    (consistent : ∀ who, (nativePlayers who).Consistent (current.execution.recall who))
    (terminal : (N).terminal (some current)) :
    current.execution.application.config.cut.Terminal := by
  obtain ⟨physical, physicalTrace, _faithful, _clear, same⟩ :=
    exists_clear_physical_of_native_consistent runtime leaks plan bounds ordered maximal inputs
      horizon scheduler players nativePlayers covered safe agreement trace consistent
  have physicalTerminal : (P).terminal (some physical) := by
    rw [same] at terminal
    exact terminal
  have done := completes physical ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    _ horizon scheduler physicalTrace) physicalTerminal
  rw [same]
  exact done

end Vegas.EventGraphRuntime.PhaseNativeProjection

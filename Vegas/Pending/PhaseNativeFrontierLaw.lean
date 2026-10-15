/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePolicyPreimage
import Vegas.Pending.ReactiveFailureFreeExpiry
import Vegas.Pending.ReactiveFrontierExecution

/-! # Canonical native store laws from actual physical safety and local matching -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph) (profile : graph.BehavioralProfile)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)
local notation "NP" => fun owner => runtime.prescribedReactivePolicy
  (nativeLeaks leaks plan) owner (profile owner)

/-- Every supported native expiry retains the same semantic frontier when the
physical policy is safe and its actual callbacks match the prescribed compiler. -/
theorem frontier_expire_of_native_consistent (bounds : MessageBounds graph)
  (ordered : graph.RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
  (players : Player → (P).Policy)
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
    (∀ who, ((NP) who).Consistent
      ((execution runtime leaks plan current.execution).recall who)) →
    ∀ who, current.actor = some who → (NP) who
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      nativePolicy runtime leaks plan (players who)
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who))
    (remaining : Nat) (execution : (N).Execution)
    (trace : ((N).protocol (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)).Trace (some ⟨remaining + 1, none, execution⟩))
    (consistent : ∀ owner, ((NP) owner).Consistent (execution.recall owner))
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier (nativeLeaks leaks plan) execution memories frontier)
    (event : graph.EventId)
    (selected : .application (.expire event) ∈
      ((nativeScheduler runtime leaks plan scheduler) execution.environmentRecall
        (execution.observeEnvironment N)).support)
    (next : (N).Execution)
    (supported : next ∈ (execution.environmentStep N (.application (.expire event))).support) :
    runtime.ReactiveFrontier (nativeLeaks leaks plan) next memories frontier := by
  obtain ⟨physical, physicalTrace, _faithful, clear, same⟩ :=
    exists_clear_physical_of_native_consistent runtime leaks plan bounds ordered maximal inputs
      horizon scheduler players (NP) covered safe agreement trace consistent
  have receipts : execution.application.ReceiptsComplete := by
    have stateEq := congrArg (fun state : (N).Control => state.execution.application) same
    change execution.application = physical.execution.application.current.native at stateEq
    rw [stateEq]
    exact (clear_publicRecord runtime leaks plan bounds inputs horizon scheduler
      physicalTrace clear).receipts
  let joint : Player → Option (N).Action := fun _ => none
  have legal : ((N).protocol (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)).Legal
        (some ⟨remaining + 1, none, execution⟩) joint := by
    refine ⟨?_, fun _ => ?_⟩
    · change ¬(remaining + 1 = 0 ∧ (none : Option Player) = none)
      rintro ⟨impossible, _⟩
      omega
    · change ¬(none : Option Player) = some _
      simp
  have moved : some (⟨remaining, none, next⟩ : (N).Control) ∈
      ((N).transition (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)
          (some ⟨remaining + 1, none, execution⟩) joint).support := by
    change _ ∈ (((nativeScheduler runtime leaks plan scheduler) execution.environmentRecall
      (execution.observeEnvironment N)).bind fun command =>
        (execution.environmentStep N command).map fun updated =>
          some (⟨remaining, command.actor? N, updated⟩ : (N).Control)).support
    rw [PMF.mem_support_bind_iff]
    refine ⟨.application (.expire event), selected, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨next, supported, rfl⟩
  have nextTrace := trace.extend joint legal moved
  have nextConsistent : ∀ owner, ((NP) owner).Consistent (next.recall owner) := by
    intro owner
    rw [(N).environmentStep_recall execution next (.application (.expire event)) supported]
    exact consistent owner
  apply related.expire_of_no_publicFailure runtime (nativeLeaks leaks plan) execution next
    memories frontier receipts event supported
  intro owner acting
  exact not_publicFailure_of_native_consistent runtime leaks plan bounds ordered maximal inputs
    horizon scheduler players (NP) covered safe agreement nextTrace nextConsistent event owner
      acting

/-- The existing posterior-frontier execution engine yields the actual native
terminal-store law using only physical safety, local matching and the physical
all-legal-history completion contract. -/
theorem initial_terminal_store_of_physical_safety (bounds : MessageBounds graph)
  (ordered : graph.RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
  (players : Player → (P).Policy)
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
    (∀ who, ((NP) who).Consistent
      ((execution runtime leaks plan current.execution).recall who)) →
    ∀ who, current.actor = some who → (NP) who
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      nativePolicy runtime leaks plan (players who)
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who))
    (independent : graph.ReadyIndependent profile)
    (completes : PhaseService.CompletesPlay runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler)
    (initial : graph.Inputs) (supportedInitial : initial ∈ inputs.support) :
    ((N).runRounds (nativeScheduler runtime leaks plan scheduler) (NP) horizon
      (ReactiveApplication.Execution.initial N (State.initial initial))).map
        (fun next => next.application.config.store) =
      (graph.canonicalContinuation profile (Config.initial initial)).map
        (fun key => key.2.1) := by
  apply initial_terminal_store_of_expiry runtime (nativeLeaks leaks plan) ordered profile
    independent inputs horizon (nativeScheduler runtime leaks plan scheduler) (fun _ => True)
  · constructor <;> intros <;> trivial
  · intro remaining execution reached _valid consistent memories frontier _supported related
      event selected next supported
    obtain ⟨trace⟩ := reached
    exact frontier_expire_of_native_consistent runtime leaks plan profile bounds ordered maximal
      inputs horizon scheduler players covered safe agreement remaining execution trace consistent
        memories frontier related event selected next supported
  · intro current trace consistent terminal
    exact terminal_of_native_consistent runtime leaks plan bounds ordered maximal inputs horizon
      scheduler players (NP) covered safe agreement completes trace consistent terminal
  · exact supportedInitial
  · trivial

end Vegas.EventGraphRuntime.PhaseNativeProjection

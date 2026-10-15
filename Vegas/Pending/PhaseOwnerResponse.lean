/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOwnerOpportunity
import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.ReactiveOwnerOpportunity

/-! # Actual owner responses before a physical event deadline -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- A physical activation episode has an actual retained native response at
its original ready turn within the original opportunity bound. The native
history is reconstructed only from this actual clear counted history. -/
theorem owner_response_within_delay_of_activation (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (delay : graph.EventId → Nat)
    (opportunity : PhaseService.Opportunity runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler delay)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (idle : current.actor = none)
    (coordinate : CommitAttemptEvent graph) (owner : Player) (entered : Nat)
    (owned : graph.actor? coordinate.event = some owner)
    (activated : PhaseService.OwnerActivatedSince runtime leaks current.execution.environmentRecall
      coordinate owner entered) :
    ∃ before : (N).Control,
      Nonempty (((N).protocol (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)).Trace (some before)) ∧
      before.actor = some owner ∧
      ∃ response ∈ (execution runtime leaks plan current.execution).recall owner,
        response.beforeView = before.execution.observe N owner ∧
        before.execution.application.publicView.ownTurn? owner = some coordinate.event ∧
        before.execution.application.activatedAt coordinate.event = some entered ∧
        before.execution.application.clock ≤ entered + delay coordinate.event := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨activation, recorded, chosen, _attempt, ready, stamp, timely⟩ :=
    PhaseService.recorded_activation_within_delay runtime leaks _ horizon scheduler delay
      opportunity current raw coordinate owner entered owned activated
  have nativePrior := nativeTrace runtime leaks plan bounds ordered maximal inputs horizon scheduler
    trace (fun _ same => by cases same; exact clear)
  have nativeRecord : environmentEntry runtime leaks plan activation ∈
      (execution runtime leaks plan current.execution).environmentRecall :=
    List.mem_map.mpr ⟨activation, recorded, rfl⟩
  have nativeChosen : (environmentEntry runtime leaks plan activation).command =
      .activate owner := by
    change command runtime leaks plan activation.command = .activate owner
    rw [chosen]
    rfl
  obtain ⟨before, beforeTrace, acting, response, member, viewed, publicEq⟩ :=
    activated_owner_response_prefix runtime (nativeLeaks leaks plan) (inputs.map State.initial)
      horizon (nativeScheduler runtime leaks plan scheduler) (control runtime leaks plan current)
      nativePrior idle (environmentEntry runtime leaks plan activation) nativeRecord owner
      nativeChosen
  have publicState : before.execution.application.publicView =
      activation.beforeView.application.native := by
    simpa only [viewed, ReactiveApplication.Execution.observe, reactiveApplication,
      State.playerView, environmentEntry, environmentView] using publicEq
  refine ⟨before, beforeTrace, acting, response, member, viewed, ?_, ?_, ?_⟩
  · apply PublicView.ownTurn?_of_ownTurn
    apply State.ownTurn_of_ready _ ordered owner coordinate.event
    · rw [publicState]
      exact ready
    · exact owned
  · exact (congrArg (fun view => view.activatedAt coordinate.event) publicState).trans stamp
  · change before.execution.application.publicView.clock ≤ entered + delay coordinate.event
    rw [publicState]
    exact timely

/-- A due owned physical event already has a real owner response in the
protected emission window. Opportunity and timeliness are those of the actual
builder; no global native service contract is used. -/
theorem due_owner_response_prefix (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (delay bound : graph.EventId → Nat)
    (opportunity : PhaseService.Opportunity runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (idle : current.actor = none)
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (owned : graph.actor? event = some owner)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (stamp : current.execution.application.current.native.activatedAt event = some entered)
    (due : runtime.deadline event ≤ current.execution.application.current.native.clock - entered) :
    ∃ before : (N).Control,
      Nonempty (((N).protocol (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)).Trace (some before)) ∧
      before.actor = some owner ∧
      ∃ response ∈ (execution runtime leaks plan current.execution).recall owner,
        response.beforeView = before.execution.observe N owner ∧
        before.execution.application.publicView.ownTurn? owner = some event ∧
        before.execution.application.publicView.InclusionFitsDeadline runtime bound event := by
  have margin := timely event (by simp only [owned, Option.isSome_some])
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have activated := opportunity current raw event owner entered owned
    ((current.execution.application.current.native.publicView_eventReady event).mpr ready) stamp
      (by omega)
  obtain ⟨before, beforeTrace, acting, response, member, viewed, turn, beforeStamp, clock⟩ :=
    owner_response_within_delay_of_activation runtime leaks plan bounds ordered maximal inputs
      horizon scheduler delay opportunity current trace clear idle
      ⟨current.execution.application.attempt, event⟩ owner entered owned activated
  exact ⟨before, beforeTrace, acting, response, member, viewed, turn,
    PublicView.inclusionFitsDeadline_of_response_delay runtime delay bound timely
      before.execution.application.publicView event entered
      (by simp only [owned, Option.isSome_some]) beforeStamp clock⟩

end Vegas.EventGraphRuntime.PhaseNativeProjection

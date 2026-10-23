/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCurrentTokens
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.ReactiveEventStability

/-! # Pending binding assignments are hidden from a fresh current drawer -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- Signed unfinished binding packets are already physically ready by their
literal retained token. A same-owner pending assignment would therefore be
the very current coordinate, contradicting its actual unspent own recall.
This derives the hidden-frontier condition without a synthetic recall. -/
theorem phaseProposalBinding_pending_hidden
    (ordered : graph.RevealRelaxedOrdered)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (commitment : phase.kind = .commitment)
    (frontier : graph.Config)
    (earlier : ∀ event : graph.EventId, event.val < phase.low →
      event ∈ control.execution.application.current.native.config.cut.completed)
    (bounded : ∀ event ∈ frontier.cut.completed, event.val < phase.high)
    (origins : ∀ event ∈ frontier.cut.completed,
      event ∉ control.execution.application.current.native.config.cut.completed →
      event ∈ phase.events → (∃ message ∈ control.execution.network.inputs,
        message.payload.attempt = control.execution.application.attempt ∧
        message.payload.packet.call.event? graph = some event ∧
        graph.actor? event = some message.sender) ∨
      ∃ owner ∈ control.execution.application.current.excluded, graph.actor? event = some owner)
    (who : Player) (event : graph.EventId)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (actor : graph.actor? event = some who)
    (active : who ∉ control.execution.application.current.excluded)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩) :
    ∀ pending ∈ frontier.cut.completed,
      pending ∉ control.execution.application.current.native.config.cut.completed →
      ¬ graph.fieldVisibleTo who (.inr pending) := by
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have recalled := (app).history_inputRecall initial horizon scheduler raw
  intro pending completed missing visible
  have inside : pending ∈ phase.events := (phase.mem_events pending).mpr
    ⟨by by_contra below; exact missing (earlier pending (by omega)), bounded pending completed⟩
  have fields := phase.fields pending ((phase.mem_events pending).mp inside).1
    ((phase.mem_events pending).mp inside).2
  rw [commitment] at fields
  obtain ⟨owner, payload, binding⟩ := fields
  have same : owner = who := by
    simpa only [EventGraph.fieldVisibleTo, EventGraph.layout, fieldLayout, Sum.elim_inr, binding,
      EventField.VisibleTo] using visible
  have owned : graph.actor? pending = some who := by
    rw [← same]
    exact actor?_of_outputLayout_binding graph binding
  have emitted := origins pending completed missing inside
  rcases emitted with emitted | ⟨excluded, excludedOwner, excludedActor⟩
  swap
  · have sameOwner : excluded = who := Option.some.inj (excludedActor.symm.trans owned)
    exact active (sameOwner ▸ excludedOwner)
  obtain ⟨message, member, current, named, sender⟩ := emitted
  have authorized := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message member)).1
  have pendingReady := ready_of_current_authentic_token runtime leaks plan inputs horizon
    scheduler raw message member current authorized pending named missing
  have identical := ordered.ready_actor_unique _ ready pendingReady actor owned
  have authored : message ∈ (app).outputs (control.execution.recall who) := by
    rw [← recalled who]
    apply List.mem_filter.mpr
    refine ⟨member, ?_⟩
    have senderEq : message.sender = who := Option.some.inj (sender.symm.trans owned)
    simp only [senderEq, decide_true]
  apply unsent message authored
  simp only [PhaseCount.event?, named, Option.map_some, current, identical]

end Vegas

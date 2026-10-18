/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochActivationRecord
import Interaction.ReactiveRawRoundTrace

/-! # All-raw opportunity from bounded exogenous owner-mask gaps -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem initial_activation_state {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (draw : graph.Inputs) :
    ActivationState runtime leaks packetBudget tape draw
      (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan draw)) := by
  refine ⟨initial_progress_geometry plan ordered maximal draw, ?_, ?_⟩
  · refine ⟨(PhaseRuntimeState.initial_invariant plan draw).1, ?_⟩
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_div,
      Nat.zero_add] using initial_clock plan draw
  · intro owner coordinate entered cycle position _request _activated _older _atOwner _offered
      earlier
    change _ < 0 at earlier
    omega

theorem activation_state_exists_invariant {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (ordered : graph.RevealRelaxedOrdered) :
    (app).ServiceInvariant (family runtime leaks packetBudget tape)
      (fun execution => ∃ draw,
        ActivationState runtime leaks packetBudget tape draw execution) := by
  constructor
  · intro execution owner action valid
    obtain ⟨draw, valid⟩ := valid
    exact ⟨draw, (activation_state_invariant runtime leaks packetBudget tape ordered draw).respond
      execution owner action valid⟩
  · intro execution next selected valid chosen moved
    obtain ⟨draw, valid⟩ := valid
    exact ⟨draw, (activation_state_invariant runtime leaks packetBudget tape ordered
      draw).environment execution next selected valid chosen moved⟩

theorem activation_state_history {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks packetBudget tape)).Trace (some current)) :
    ∃ draw, ActivationState runtime leaks packetBudget tape draw current.execution := by
  apply (activation_state_exists_invariant runtime leaks packetBudget tape ordered).history
    (inputs.map (PhaseRuntimeState.initial plan)) horizon _ trace
  intro state supported
  rw [PMF.support_map] at supported
  obtain ⟨draw, _drawSupported, rfl⟩ := supported
  exact ⟨draw, initial_activation_state runtime leaks packetBudget tape plan ordered maximal draw⟩

theorem recorded_early_offer {length : Nat} (packetBudget cycles : Nat)
    (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) (execution : (app).Execution)
    (state : ActivationState runtime leaks packetBudget tape inputs execution)
    (bounded : execution.application.current.native.clock ≤ cycles)
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (acting : graph.actor? event = some owner)
    (ready : execution.application.current.native.publicView.EventReady event)
    (activated : execution.application.current.native.activatedAt event = some entered)
    (elapsed : entered + (activationGap + 1) < execution.application.current.native.clock) :
    ∃ entry ∈ execution.environmentRecall, entry.command = .activate owner ∧
      PhaseRuntimeState.requests entry.beforeView.application owner
        ⟨execution.application.attempt, event⟩ ∧
      entry.beforeView.application.native.EventReady event ∧
      entry.beforeView.application.native.activatedAt event = some entered ∧
      entry.beforeView.application.native.clock ≤ entered + activationGap := by
  have enteredBound : entered + 1 < cycles := by omega
  obtain ⟨cycle, lower, upper, offered⟩ := gaps.activation (entered + 1) enteredBound owner
  obtain ⟨position, atOwner⟩ := tape.owner_surjective cycle owner
  have cycleBefore : cycle < execution.application.current.native.clock := by omega
  have positionBound : packetBudget + position.val < cycleWidth (graph := graph) packetBudget := by
    unfold cycleWidth
    omega
  have targetBound : cycle * cycleWidth (graph := graph) packetBudget +
      (packetBudget + position.val) < (cycle + 1) * cycleWidth (graph := graph) packetBudget := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have scaled := Nat.mul_le_mul_right (cycleWidth (graph := graph) packetBudget)
    (Nat.succ_le_of_lt cycleBefore)
  change (cycle + 1) * cycleWidth (graph := graph) packetBudget ≤
    execution.application.current.native.clock * cycleWidth (graph := graph) packetBudget at scaled
  have cursorBound := Nat.div_mul_le_self execution.environmentRecall.length
    (cycleWidth (graph := graph) packetBudget)
  have cursorClock : execution.application.current.native.clock =
      execution.environmentRecall.length / cycleWidth (graph := graph) packetBudget := by
    simpa only [Nat.zero_add] using state.clock.2
  rw [← cursorClock] at cursorBound
  have earlier : cycle * cycleWidth (graph := graph) packetBudget +
      (packetBudget + position.val) < execution.environmentRecall.length := by omega
  have request := execution.application.request_of_ready ordered state.geometry.frontier
    state.geometry.live state.geometry.maximal state.geometry.quiescent event
      ((execution.application.current.native.publicView_eventReady event).mp ready) owner acting
  obtain ⟨entry, member, command, requestView, wasReady, stamp, atClock⟩ := state.recorded owner
    ⟨execution.application.attempt, event⟩ entered cycle position request activated (by omega)
      atOwner offered earlier
  exact ⟨entry, member, command, requestView, wasReady, stamp, by omega⟩

theorem opportunity_of_recorded {length : Nat} (packetBudget cycles : Nat)
    (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) (execution : (app).Execution)
    (state : ActivationState runtime leaks packetBudget tape inputs execution)
    (bounded : execution.application.current.native.clock ≤ cycles) :
    PhaseService.OpportunityAt runtime leaks execution (fun _ => activationGap + 1) := by
  intro event owner entered acting ready activated elapsed
  obtain ⟨entry, member, command, requestView, wasReady, stamp, _atClock⟩ :=
    recorded_early_offer runtime leaks packetBudget cycles tape activationGap processingGap gaps
      ordered inputs execution state bounded event owner entered acting ready activated elapsed
  exact ⟨entry, member, command, requestView.1.symm, wasReady, stamp⟩

theorem family_opportunity {length : Nat} (packetBudget cycles : Nat)
    (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : PMF graph.Inputs) :
    PhaseService.Opportunity runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (cycles * cycleWidth (graph := graph) packetBudget) (family runtime leaks packetBudget tape)
        (fun _ => activationGap + 1) := by
  intro current trace
  obtain ⟨draw, state⟩ := activation_state_history runtime leaks packetBudget tape plan ordered
    maximal inputs _ current trace
  have accounted := (app).raw_trace_horizon (inputs.map (PhaseRuntimeState.initial plan))
    (cycles * cycleWidth (graph := graph) packetBudget)
      (family runtime leaks packetBudget tape) trace
  have cursorBound : current.execution.environmentRecall.length ≤
      cycles * cycleWidth (graph := graph) packetBudget := by omega
  have divided : current.execution.environmentRecall.length /
      cycleWidth (graph := graph) packetBudget ≤
        (cycles * cycleWidth (graph := graph) packetBudget) /
          cycleWidth (graph := graph) packetBudget := Nat.div_le_div_right cursorBound
  have endDiv : cycles * cycleWidth (graph := graph) packetBudget /
      cycleWidth (graph := graph) packetBudget = cycles := by
    simpa only [Nat.add_zero] using cursor_div packetBudget cycles 0 (cycleWidth_pos packetBudget)
  rw [endDiv] at divided
  have bounded : current.execution.application.current.native.clock ≤ cycles := by
    rw [state.clock.2, Nat.zero_add]
    exact divided
  exact opportunity_of_recorded runtime leaks packetBudget cycles tape activationGap processingGap
    gaps ordered draw current.execution state bounded

end Vegas.EventGraphRuntime.ReservedEpoch

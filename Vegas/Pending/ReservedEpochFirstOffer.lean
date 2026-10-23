/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochOpportunity
import Vegas.Pending.ReservedEpochMixtureOpportunity
import Vegas.Pending.PhaseOncePolicy
import Vegas.Pending.PhaseActivationResponse

/-! # A genuine first response has a protected inclusion window -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem first_response_clock_bound_of_recorded {length : Nat} (packetBudget cycles : Nat)
    (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((app).protocol inputs horizon scheduler).Trace (some current))
    (draw : graph.Inputs)
    (state : ActivationState runtime leaks packetBudget tape draw current.execution)
    (bounded : current.execution.application.current.native.clock ≤ cycles)
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (request : current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩)
    (activated : current.execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨current.execution.application.attempt, event⟩ (current.execution.recall owner)) :
    current.execution.application.current.native.clock ≤ entered + (activationGap + 1) := by
  by_contra tooLate
  have elapsed : entered + (activationGap + 1) <
      current.execution.application.current.native.clock := by omega
  obtain ⟨entry, member, command, requestView, _wasReady, _stamp, atClock⟩ :=
    recorded_early_offer runtime leaks packetBudget cycles tape activationGap processingGap gaps
      ordered draw current.execution state bounded event owner entered request.2.2.2.1
        ((current.execution.application.current.native.publicView_eventReady event).mpr
          request.2.2.1) activated elapsed
  rcases PhaseService.activation_response_or_current runtime leaks inputs horizon scheduler
      current trace entry member owner command with responded | active
  · obtain ⟨response, recalled, view⟩ := responded
    apply first
    refine ⟨response, recalled, ?_⟩
    rw [view]
    exact requestView
  · have equal := congrArg (fun view : PhasePublicView graph => view.native.clock) active.2
    change current.execution.application.current.native.clock =
      entry.beforeView.application.native.clock at equal
    omega

theorem first_response_clock_bound {length : Nat} (packetBudget cycles : Nat)
    (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (cycles * cycleWidth (graph := graph) packetBudget)
        (family runtime leaks packetBudget tape)).Trace (some current))
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (request : current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩)
    (activated : current.execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨current.execution.application.attempt, event⟩ (current.execution.recall owner)) :
    current.execution.application.current.native.clock ≤ entered + (activationGap + 1) := by
  obtain ⟨draw, state⟩ := activation_state_history runtime leaks packetBudget tape plan ordered
    maximal inputs _ current trace
  have accounted := (app).raw_trace_horizon (inputs.map (PhaseRuntimeState.initial plan))
    (cycles * cycleWidth (graph := graph) packetBudget)
      (family runtime leaks packetBudget tape) trace
  have divided : current.execution.environmentRecall.length /
      cycleWidth (graph := graph) packetBudget ≤
        (cycles * cycleWidth (graph := graph) packetBudget) /
          cycleWidth (graph := graph) packetBudget := Nat.div_le_div_right (by omega)
  have endDiv : cycles * cycleWidth (graph := graph) packetBudget /
      cycleWidth (graph := graph) packetBudget = cycles := by
    simpa only [Nat.add_zero] using cursor_div packetBudget cycles 0 (cycleWidth_pos packetBudget)
  rw [endDiv] at divided
  have bounded : current.execution.application.current.native.clock ≤ cycles := by
    rw [state.clock.2, Nat.zero_add]
    exact divided
  exact first_response_clock_bound_of_recorded runtime leaks packetBudget cycles tape
    activationGap processingGap gaps ordered (inputs.map (PhaseRuntimeState.initial plan)) _
      (family runtime leaks packetBudget tape) current trace draw state bounded event owner
        entered request activated first

theorem first_response_protected {length : Nat} (packetBudget cycles : Nat)
    (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (cycles * cycleWidth (graph := graph) packetBudget)
        (family runtime leaks packetBudget tape)).Trace (some current))
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (request : current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩)
    (activated : current.execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨current.execution.application.attempt, event⟩ (current.execution.recall owner)) :
    current.execution.application.current.native.clock - entered + (processingGap + 1) <
      runtime.deadline event ∧
        current.execution.application.current.native.WithinDeadline runtime event := by
  have responseBound := first_response_clock_bound runtime leaks packetBudget cycles tape
    activationGap processingGap gaps plan ordered maximal inputs current trace event owner entered
      request activated first
  have slack := margin event (by rw [request.2.2.2.1]; rfl)
  change (activationGap + 1) + (processingGap + 1) < runtime.deadline event at slack
  refine ⟨by omega, ?_⟩
  simp only [State.WithinDeadline, activated]
  omega

end Vegas.EventGraphRuntime.ReservedEpoch

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochClock
import Vegas.Pending.PhaseNativeInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveResponseAccounting

/-! # Actual native clock accounting under reserved epochs -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def ClockAligned (packetBudget : Nat) (inputs : graph.Inputs) (origin : Nat)
    (execution : (app).Execution) : Prop :=
  execution.application.Invariant inputs ∧
    execution.application.current.native.clock = origin +
      execution.environmentRecall.length / cycleWidth (graph := graph) packetBudget

theorem clock_aligned_invariant {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (inputs : graph.Inputs) (origin : Nat) :
    (app).ServiceInvariant (family runtime leaks packetBudget tape)
      (ClockAligned runtime leaks packetBudget inputs origin) where
  respond execution owner response aligned := by
    refine ⟨(phaseApplication_invariant runtime leaks inputs).respond execution owner response
      aligned.1, ?_⟩
    rw [PhaseSeedCalendar.respond_clock runtime leaks execution aligned.1 owner response,
      (app).respond_environmentRecall]
    exact aligned.2
  environment execution next selected aligned supported reached := by
    refine ⟨(phaseApplication_invariant runtime leaks inputs).environmentStep execution next
      selected aligned.1 reached, ?_⟩
    have chosen := (family_support runtime leaks packetBudget tape execution.environmentRecall
      (execution.observeEnvironment app) selected).mp supported
    have clock := PhaseSeedCalendar.environmentStep_clock runtime leaks execution next
      selected aligned.1 reached
    rw [clock, chosen, command_ticks, aligned.2,
      (app).environmentStep_environmentRecall execution next selected reached,
      List.length_append, List.length_singleton, cycle_succ]
    omega

omit [Fintype Player] in
theorem initial_clock (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (PhaseRuntimeState.initial plan inputs).current.native.clock = 0 :=
  (PhaseRuntimeState.settle_physical plan.phases 0
    ⟨State.initial inputs, ∅⟩ ⟨State.initial inputs, ∅⟩ []).2.2

theorem clock_history {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (control : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks packetBudget tape)).Trace (some control)) :
    control.execution.application.current.native.clock =
      control.execution.environmentRecall.length / cycleWidth (graph := graph) packetBudget := by
  have invariant : (app).ServiceInvariant (family runtime leaks packetBudget tape)
      (fun execution => ∃ draw, ClockAligned runtime leaks packetBudget draw 0 execution) := by
    constructor
    · intro execution owner response valid
      obtain ⟨draw, aligned⟩ := valid
      exact ⟨draw, (clock_aligned_invariant runtime leaks packetBudget tape draw 0).respond
        execution owner response aligned⟩
    · intro execution next selected valid supported reached
      obtain ⟨draw, aligned⟩ := valid
      exact ⟨draw, (clock_aligned_invariant runtime leaks packetBudget tape draw 0).environment
        execution next selected aligned supported reached⟩
  have initialized : ∀ state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support,
      ∃ draw, ClockAligned runtime leaks packetBudget draw 0
        (ReactiveApplication.Execution.initial app state) := by
    intro state supported
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨draw, (PhaseRuntimeState.initial_invariant plan draw).1, ?_⟩
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_div,
      Nat.add_zero] using initial_clock plan draw
  obtain ⟨draw, _valid, clock⟩ := invariant.history _ horizon initialized trace
  simpa only [Nat.zero_add] using clock

end Vegas.EventGraphRuntime.ReservedEpoch

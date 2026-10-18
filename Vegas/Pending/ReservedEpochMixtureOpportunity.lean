/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochOpportunity
import Interaction.ReactiveServiceMixture

/-! # Owner opportunity under the actual behavioral correlated-tape scheduler -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem implementation_activation_state_history {length : Nat} (packetBudget : Nat)
    (prior : PMF (Tape Player length))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : PMF graph.Inputs)
    (horizon : Nat) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (implementation runtime leaks packetBudget prior).scheduler).Trace (some current)) :
    ∃ tape ∈ prior.support, ∃ draw,
      ActivationState runtime leaks packetBudget tape draw current.execution := by
  let predicate := fun (tape : Tape Player length) (execution : (app).Execution) =>
    tape ∈ prior.support ∧ ∃ draw, ActivationState runtime leaks packetBudget tape draw execution
  have seeded : ∀ tape, (app).ServiceInvariant (family runtime leaks packetBudget tape)
      (predicate tape) := by
    intro tape
    constructor
    · intro execution owner action valid
      exact ⟨valid.1, (activation_state_exists_invariant runtime leaks packetBudget tape
        ordered).respond execution owner action valid.2⟩
    · intro execution next selected valid chosen moved
      exact ⟨valid.1, (activation_state_exists_invariant runtime leaks packetBudget tape
        ordered).environment execution next selected valid.2 chosen moved⟩
  have invariant := ReactiveApplication.ServiceInvariant.schedulerMixture app prior
    (family runtime leaks packetBudget) predicate seeded
  have actual := invariant.history (inputs.map (PhaseRuntimeState.initial plan))
    horizon (fun state supported => by
      rw [PMF.support_map] at supported
      obtain ⟨draw, _drawSupported, rfl⟩ := supported
      intro tape original
      change tape ∈ prior.support at original
      exact ⟨original, draw,
        initial_activation_state runtime leaks packetBudget tape plan ordered maximal draw⟩) trace
  obtain ⟨tape, supported⟩ := ((implementation runtime leaks packetBudget prior).posterior
    current.execution.environmentRecall).support_nonempty
  obtain ⟨original, draw, state⟩ := actual tape supported
  exact ⟨tape, original, draw, state⟩

theorem implementation_opportunity {length : Nat} (packetBudget cycles : Nat)
    (prior : PMF (Tape Player length)) (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support, tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : PMF graph.Inputs) :
    PhaseService.Opportunity runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (cycles * cycleWidth (graph := graph) packetBudget)
        (implementation runtime leaks packetBudget prior).scheduler
          (fun _ => activationGap + 1) := by
  intro current trace
  obtain ⟨tape, original, draw, state⟩ := implementation_activation_state_history runtime leaks
    packetBudget prior plan ordered maximal inputs _ current trace
  have accounted := (app).raw_trace_horizon (inputs.map (PhaseRuntimeState.initial plan))
    (cycles * cycleWidth (graph := graph) packetBudget)
      (implementation runtime leaks packetBudget prior).scheduler trace
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
    (gaps tape original) ordered draw current.execution state bounded

end Vegas.EventGraphRuntime.ReservedEpoch

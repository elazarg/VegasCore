/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochExhaustion
import Vegas.Pending.ReservedEpochTraceDelivery
import Interaction.ReactiveAnchoredTrace

/-! # Semantic completion at the derived physical execution horizon -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def packetCapacity : Nat := submissionBudget (Player := Player) (completionCycles runtime)

def executionHorizon : Nat := horizon (graph := graph) (completionCycles runtime)

/-- Completion applies to an actual raw terminal history under an arbitrary
initial private-input law. No prescribed player profile is assumed. -/
theorem terminal_history_complete {length : Nat} (tape : Tape Player length)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) (family runtime leaks (packetCapacity runtime) tape)).Trace
        (some current)) (terminal : (app).terminal (some current)) :
    current.execution.application.phases = [] ∧
      current.execution.application.current.native.config.cut.completed = Finset.univ := by
  rcases current with ⟨remaining, actor, execution⟩
  obtain ⟨rfl, rfl⟩ := terminal
  let players : Player → (app).Policy := fun _ => (app).silentPolicy
  obtain ⟨_bounded, supported⟩ := ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace
    (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
      (family runtime leaks (packetCapacity runtime) tape) players trace
  change execution ∈ ((inputs.map (PhaseRuntimeState.initial plan)).bind fun state =>
    (app).runRounds (family runtime leaks (packetCapacity runtime) tape)
      ((app).anchoredPolicy execution players) (executionHorizon runtime)
        (ReactiveApplication.Execution.initial app state)).support at supported
  obtain ⟨state, initialized, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  rw [PMF.support_map] at initialized
  obtain ⟨draw, _drawSupported, rfl⟩ := initialized
  exact runRounds_complete runtime leaks (packetCapacity runtime) tape plan ordered maximal
    ((app).anchoredPolicy execution players) draw execution reached

theorem family_completesPlay {length : Nat} (tape : Tape Player length)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : PMF graph.Inputs) :
    PhaseService.CompletesPlay runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) (family runtime leaks (packetCapacity runtime) tape) := by
  intro current trace terminal
  exact (terminal_history_complete runtime leaks tape plan ordered maximal inputs current trace
    terminal).2

/-- The actual behavioral mixture terminates under every legal raw history.
The proof extracts a supported original tape through the anchored run law. -/
theorem implementation_completesPlay {length : Nat} (prior : PMF (Tape Player length))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : PMF graph.Inputs) :
    PhaseService.CompletesPlay runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime)
        (implementation runtime leaks (packetCapacity runtime) prior).scheduler := by
  intro current trace terminal
  rcases current with ⟨remaining, actor, execution⟩
  obtain ⟨rfl, rfl⟩ := terminal
  let players : Player → (app).Policy := fun _ => (app).silentPolicy
  obtain ⟨_bounded, supported⟩ := ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace
    (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
      (implementation runtime leaks (packetCapacity runtime) prior).scheduler players trace
  change execution ∈ ((inputs.map (PhaseRuntimeState.initial plan)).bind fun state =>
    (app).runRounds (implementation runtime leaks (packetCapacity runtime) prior).scheduler
      ((app).anchoredPolicy execution players) (executionHorizon runtime)
        (ReactiveApplication.Execution.initial app state)).support at supported
  obtain ⟨state, initialized, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  rw [PMF.support_map] at initialized
  obtain ⟨draw, _drawSupported, rfl⟩ := initialized
  rw [← realize runtime leaks (packetCapacity runtime) prior] at reached
  obtain ⟨tape, _tapeSupported, fixed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  exact (runRounds_complete runtime leaks (packetCapacity runtime) tape plan ordered maximal
    ((app).anchoredPolicy execution players) draw execution fixed).2

end Vegas.EventGraphRuntime.ReservedEpoch

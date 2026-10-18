/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochReceiptContract

/-! # Raw receipt coverage under the actual correlated behavioral scheduler -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem implementation_idle_emission_receipt {length : Nat} (cycles : Nat)
    (prior : PMF (Tape Player length)) (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support, tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (remaining : Nat) (execution : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
        (implementation runtime leaks
          (submissionBudget (Player := Player) cycles) prior).scheduler).Trace
          (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : (app).PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (message : Message Player (app).Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.1.publicView.clock + (processingGap + 1) <
      execution.application.current.native.clock) :
    ∃ accepted, (message.id, accepted) ∈ execution.receipts := by
  let capacity := submissionBudget (Player := Player) cycles
  let fallback : Player → (app).Policy := fun _ => (app).silentPolicy
  let players := (app).anchoredPolicy execution fallback
  let used := horizon (graph := graph) cycles - remaining
  obtain ⟨bounded, supported⟩ := ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace
    (inputs.map (PhaseRuntimeState.initial plan)) (horizon (graph := graph) cycles)
      (implementation runtime leaks capacity prior).scheduler fallback trace
  change execution ∈ ((inputs.map (PhaseRuntimeState.initial plan)).bind fun state =>
    (app).runRounds (implementation runtime leaks capacity prior).scheduler players used
      (ReactiveApplication.Execution.initial app state)).support at supported
  obtain ⟨state, initialized, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  rw [PMF.support_map] at initialized
  obtain ⟨draw, _drawSupported, rfl⟩ := initialized
  rw [← realize runtime leaks capacity prior] at reached
  obtain ⟨tape, original, fixed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have rounds : execution ∈ ((app).roundsFrom (PMF.pure (PhaseRuntimeState.initial plan draw))
      (family runtime leaks capacity tape) players used).support := by
    simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind] using fixed
  obtain ⟨fixedTrace⟩ := (app).raw_trace_roundsFrom (PMF.pure (PhaseRuntimeState.initial plan draw))
    (horizon (graph := graph) cycles) (family runtime leaks capacity tape) players used
      (Nat.sub_le _ _) execution rounds
  have distance : horizon (graph := graph) cycles - used = remaining := by dsimp [used]; omega
  rw [distance] at fixedTrace
  have actualTrace : ((app).protocol ((PMF.pure draw).map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles) (family runtime leaks capacity tape)).Trace
        (some ⟨remaining, none, execution⟩) := by
    rw [PMF.pure_map]
    exact fixedTrace
  exact idle_emission_receipt runtime leaks cycles tape activationGap processingGap
    (gaps tape original) plan (PMF.pure draw) remaining execution actualTrace owner entry recorded
      message emitted elapsed

theorem implementation_emission_receipt {length : Nat} (cycles : Nat)
    (prior : PMF (Tape Player length)) (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support, tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
        (implementation runtime leaks
          (submissionBudget (Player := Player) cycles) prior).scheduler).Trace
          (some current))
    (owner : Player) (entry : (app).PlayerEntry)
    (recorded : entry ∈ current.execution.recall owner)
    (message : Message Player (app).Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.1.publicView.clock + (processingGap + 1) <
      current.execution.application.current.native.clock) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts := by
  apply emission_receipt_of_idle runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
    (horizon (graph := graph) cycles) (processingGap + 1)
      (implementation runtime leaks (submissionBudget (Player := Player) cycles) prior).scheduler
        _ current trace owner entry recorded message emitted elapsed
  intro remaining execution localTrace who remembered member envelope sent old
  exact implementation_idle_emission_receipt runtime leaks cycles prior activationGap processingGap
    gaps plan inputs remaining execution localTrace who remembered member envelope sent old

theorem implementation_protectedInclusion {length : Nat} (cycles : Nat)
    (prior : PMF (Tape Player length)) (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support, tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) :
    PhaseService.ProtectedInclusion runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
        (implementation runtime leaks (submissionBudget (Player := Player) cycles) prior).scheduler
          (fun _ => processingGap + 1) := by
  intro current trace coordinate owner _acting earlier later entry message recalled emitted
    _sender _attempt _event _ready _sole _current _unfinished elapsed
  apply implementation_emission_receipt runtime leaks cycles prior activationGap processingGap gaps
    plan inputs current trace owner entry _ message emitted elapsed
  rw [recalled]
  exact List.mem_append_right _ List.mem_cons_self

end Vegas.EventGraphRuntime.ReservedEpoch

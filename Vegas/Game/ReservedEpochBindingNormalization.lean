/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochPhaseBindingFrame

/-! # Paired actual normalization while a foreign binding chain remains unfinished -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem normalize_binding_pair_unfinished (left right : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (installed : phase ∈ left.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (leftValid : left.current.native.Invariant inputs)
    (rightValid : right.current.native.Invariant inputs) (owner : Player)
    (survivor : owner ∉ left.current.excluded)
    (frame : BindingFrame program owner left.current.native right.current.native)
    (phases : left.phases = right.phases)
    (excluded : left.current.excluded = right.current.excluded)
    (unfinished : ∃ event ∈ phase.events, (graph).actor? event = some owner ∧
      event ∉ left.current.native.config.cut.completed) :
    BindingFrame program owner left.normalize.current.native right.normalize.current.native ∧
      left.normalize.phases = left.phases ∧ right.normalize.phases = right.phases ∧
      left.normalize.generation = left.generation ∧ right.normalize.generation = right.generation ∧
      left.normalize.current.excluded = left.current.excluded ∧
      right.normalize.current.excluded = right.current.excluded := by
  have rightInstalled : phase ∈ right.phases.head? := by
    simpa only [← phases] using installed
  have rightSurvivor : owner ∉ right.current.excluded := by
    simpa only [← excluded] using survivor
  have rightUnfinished : ∃ event ∈ phase.events, (graph).actor? event = some owner ∧
      event ∉ right.current.native.config.cut.completed := by
    obtain ⟨event, inside, actor, absent⟩ := unfinished
    obtain ⟨low, high⟩ := (phase.mem_events event).mp inside
    obtain ⟨who, payload, typed⟩ := by
      simpa only [commitment] using phase.fields event low high
    have sameOwner : who = owner := Option.some.inj
      (((graph).actor?_of_outputLayout_binding typed).symm.trans actor)
    subst who
    refine ⟨event, inside, actor, ?_⟩
    have output := frame.ownerOutputs event payload typed
    intro completed
    apply absent
    rw [← left.current.native.config.output_available event, output]
    exact (right.current.native.config.output_available event).mpr completed
  have first := normalize_unfinished_owner_frame program left phase installed commitment inputs
    leftValid owner survivor unfinished
  have second := normalize_unfinished_owner_frame program right phase rightInstalled commitment
    inputs rightValid owner rightSurvivor rightUnfinished
  have firstEq := normalize_eq_drain_of_unfinished_owner program left phase installed owner
    survivor unfinished
  have secondEq := normalize_eq_drain_of_unfinished_owner program right phase rightInstalled owner
    rightSurvivor rightUnfinished
  refine ⟨first.symm.trans (frame.trans second), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [firstEq]
  · rw [secondEq]
  · rw [firstEq]
  · rw [secondEq]
  · rw [firstEq]
    exact phase.drain_excluded left.current
  · rw [secondEq]
    exact phase.drain_excluded right.current

end Vegas.EventGraphRuntime.ReservedEpoch

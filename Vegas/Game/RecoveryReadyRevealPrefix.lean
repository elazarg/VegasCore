/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitPrefixWitness
import Vegas.Game.CompiledRevealLayout

/-! # Static source disclosure prefixes at actual ready publication cuts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A ready publication in the installed disclosure interval has an exact
source coordinate and a source reveal prefix through that coordinate. Earlier
independent publications need not have completed physically. -/
theorem RecoverySourceCheckpoint.ready_reveal_prefix
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (frontier : state.Frontier)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .reveal)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (ready : state.current.native.config.cut.Ready event) :
    ∃ selected : Fin (eventCount checkpoint.residual.tail),
      checkpoint.embedding.event selected = event ∧
      ∀ count, count ≤ selected.val + 1 → RevealPrefix checkpoint.residual.tail count := by
  obtain ⟨selected, selectedEq⟩ := checkpoint.native_event_index frontier event ready
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have interval := (phase.mem_events event).mp inside
  refine ⟨selected, selectedEq, fun count before => ?_⟩
  apply RevealPrefix.of_outputLayout count checkpoint.residual.tail (by omega)
  intro index below
  have typed := phase.fields (checkpoint.embedding.event index)
    (by rw [checkpoint.compiled.rankEq, low]; omega)
    (by have rank := checkpoint.compiled.rankEq selected
        rw [selectedEq, low] at rank
        rw [checkpoint.compiled.rankEq, low]; omega)
  rw [kind] at typed
  obtain ⟨payload, publication⟩ := typed
  have layout : outputLayout checkpoint.residual.tail index = .publication payload :=
    (checkpoint.embedding.layout_eq index).symm.trans publication
  rw [layout]
  trivial

end Vegas

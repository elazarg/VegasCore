/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryCommitPrefixWitness
import Vegas.Compile.CommitPrefixAtEvent

/-! # Typed source predecessor prefixes selected by ready physical bindings -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The actual phase interval and binding layout select the exact typed source
predecessor prefix within the same saved checkpoint. -/
theorem RecoverySourceCheckpoint.ready_binding_prefix
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (frontier : state.Frontier)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (ready : state.current.native.config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload) :
    ∃ selected : Fin (eventCount checkpoint.residual.tail),
      checkpoint.embedding.event selected = event ∧
      ∃ (Δ : SourceCtx Player L) (P : Finset VarId) (name : VarId)
        (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ who name payload)
        (next : SourceProgram Player L ((name, .commitment who payload) :: Δ) (insert name P))
        (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names
          Δ P),
        selected.val = earlier.length ∧
          earlier.prepend (.commit name who fresh guard next) = checkpoint.residual.tail := by
  obtain ⟨selected, selectedEq⟩ := checkpoint.native_event_index frontier event ready
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have interval := (phase.mem_events event).mp inside
  have bindings : ∀ index : Fin (eventCount checkpoint.residual.tail),
      index.val ≤ selected.val →
        ∃ owner value, outputLayout checkpoint.residual.tail index = .binding owner value := by
    intro index before
    have typed := phase.fields (checkpoint.embedding.event index)
      (by rw [checkpoint.compiled.rankEq, low]; omega)
      (by have rank := checkpoint.compiled.rankEq selected
          rw [selectedEq, low] at rank
          rw [checkpoint.compiled.rankEq, low]; omega)
    rw [kind] at typed
    obtain ⟨owner, value, layout⟩ := typed
    exact ⟨owner, value, (checkpoint.embedding.layout_eq index).symm.trans layout⟩
  have layout : outputLayout checkpoint.residual.tail selected = .binding who payload :=
    (checkpoint.embedding.layout_eq selected).symm.trans (selectedEq.symm ▸ binding)
  obtain ⟨Δ, P, name, fresh, guard, next, earlier, atEnd, reconstruct⟩ :=
    exists_commitPrefix_at_binding checkpoint.residual.tail selected who payload bindings layout
  exact ⟨selected, selectedEq, Δ, P, name, fresh, guard, next, earlier, atEnd.symm, reconstruct⟩

end Vegas

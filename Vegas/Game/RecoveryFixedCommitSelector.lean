/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryBindingPrefix
import Vegas.Compile.CommitPrefixBindingSplit

/-! # Actual ready bindings select the same saved source-word block -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime
  Interaction GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A ready actual binding selects its exact typed instruction inside the
given saved commitment block. The ORIGINAL block and its word prior are retained. -/
theorem RecoverySourceCheckpoint.fixed_binding_prefix
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (frontier : state.Frontier)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining)
    (high : phase.high = phase.low + block.length)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (ready : state.current.native.config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload) :
    ∃ selected : Fin (eventCount checkpoint.residual.tail),
      checkpoint.embedding.event selected = event ∧
      ∃ (Ξ : SourceCtx Player L) (Q : Finset VarId) (name : VarId)
        (fresh : name ∉ Ξ.map Prod.fst) (guard : SourceGuard L Ξ who name payload)
        (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names
          Ξ Q)
        (later : SourceProgram.CommitPrefix ((name, .commitment who payload) :: Ξ)
          (insert name Q) Δ P),
        earlier.length = selected.val ∧
          earlier.append (.commit name who fresh guard later) = block ∧
          earlier.prepend (.commit name who fresh guard (later.prepend suffix)) =
            checkpoint.residual.tail := by
  obtain ⟨selected, selectedEq⟩ := checkpoint.native_event_index frontier event ready
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have interval := (phase.mem_events event).mp inside
  have rank := checkpoint.compiled.rankEq selected
  rw [selectedEq, low] at rank
  have bounded : selected.val < block.length := by omega
  let chosen : Fin (eventCount (block.prepend suffix)) :=
    cast (congrArg (fun program => Fin (eventCount program)) reconstruct.symm) selected
  have castInfo {Γ' : SourceCtx Player L} {O' : Finset VarId}
      (first second : SourceProgram Player L Γ' O') (same : first = second)
      (index : Fin (eventCount second)) :
      (cast (congrArg (fun program => Fin (eventCount program)) same.symm) index).val = index.val ∧
        outputLayout first
          (cast (congrArg (fun program => Fin (eventCount program)) same.symm) index) =
            outputLayout second index := by
    cases same
    exact ⟨rfl, rfl⟩
  have castEq := castInfo (block.prepend suffix) checkpoint.residual.tail reconstruct selected
  have chosenVal : chosen.val = selected.val := castEq.1
  have layout : outputLayout (block.prepend suffix) chosen = .binding who payload :=
    castEq.2.trans ((checkpoint.embedding.layout_eq selected).symm.trans
      (selectedEq.symm ▸ binding))
  obtain ⟨Ξ, Q, name, fresh, guard, earlier, later, size, sameBlock⟩ :=
    block.binding_split_of_layout suffix chosen (by omega) who payload layout
  refine ⟨selected, selectedEq, Ξ, Q, name, fresh, guard, earlier, later,
    size.trans chosenVal, sameBlock, ?_⟩
  calc
    _ = (earlier.append (.commit name who fresh guard later)).prepend suffix :=
      (earlier.prepend_append (.commit name who fresh guard later) suffix).symm
    _ = block.prepend suffix := congrArg (fun segment => segment.prepend suffix) sameBlock
    _ = checkpoint.residual.tail := reconstruct

end Vegas

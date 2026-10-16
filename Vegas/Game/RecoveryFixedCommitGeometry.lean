/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryFixedCommitSelector
import Vegas.Game.CompiledCommitMaximality

/-! # The physical head is the given maximal source commitment block -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The same saved source block fixes the actual commitment descriptor's
upper boundary. This follows from the compiled suffix and actual maximal
descriptor geometry, without choosing a new source checkpoint or prior. -/
theorem RecoverySourceCheckpoint.commit_block_phase_geometry
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (positive : 0 < block.length) (boundary : IsCommitBoundary suffix)
    (frontier : state.Frontier)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) :
    phase.kind = .commitment ∧ phase.high = phase.low + block.length := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, aligned, agree, guards, failures, unique, ranks, actors, commits, owners, endpoints,
    automatic, history, memory, steps, menus, readout, sourceTrace, views, historyAlignment, origin⟩
  dsimp only at block
  change block.prepend suffix = program at reconstruct
  subst program
  have low : phase.low = state.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have adjacent := frontier.adjacent
  have last := frontier.last
  rw [installed] at adjacent last maximal
  have same := compiledCommitPhase_eq_of_maximal setup.program mode block suffix embedding
    compiled positive boundary phase remaining adjacent last maximal low
  rw [same]
  exact ⟨rfl, rfl⟩

end Vegas

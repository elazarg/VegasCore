/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Game.CompiledCommitControl
import Vegas.Game.CompiledCommitExclusionWord
import GameTheory.Protocol.Backward

/-! # Complete information on chosen decoded commitment continuations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


/-- The maximal native commitment descriptor identifies every original
slot of the checkpoint's decoded source block, independently of its values. -/
theorem RecoverySourceCheckpoint.commit_phase_geometry
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (frontier : state.Frontier)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    match commitPhase checkpoint.residual.tail with
    | ⟨_, _, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      block.length = phase.high - phase.low ∧
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ phase.events := by
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  have committing := checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations
    checkpoint.registry checkpoint.embedding checkpoint.before state.attempt.phase
    phase kind low checkpoint.source
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, beforeRefs,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, priorTrace, views,
    historyAlignment, origin⟩
  dsimp only at committing ⊢
  generalize decomposition : commitPhase program = segment at ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [CommitPrefix.length]; omega
  have adjacent := frontier.adjacent
  have last := frontier.last
  rw [installed] at adjacent last maximal
  have same := compiledCommitPhase_eq_of_maximal setup.program mode block suffix embedding
    compiled positive boundary phase remaining adjacent last maximal low
  rw [same]
  constructor
  · change block.length = (state.attempt.phase + block.length) - state.attempt.phase
    omega
  · intro index bound
    apply (RuntimePhase.mem_events _ _).mpr
    change state.attempt.phase ≤ (embedding.event index).val ∧
      (embedding.event index).val < state.attempt.phase + block.length
    rw [compiled.rankEq]
    omega

/-- The actual saved record and native extension determine the entire
chosen commitment exclusion word. No equality of hidden entries is needed. -/
theorem RecoverySourceCheckpoint.commit_exclusion_scan [Fintype Player]
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (archives : state.ArchivedExclusions)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
    (extension : state.entry.native.PublicFailureExtension native)
    (completed : match commitPhase checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ native.config.cut.completed) :
    checkpoint.commitExclusionWord native =
      (List.range (checkpoint.commitInstructionWord native).length).map (fun index =>
        PhaseRuntimeState.archivedFailureOwners state.retired ∪
          native.failureOwnersBefore (state.attempt.phase + index + 1)) := by
  have before : state.entry.excluded =
      PhaseRuntimeState.archivedFailureOwners state.retired ∪
        native.failureOwnersBefore state.attempt.phase := by
    rw [archives.saved_eq, ← extension.failureOwnersBefore_eq state.attempt.phase saved]
  dsimp only [RecoverySourceCheckpoint.commitExclusionWord,
    RecoverySourceCheckpoint.commitInstructionWord]
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, beforeRefs,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, priorTrace, views,
    historyAlignment, origin⟩
  dsimp only at completed ⊢
  generalize decomposition : commitPhase program = segment at completed ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only at completed ⊢
  rw [CommitPrefix.Attempt.joints_length]
  exact decodeCommitAttempt_exclusionWord_scan setup.program mode block suffix embedding native
    state.attempt.phase compiled.rankEq completed source state.entry.excluded
    (PhaseRuntimeState.archivedFailureOwners state.retired) before

end Vegas

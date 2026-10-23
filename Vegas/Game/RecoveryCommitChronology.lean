/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryResidualUniqueness
import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Source.CommitRecoveryObservedMemory
import Vegas.Game.CompiledCommitHead
import Vegas.Source.CommitRecoveryCommitWindow
import Vegas.Pending.ArchiveBindingRecord
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.PhaseArchivedOwnPrefix
import Vegas.Pending.PhaseArchivedObservation
import Vegas.Game.CompiledCommitMaximality
import Vegas.Game.CompiledCommitControl
import Vegas.Game.CompiledCommitExclusionWord
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseRetiredCompletion
import Vegas.Source.CommitRecoveryOwnHistory
import Vegas.Source.CommitRecoveryClearRecall
import Vegas.Source.CommitRecoveryControl
import GameTheory.Protocol.Backward

/-! # Complete information on chosen decoded commitment continuations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


private theorem clear_of_initial_control
    (setup : Setup (Player := Player) (L := L))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (initial : setup.commitRecoveryControl state = 1) : setup.CommitRecoveryClear state := by
  cases trace with
  | start => trivial
  | @extend before after prior joint legal supported =>
      cases before with
      | none =>
          obtain ⟨draw, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          rfl
      | some previous =>
          have strict := setup.commitRecoveryControl_step joint legal supported
          have positive : 0 < setup.commitRecoveryControl (some previous) :=
            Nat.zero_lt_succ _
          omega

/-- The initial public address and generation force a genuine checkpoint to precede
all source instructions, so its saved source exclusion is empty. -/
theorem RecoverySourceCheckpoint.initial_clear
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : state.attempt.phase = 0) (generation : state.generation = 0) :
    setup.CommitRecoveryClear (some (CommitRecoveryState.atPoint
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
        state.entry.excluded state.generation)) := by
  apply clear_of_initial_control setup checkpoint.trace
  have position := checkpoint.saved_position
  rw [phase] at position
  simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control,
    CommitRecoveryState.atPoint, generation, Nat.zero_mul, Nat.zero_add, position]

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

/-- An actual completed member commitment phase identifies the saved typed block
and supplies all of its native completion witnesses. -/
theorem RecoverySourceCheckpoint.completed_commit_phase
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (member : phase ∈ plan.phases) (kind : phase.kind = .commitment)
    (low : phase.low = state.attempt.phase) (who : Player)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (completed : ∀ event ∈ phase.events, event ∈ native.config.cut.completed) :
    ProtocolState.atCommit checkpoint.residual.tail
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true ∧
      (match commitPhase checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ native.config.cut.completed) := by
  have total := checkpoint.compiled.countEq
  have bounded := phase.bounded
  have nonempty := phase.nonempty
  change phase.high ≤ eventCount setup.program at bounded
  have positive : 0 < eventCount checkpoint.residual.tail := by omega
  let zero : Fin (eventCount checkpoint.residual.tail) := ⟨0, positive⟩
  have ranked : (checkpoint.embedding.event zero).val = state.attempt.phase := by
    simpa only [zero, Nat.add_zero] using checkpoint.compiled.rankEq zero
  have headBinding := phase.fields (checkpoint.embedding.event zero) (by omega) (by omega)
  rw [kind] at headBinding
  obtain ⟨owner, payload, layout⟩ := headBinding
  change outputLayout setup.program (checkpoint.embedding.event zero) = .binding owner payload
    at layout
  have decoded := ProtocolViewSuffix.decode_entry setup.program checkpoint.residual.tail
    checkpoint.refs checkpoint.embedding checkpoint.residual.lift checkpoint.views positive who
    checkpoint.source state.entry.native.config.store checkpoint.agrees
  have headCommit := decodeEventView?_atCommit setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who (checkpoint.embedding.event zero)
    ((toEventGraph setup.program).playerStore who state.entry.native.config.store)
    (checkpoint.source.history who) _ decoded owner payload layout
  have committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true := by
    simpa only [ProtocolState.atCommit_observe, checkpoint.atCommit] using headCommit
  refine ⟨committing, ?_⟩
  obtain ⟨prior, remaining, installed⟩ := List.mem_iff_append.mp member
  have suffixProof : phase :: remaining <:+ plan.phases := ⟨prior, installed.symm⟩
  obtain ⟨adjacent, last, maximalTail⟩ := plan.suffix_geometry maximal _ suffixProof
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, trace, views,
    historyAlignment, origin⟩
  dsimp only at ⊢
  generalize decomposition : commitPhase program = segment
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only
  have blockPositive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit name owner fresh guard rest => simp only [CommitPrefix.length]; omega
  have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block suffix
    embedding compiled blockPositive boundary phase remaining adjacent last maximalTail low
  intro index earlier
  apply completed
  rw [phaseEq, RuntimePhase.mem_events]
  have rank := compiled.rankEq index
  change state.attempt.phase ≤ (embedding.event index).val ∧
    (embedding.event index).val < state.attempt.phase + block.length
  omega

end Vegas

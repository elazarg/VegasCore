/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Game.RecoverySourceBoundary
import Vegas.Game.CompiledCommitClosing
import Vegas.Game.CompiledCommitTail
import Vegas.Game.CompiledCommitMaximality
import Vegas.Source.CommitRecoveryBlockCloseLift

/-! # Actual source checkpoints at commitment-phase retries -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A physical retry restores the source semantic checkpoint and retains the
actual effective private action history. The new checkpoint is reached by
legal source recovery instructions, not supplied as a simulation premise. -/
theorem RecoverySourceCheckpoint.after_commit_retry
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (binding : state.BindingRecord) (receipts : state.ReceiptRecord)
    (stored : state.StoredCheckpoint) (finished : phase.Finished (phase.drain state.current))
    (missed : (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty) :
    Nonempty (RecoverySourceCheckpoint setup mode state.normalize) := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, aligned, agree, guards, failures, unique, ranks, actors, commits, owners, endpoints,
    automatic, history, memory, steps, menus, readout, sourceTrace⟩
  obtain ⟨Δ, P, suffix, block, reconstruct, boundary⟩ := commitPhase program
  subst program
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [SourceProgram.CommitPrefix.length]; omega
  have low : phase.low = state.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have adjacent := receipts.exclusion.frontier.adjacent
  have last := receipts.exclusion.frontier.last
  rw [installed] at adjacent last maximal
  have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block suffix embedding
    compiled positive boundary phase remaining adjacent last maximal low
  subst phase
  let phase := compiledCommitPhase setup.program mode block suffix embedding compiled positive
  have ownerEq : phase.owners = block.owners :=
    compiledCommitPhase_owners setup.program mode block suffix embedding compiled positive
  have missedSource : ((phase.drain state.current).excluded \ state.entry.excluded).Nonempty := by
    obtain ⟨who, member⟩ := missed
    exact ⟨who, (Finset.mem_inter.mp member).1⟩
  have survivesSource : (block.owners \ (phase.drain state.current).excluded).Nonempty := by
    rw [← ownerEq]
    exact survives
  obtain ⟨final, closed, values, finalGuards, normalized, _recall⟩ :=
    sourceClose_of_retry_bindingPhase setup.program mode block suffix embedding compiled positive
      state remaining installed binding receipts stored source agree guards finished missedSource
      survivesSource
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  have reached := closed.reaches_lift setup.program sourceInitial suffix boundary positive lift
    ranks actors (fun point who => menus who point) steps commits owners endpoints automatic
    history memory
  have reachedTrace := setup.recoveryTrace_of_reaches sourceInitial sourceTrace reached
  rw [normalized]
  refine ⟨
    { residual := ⟨Γ, O, block.prepend suffix, lift⟩
      source := { source with history := final.history }
      refs := refs
      registry := registry
      embedding := embedding
      before := before
      compiled := ?_
      terminalAlignment := aligned
      agrees := values
      guards := finalGuards
      failures := failures
      unique := unique
      remaining := ranks
      actor := actors
      atCommit := commits
      owners := owners
      commitEnd := endpoints
      automatic := automatic
      history := history
      withHistory := memory
      step := steps
      menus := menus
      readout := readout
      trace := reachedTrace }⟩
  change CompiledSuffix setup.program (block.prepend suffix) refs source.revelations registry
    embedding before phase.low
  rw [← low] at compiled
  exact compiled

end Vegas

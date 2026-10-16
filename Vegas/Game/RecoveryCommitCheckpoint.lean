/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Game.RecoverySourceBoundary
import Vegas.Game.CommitAttemptSurvivingRecall
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
    (priorTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      state.entry.excluded state.generation)))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (binding : state.BindingRecord) (receipts : state.ReceiptRecord)
    (remembered : state.HistoryCheckpoint)
    {inputs} (native : state.Invariant inputs)
    (finished : phase.Finished (phase.drain state.current))
    (missed : (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty) :
    ∃ next : RecoverySourceCheckpoint setup mode state.normalize,
      next.residual.lift (ProtocolState.entry next.residual.tail next.source) =
        ProtocolState.withHistory setup.program
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          (ProtocolState.history setup.program
            (checkpoint.commitResultPoint (phase.drain state.current))) ∧
      (∃ (nextTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
          state.normalize.entry.excluded state.normalize.generation))) (fuel : Nat),
        setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, priorTrace⟩ ⟨_, nextTrace⟩ ∧
        setup.recoveryJointRecall nextTrace =
          (checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
            setup.recoveryJointRecall priorTrace) ∧
      ∀ who, who ∉ (phase.drain state.current).excluded →
      next.source.history who = checkpoint.source.history who ++
        (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) who).length := by
  dsimp only [RecoverySourceCheckpoint.commitResultPoint,
    RecoverySourceCheckpoint.commitInstructionWord]
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, aligned, agree, guards, failures, unique, ranks, actors, commits, owners, endpoints,
    automatic, history, memory, steps, menus, readout, _sourceTrace, views, historyAlignment,
    origin⟩
  dsimp only
  generalize _decomposition : commitPhase program = segment at ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
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
  let image := phase.drain state.current
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding image.native
    source state.entry.excluded
  let final := decoded.1
  have member : phase ∈ state.phases.head? := by
    rw [installed]
    exact Option.mem_some_iff.mpr rfl
  have within := receipts.exclusion.frontier.positioned
  rw [installed] at within
  have record := (receipts.exclusion.installed phase member).phase_drain phase
  have excludedEq : decoded.2.1 = image.excluded :=
    decodeCommitAttempt_excluded_eq_physical setup.program mode block suffix embedding
      compiled positive image source state.entry.excluded record
      (phase.drain_within state.current within.2) finished
  let attempt : block.Attempt source state.entry.excluded final image.excluded :=
    excludedEq ▸ decoded.2.2
  have failed : attempt.failedOwners.Nonempty := by
    rwa [← attempt.newly_excluded]
  have normalized : state.normalize =
      ⟨phase :: remaining, state.generation + 1, PhaseRuntimeState.restore state.entry image,
        phase.drain (PhaseRuntimeState.restore state.entry image),
        state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]⟩ := by
    change PhaseRuntimeState.settle state.phases state.generation state.entry state.current
      state.retired = _
    rw [installed]
    exact PhaseRuntimeState.settle_retry phase remaining state.generation state.entry
      state.current state.retired finished rfl missed survives
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  have instructions := attempt.instructions_closed_lift setup.program sourceInitial suffix lift
    ranks actors (fun point who => menus who point) steps
    (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend suffix) source)) state.entry.excluded
      state.generation) rfl rfl ((commits _).trans committing)
    ((endpoints _).trans (block.commitEnd_entry_prepend suffix boundary source)).le positive
  rw [attempt.close_retry_lift setup.program suffix boundary positive state.generation lift ranks
    commits owners endpoints history memory failed survivesSource] at instructions
  obtain ⟨reachedTrace, reachedPrefix, reachedInstructions⟩ :=
    setup.recoveryTrace_of_instructions sourceInitial priorTrace instructions
  let fuel := attempt.joints.length
  have decodedInstructions : attempt.joints = decoded.2.2.joints :=
    SourceProgram.CommitPrefix.Attempt.joints_cast_after excludedEq decoded.2.2
  rw [decodedInstructions] at reachedInstructions
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
      agrees := agree
      guards := guards
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
      trace := ⟨reachedTrace⟩
      views := views
      origin := origin
      historyAlignment := by
        intro clear
        obtain ⟨who, member⟩ := missedSource
        have excluded := (Finset.mem_sdiff.mp member).1
        change who ∈ (phase.drain state.current).excluded at excluded
        change (phase.drain state.current).excluded = ∅ at clear
        rw [clear] at excluded
        exact False.elim (Finset.notMem_empty _ excluded) }, ?_⟩
  · change CompiledSuffix setup.program (block.prepend suffix) refs source.revelations registry
      embedding before phase.low
    rw [← low] at compiled
    exact compiled
  · refine ⟨?_, ⟨reachedTrace, fuel, reachedPrefix, reachedInstructions⟩, ?_⟩
    · change lift (ProtocolState.entry (block.prepend suffix)
          { source with history := final.history }) =
        ProtocolState.withHistory setup.program
          (lift (ProtocolState.entry (block.prepend suffix) source))
          (ProtocolState.history setup.program
            (lift (block.liftPoint suffix (ProtocolState.entry suffix final))))
      rw [← memory, history, SourceProgram.CommitPrefix.liftPoint_history,
        ProtocolState.history_entry, ProtocolState.withHistory_entry]
    · intro who active
      exact decodeCommitAttempt_history_extension_of_survivor setup.program mode block suffix
        embedding state.attempt.phase compiled.rankEq state.entry.native image.native source
        state.entry.excluded who (by rw [excludedEq]; exact active)
        (phase.drain_bindingInvariant state.current binding.active)
        (phase.drain_invariant state.current native.active).reachable
        (remembered.trans (phase.drain_history_prefix state.current))
        (show state.entry.native.config.cut.IsPrefix state.attempt.phase from by
          rw [← low]; exact within.1)
        (phase.finished_prefix image (phase.drain_within state.current within.2) finished)
        views.actionEq

end Vegas

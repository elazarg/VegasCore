/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Source.CommitRecoveryNoMissInformation
import Vegas.Source.CommitPhaseRecall
import Vegas.Game.CommitAttemptSurvivingRecall
import Vegas.Game.CompiledCommitCompletion
import Vegas.Compile.CommitPrefixAdmission
import Vegas.Source.CommitPrefixIntendedLift
import Vegas.Game.CompiledCommitClosing
import Vegas.Game.CompiledCommitTail
import Vegas.Game.CompiledCommitMaximality
import Vegas.Source.CommitPhaseAutomaticAttempt
import Vegas.Game.CommitAttemptOwnRecall
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Source.CommitRecoveryBlockCloseLift
import GameTheory.Protocol.Backward

/-! # Saved source checkpoints after clean and exhausted physical binding phases -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem next_phase_address {graph : Vegas.EventGraph Player L}
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph)) (generation : Nat)
    (image : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (adjacent : (phase :: remaining).IsChain fun before after => before.high = after.low)
    (last : ∀ final ∈ (phase :: remaining).getLast?, final.high = graph.order.eventCount) :
    (⟨remaining, generation, image, image, retired⟩ : PhaseRuntimeState graph).attempt.phase =
      phase.high := by
  cases remaining with
  | nil =>
      have ending := last phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
      simpa only [PhaseRuntimeState.attempt, List.head?_nil, Option.map_none, Option.getD_none]
        using ending.symm
  | cons next rest =>
      have boundary := adjacent.rel_head? (y := next) (by simp)
      simpa only [PhaseRuntimeState.attempt, List.head?_cons, Option.map_some, Option.getD_some]
        using boundary.symm

/-- Read the exact whole source endpoint of the current maximal binding
segment from an actual physical image. The source entry and own words are those
of this same saved checkpoint. -/
def RecoverySourceCheckpoint.commitResultPoint
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (image : RecoveryState ((toEventGraph setup.program).withMode mode)) :
    ProtocolState setup.program :=
  match commitPhase checkpoint.residual.tail with
  | ⟨_, _, suffix, block, reconstruct, _⟩ =>
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program)
        reconstruct.symm) checkpoint.embedding
    let decoded := decodeCommitAttempt setup.program mode block suffix embedding
      image.native checkpoint.source state.entry.excluded
    checkpoint.residual.lift (cast (congrArg (fun program => ProtocolState program)
      reconstruct) (block.liftPoint suffix (ProtocolState.entry suffix decoded.1)))

/-- Read the exact original typed-choice and omission instruction word of
this checkpoint's actual maximal physical commitment image. -/
def RecoverySourceCheckpoint.commitInstructionWord
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode)) :
    List (Player → Option (CommitRecoveryMove Player L)) :=
  match commitPhase checkpoint.residual.tail with
  | ⟨_, _, suffix, block, reconstruct, _⟩ =>
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program)
        reconstruct.symm) checkpoint.embedding
    (decodeCommitAttempt setup.program mode block suffix embedding native
      checkpoint.source state.entry.excluded).2.2.joints

/-- The original accepted-none mask determines the exclusion set after
all successive static slots, including automatic slots of excluded owners. -/
def RecoverySourceCheckpoint.commitExclusionWord
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode)) :
    List (Finset Player) :=
  match commitPhase checkpoint.residual.tail with
  | ⟨_, _, suffix, block, reconstruct, _⟩ =>
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program)
        reconstruct.symm) checkpoint.embedding
    (decodeCommitAttempt setup.program mode block suffix embedding native
      checkpoint.source state.entry.excluded).2.2.exclusionsAfter

/-- Every owner's completed physical prefix contains successful bindings
satisfying their original private guards, including the saved entry cells. -/
def RecoverySourceCheckpoint.commitAdmitted
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (image : RecoveryState ((toEventGraph setup.program).withMode mode)) : Prop :=
  match commitPhase checkpoint.residual.tail with
  | ⟨_, pending, suffix, block, reconstruct, _⟩ =>
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program)
        reconstruct.symm) checkpoint.embedding
    ∀ who, (fillCommitPrefix setup.program block suffix embedding image.native.config.store
      checkpoint.source).IntendedFor who pending

/-- A completed physical phase without a new owned miss saves the exact
source-ordered binding result and its initialized legal source recovery trace. -/
theorem RecoverySourceCheckpoint.after_commit_clean
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
    (stored : state.StoredCheckpoint) (remembered : state.HistoryCheckpoint)
    {inputs} (native : state.Invariant inputs) (coverage : state.FailureCoverage)
    (finished : phase.Finished (phase.drain state.current))
    (clean : ¬ (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty) :
    (∃ next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)),
      next.residual.lift (ProtocolState.entry next.residual.tail next.source) =
        checkpoint.commitResultPoint (phase.drain state.current) ∧
      (∃ fuel : Nat,
        setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩ ∧
        setup.recoveryJointRecall next.trace =
          (checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
            setup.recoveryJointRecall checkpoint.trace) ∧
      (∀ who, who ∉ (phase.drain state.current).excluded →
        next.source.history who = checkpoint.source.history who ++
          (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
            ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
              (decodeHistory setup.program (state.entry.native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) who).length) ∧
      ((phase.drain state.current).excluded = ∅ →
        ProtocolState.Intended setup.program (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) →
        checkpoint.commitAdmitted (phase.drain state.current) →
        ProtocolState.Intended setup.program (next.residual.lift
          (ProtocolState.entry next.residual.tail next.source)))) ∧
      state.normalize = PhaseRuntimeState.settle remaining state.generation
        (phase.drain state.current) (phase.drain state.current) state.retired := by
  let priorTrace := checkpoint.trace
  dsimp only [RecoverySourceCheckpoint.commitResultPoint, RecoverySourceCheckpoint.commitAdmitted,
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
  have head : state.phases.head? = some phase := by rw [installed]; rfl
  have member : phase ∈ state.phases.head? := by
    rw [head]
    exact Option.mem_some_iff.mpr rfl
  have within := receipts.exclusion.frontier.positioned
  rw [installed] at within
  let image := phase.drain state.current
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding image.native source
    state.entry.excluded
  let final := decoded.1
  have record := (receipts.exclusion.installed phase member).phase_drain phase
  have excludedEq := decodeCommitAttempt_excluded_eq_physical setup.program mode block suffix
    embedding compiled positive image source state.entry.excluded record
    (phase.drain_within state.current within.2) finished
  let attempt : block.Attempt source state.entry.excluded final image.excluded :=
    excludedEq ▸ decoded.2.2
  have activeAgree : refs.Agrees source.state image.native.config.store := by
    intro name cell selected
    apply (refs.get selected).get?_preserved state.entry.native.config.store _
      (fun field value present => phase.drain_keepsStore state.current field value
        (stored field value present)) _ (agree selected)
  have values : (commitBlockRefs setup.program block suffix embedding refs).Agrees final.state
      image.native.config.store := by
    apply decodeCommitAttempt_state_agrees setup.program mode block suffix embedding refs
      image.native source state.entry.excluded state.attempt.phase compiled.rankEq
      (phase.drain_bindingInvariant state.current binding.active)
      ((receipts.ordered phase member rfl).congr (phase.drain_tables state.current).1) activeAgree
    intro index inside
    exact finished ((compiledCommitPhase_mem_iff setup.program mode block suffix embedding
      compiled positive _).mpr ⟨index, inside, rfl⟩)
  have finalGuards := decodeCommitAttempt_registry_extension setup.program mode block suffix
    embedding image.native source state.entry.excluded registry guards
  have noFailure : attempt.failedOwners = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨who, failed⟩
    apply clean
    refine ⟨who, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rwa [attempt.newly_excluded]
    · rw [ownerEq]
      exact attempt.failed_subset_owners failed
  have normalized : state.normalize = PhaseRuntimeState.settle remaining state.generation
      (phase.drain state.current) (phase.drain state.current) state.retired := by
    change PhaseRuntimeState.settle state.phases state.generation state.entry state.current
      state.retired = _
    rw [installed]
    apply PhaseRuntimeState.settle_clean phase remaining state.generation state.entry state.current
      state.retired finished
    exact fun failed => clean failed.2
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨_addresses, instructions, _exclusions⟩ :=
    attempt.instructions_closed_lift setup.program sourceInitial suffix lift
    ranks actors (fun point who => menus who point) steps
    (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend suffix) source)) state.entry.excluded
      state.generation) rfl rfl ((commits _).trans committing)
    ((endpoints _).trans (block.commitEnd_entry_prepend suffix boundary source)).le positive
  rw [attempt.close_clean_lift setup.program suffix boundary positive state.generation lift ranks
    commits endpoints noFailure] at instructions
  obtain ⟨reachedTrace, reachedPrefix, _reachedLength, reachedInstructions, _reachedAddresses⟩ :=
    setup.recoveryInstructionPath_information sourceInitial instructions priorTrace
  let fuel := attempt.joints.length
  have decodedInstructions : attempt.joints = decoded.2.2.joints :=
    SourceProgram.CommitPrefix.Attempt.joints_cast_after excludedEq decoded.2.2
  rw [decodedInstructions] at reachedInstructions
  obtain ⟨finalEmbedding, finalBefore, finalCompiled, finalAlignment, ⟨finalViews⟩⟩ :=
    attempt.compiledTail
      setup.program suffix refs registry embedding before state.attempt.phase compiled aligned lift
        views
  obtain ⟨tailRanks, tailActors, tailCommits, tailOwners, tailEnds, tailAutomatic, tailHistory,
    tailMemory, tailSteps, tailMenus, tailReadout⟩ := block.liftPoint_recovery suffix
  have address := next_phase_address phase remaining state.generation (phase.drain state.current)
    state.retired adjacent last
  have finalFailures := attempt.preservesFailures failures
  refine ⟨?_, normalized⟩
  refine ⟨
    { residual := ⟨Δ, P, suffix, fun point => lift (block.liftPoint suffix point)⟩
      source := final
      refs := commitBlockRefs setup.program block suffix embedding refs
      registry := block.guardRegistry registry
      embedding := finalEmbedding
      before := finalBefore
      compiled := ?_
      terminalAlignment := finalAlignment
      agrees := values
      guards := finalGuards
      failures := finalFailures
      unique := block.names_nodup unique
      remaining := fun point => (ranks _).trans (tailRanks point)
      actor := fun point => (actors _).trans (tailActors point)
      atCommit := fun point => (commits _).trans (tailCommits point)
      owners := fun point => (owners _).trans (tailOwners point)
      commitEnd := fun point => (endpoints _).trans (tailEnds point)
      automatic := fun point =>
        (congrArg lift (tailAutomatic point)).trans (automatic _)
      history := fun point => (history _).trans (tailHistory point)
      withHistory := fun point past =>
        (congrArg lift (tailMemory point past)).trans (memory _ _)
      step := ?_
      menus := fun who point => (menus who _).trans (tailMenus who point)
      readout := ?_
      trace := reachedTrace
      views := finalViews
      origin := origin.compose (block.protocolSuffix suffix)
      historyAlignment := ?_ }, ?_, ?_, ?_, ?_⟩
  · rw [address]
    exact finalCompiled
  · intro point excluded joint
    rw [steps, tailSteps]
    simp only [PMF.map_comp, Function.comp_def]
  · intro point
    rw [readout, tailReadout, Option.map_map]
    congr 1
    funext terminal
    simp only [Function.comp_apply, cast_cast]
  · intro clear
    have oldClear : state.entry.excluded = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro who member
      have excluded := (record.excluded who).mpr (Or.inl member)
      rw [clear] at excluded
      exact Finset.notMem_empty _ excluded
    have alignedHistory := historyAlignment oldClear
    change (decodeCommitAttempt setup.program mode block suffix embedding image.native source
      state.entry.excluded).1.history = _
    rw [oldClear]
    exact decodeCommitAttempt_history_of_clear_phase setup.program mode block suffix embedding
      state.attempt.phase compiled.rankEq state.entry.native image source
      (phase.drain_bindingInvariant state.current binding.active)
      (phase.drain_invariant state.current native.active).reachable (coverage.active.drain phase)
      clear (remembered.trans (phase.drain_history_prefix state.current)) within.1
      (phase.finished_prefix image (phase.drain_within state.current within.2) finished)
      alignedHistory views.actionEq
  · rfl
  · exact ⟨fuel, reachedPrefix, reachedInstructions⟩
  · intro who active
    exact decodeCommitAttempt_history_extension_of_survivor setup.program mode block suffix
      embedding state.attempt.phase compiled.rankEq state.entry.native image.native source
      state.entry.excluded who (by rw [excludedEq]; exact active)
      (phase.drain_bindingInvariant state.current binding.active)
      (phase.drain_invariant state.current native.active).reachable
      (remembered.trans (phase.drain_history_prefix state.current)) within.1
      (phase.finished_prefix image (phase.drain_within state.current within.2) finished)
      views.actionEq
  · intro clear intended admitted
    have completed : ∀ index : Fin (eventCount (block.prepend suffix)),
        index.val < block.length → embedding.event index ∈ image.native.config.cut.completed := by
      intro index inside
      exact finished ((compiledCommitPhase_mem_iff setup.program mode block suffix embedding
        compiled positive _).mpr ⟨index, inside, rfl⟩)
    have equal := decodeCommitAttempt_eq_fill_of_clear setup.program mode block suffix embedding
      image.native (phase.drain_bindingInvariant state.current binding.active) source
      state.entry.excluded completed (excludedEq.trans clear)
    have finalIntended := fillCommitPrefix_intended setup.program block suffix embedding
      image.native.config.store source (origin.intended_reflect _ intended) admitted
    rw [← equal] at finalIntended
    exact attempt.intended_lift setup.program suffix lift origin intended finalIntended

/-- An actual exhausted physical phase rebuilds the saved source block with
only automatic excluded slots and preserves the retained attempted history.
No retry, source outcome, closure law or source path is supplied as a premise. -/
theorem RecoverySourceCheckpoint.after_commit_exhausted
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
    (exhausted : ¬ (phase.owners \ (phase.drain state.current).excluded).Nonempty) :
    let image := phase.drain state.current
    let rebuilt := phase.drain (PhaseRuntimeState.restore state.entry image)
    let archive := state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]
    (∃ next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, rebuilt, rebuilt, archive⟩ :
        PhaseRuntimeState ((toEventGraph setup.program).withMode mode)),
      (∃ fuel : Nat,
        setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩ ∧
        setup.recoveryJointRecall next.trace =
          (checkpoint.commitInstructionWord image.native).reverse ++
            setup.recoveryJointRecall checkpoint.trace) ∧
      (∀ who, who ∉ image.excluded → next.source.history who = checkpoint.source.history who)) ∧
      state.normalize = PhaseRuntimeState.settle remaining state.generation rebuilt rebuilt
        archive := by
  let priorTrace := checkpoint.trace
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord]
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
  have noSource : ¬ (block.owners \ (phase.drain state.current).excluded).Nonempty := by
    rwa [← ownerEq]
  obtain ⟨chosenFinal, chosenFinalEq, closed, values, finalGuards, normalized⟩ :=
    sourceClose_of_exhausted_bindingPhase setup.program mode block suffix embedding compiled
      positive state remaining installed binding receipts stored source agree guards finished
      missedSource noSource
  let image := phase.drain state.current
  let rebuilt := phase.drain (PhaseRuntimeState.restore state.entry image)
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding image.native source
    state.entry.excluded
  let final := decoded.1
  have selectedFinal : chosenFinal = final := chosenFinalEq
  subst chosenFinal
  have member : phase ∈ state.phases.head? := by
    rw [installed]
    exact Option.mem_some_iff.mpr rfl
  have within := receipts.exclusion.frontier.positioned
  rw [installed] at within
  have record := (receipts.exclusion.installed phase member).phase_drain phase
  have excludedEq := decodeCommitAttempt_excluded_eq_physical setup.program mode block suffix
    embedding compiled positive image source state.entry.excluded record
    (phase.drain_within state.current within.2) finished
  let attempt : block.Attempt source state.entry.excluded final image.excluded :=
    excludedEq ▸ decoded.2.2
  have failed : attempt.failedOwners.Nonempty := by rwa [← attempt.newly_excluded]
  let restoredSource := { source with history := final.history }
  have allSource : block.owners ⊆ image.excluded := by
    intro who member
    by_contra outside
    exact noSource ⟨who, Finset.mem_sdiff.mpr ⟨member, outside⟩⟩
  let automaticAttempt := block.automaticAttempt restoredSource image.excluded allSource
  obtain ⟨finalEmbedding, finalBefore, finalCompiled, finalAlignment, ⟨finalViews⟩⟩ :=
    automaticAttempt.compiledTail setup.program suffix refs registry embedding before
      state.attempt.phase compiled aligned lift views
  obtain ⟨tailRanks, tailActors, tailCommits, tailOwners, tailEnds, tailAutomatic, tailHistory,
    tailMemory, tailSteps, tailMenus, tailReadout⟩ := block.liftPoint_recovery suffix
  let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨_addresses, instructions, _exclusions⟩ :=
    attempt.instructions_closed_lift setup.program sourceInitial suffix lift
    ranks actors (fun point who => menus who point) steps
    (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend suffix) source)) state.entry.excluded
      state.generation) rfl rfl ((commits _).trans committing)
    ((endpoints _).trans (block.commitEnd_entry_prepend suffix boundary source)).le positive
  rw [attempt.close_exhausted_lift setup.program suffix boundary positive state.generation lift
    ranks commits owners endpoints automatic history memory failed allSource] at instructions
  obtain ⟨reachedTrace, reachedPrefix, _reachedLength, reachedInstructions, _reachedAddresses⟩ :=
    setup.recoveryInstructionPath_information sourceInitial instructions priorTrace
  let fuel := attempt.joints.length
  have decodedInstructions : attempt.joints = decoded.2.2.joints :=
    SourceProgram.CommitPrefix.Attempt.joints_cast_after excludedEq decoded.2.2
  rw [decodedInstructions] at reachedInstructions
  have address := next_phase_address phase remaining state.generation rebuilt
    (state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]) adjacent last
  have finalFailures := automaticAttempt.preservesFailures failures
  have finalHistory : ∃ (finalTrace : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint
        (lift (block.liftPoint suffix
          (ProtocolState.entry suffix (block.automatic restoredSource))))
        rebuilt.excluded state.generation))) (finalFuel : Nat),
      setup.commitRecoveryProtocol.ReachesWithin finalFuel
        ⟨_, priorTrace⟩ ⟨_, finalTrace⟩ ∧
      setup.recoveryJointRecall finalTrace = decoded.2.2.joints.reverse ++
        setup.recoveryJointRecall priorTrace := by
    rw [show rebuilt.excluded = image.excluded from phase.drain_excluded _]
    exact ⟨reachedTrace, fuel, reachedPrefix, reachedInstructions⟩
  obtain ⟨finalTrace, finalFuel, finalPrefix, finalInstructions⟩ := finalHistory
  refine ⟨?_, normalized⟩
  refine ⟨
    { residual := ⟨Δ, P, suffix, fun point => lift (block.liftPoint suffix point)⟩
      source := block.automatic restoredSource
      refs := commitBlockRefs setup.program block suffix embedding refs
      registry := block.guardRegistry registry
      embedding := finalEmbedding
      before := finalBefore
      compiled := ?_
      terminalAlignment := finalAlignment
      agrees := values
      guards := finalGuards
      failures := finalFailures
      unique := block.names_nodup unique
      remaining := fun point => (ranks _).trans (tailRanks point)
      actor := fun point => (actors _).trans (tailActors point)
      atCommit := fun point => (commits _).trans (tailCommits point)
      owners := fun point => (owners _).trans (tailOwners point)
      commitEnd := fun point => (endpoints _).trans (tailEnds point)
      automatic := fun point =>
        (congrArg lift (tailAutomatic point)).trans (automatic _)
      history := fun point => (history _).trans (tailHistory point)
      withHistory := fun point past =>
        (congrArg lift (tailMemory point past)).trans (memory _ _)
      step := ?_
      menus := fun who point => (menus who _).trans (tailMenus who point)
      readout := ?_
      trace := finalTrace
      views := finalViews
      origin := origin.compose (block.protocolSuffix suffix)
      historyAlignment := by
        intro clear
        have imageClear : image.excluded = ∅ := by
          change rebuilt.excluded = ∅ at clear
          have same : rebuilt.excluded = image.excluded :=
            phase.drain_excluded (PhaseRuntimeState.restore state.entry image)
          exact same.symm.trans clear
        obtain ⟨who, member⟩ := missedSource
        have excluded := (Finset.mem_sdiff.mp member).1
        rw [imageClear] at excluded
        exact False.elim (Finset.notMem_empty _ excluded) }, ?_⟩
  · rw [address]
    exact finalCompiled
  · intro point excluded joint
    rw [steps, tailSteps]
    simp only [PMF.map_comp, Function.comp_def]
  · intro point
    rw [readout, tailReadout, Option.map_map]
    congr 1
    funext terminal
    simp only [Function.comp_apply, cast_cast]
  · refine ⟨⟨finalFuel, finalPrefix, finalInstructions⟩, ?_⟩
    intro who active
    have outside : who ∉ block.owners := fun member => active (allSource member)
    exact closed.history_eq_of_not_owner who outside

end Vegas

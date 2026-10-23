/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryCommitChronology
import Vegas.Game.RecoverySurvivingBindingSource
import Vegas.Game.RevealService
import Vegas.Source.CommitRecoveryCommitUnique
import Vegas.Source.CommitRecoveryCommitWindow
import Interaction.ReactiveRounds

/-! # Exact control of the genuinely chosen decoded commitment close -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem finished_close_control
    {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
    (state : CommitRecoveryState program) (finished : state.Finished) :
    (state.close.generation = state.generation + 1 ∧
      ProtocolState.remaining program state.close.saved =
        ProtocolState.remaining program state.saved) ∨
    (state.close.generation = state.generation ∧
      ProtocolState.remaining program state.close.saved =
        ProtocolState.commitEnd program state.saved) := by
  classical
  unfold CommitRecoveryState.close
  simp only [finished, ↓reduceIte]
  split
  · split
    · exact Or.inl ⟨rfl, by simp only [CommitRecoveryState.retry, CommitRecoveryState.atPoint,
        CommitRecoveryState.restored, ProtocolState.remaining_withHistory]⟩
    · exact Or.inr ⟨rfl, by simp only [CommitRecoveryState.exhausted,
        CommitRecoveryState.atPoint, ProtocolState.automaticCommitBlock_remaining,
        CommitRecoveryState.restored, ProtocolState.commitEnd_withHistory]⟩
  · exact Or.inr ⟨rfl, finished.2⟩

/-- A chosen decoded commitment continuation is literally the realization of
its original typed attempt path, including the final retry or exhausted close.
The predecessor trace is the retained checkpoint trace. -/
theorem RecoverySourceCheckpoint.chosen_commit_trace
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord native).reverse ++
        setup.recoveryJointRecall checkpoint.trace) :
    match commitPhase checkpoint.residual.tail with
    | ⟨_, _, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      let decoded := decodeCommitAttempt setup.program mode block suffix embedding native
        checkpoint.source state.entry.excluded
      let start := CommitRecoveryState.atPoint
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          state.entry.excluded state.generation
      let point := checkpoint.residual.lift (cast (congrArg ProtocolState reconstruct)
        (block.liftPoint suffix (ProtocolState.entry suffix decoded.1)))
      let final := (start.install (point, decoded.2.1)
        (fun _ member => decoded.2.2.excluded_subset member)).close
      ∃ canonical : setup.commitRecoveryProtocol.Trace (some final),
        setup.commitRecoveryProtocol.ReachesWithin decoded.2.2.joints.length
          ⟨_, checkpoint.trace⟩ ⟨_, canonical⟩ ∧
        setup.recoveryJointRecall canonical = decoded.2.2.joints.reverse ++
          setup.recoveryJointRecall checkpoint.trace ∧
        closed = ⟨_, canonical⟩ ∧
        ∃ addresses, setup.recoveryAddressWord canonical =
          setup.recoveryAddressWord checkpoint.trace ++ addresses ∧
          addresses.map (fun address => address.2.1) = decoded.2.2.exclusionsAfter ∧
          start.IntervalAddresses addresses ∧
          addresses.getLast? = some final.publicAddress := by
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord] at instructions
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, priorTrace, views,
    historyAlignment, origin⟩
  dsimp only at committing instructions ⊢
  generalize decomposition : commitPhase program = segment at instructions ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only at instructions ⊢
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [CommitPrefix.length]; omega
  let start := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) source)) state.entry.excluded state.generation
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding native source
    state.entry.excluded
  let final := (start.install
    (lift (block.liftPoint suffix (ProtocolState.entry suffix decoded.1)), decoded.2.1)
      (fun _ member => decoded.2.2.excluded_subset member)).close
  have wholeCommit : ProtocolState.atCommit setup.program start.point = true :=
    (commits _).trans committing
  have ending : ProtocolState.commitEnd setup.program start.saved = instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (block.prepend suffix) source)) = _
    rw [origin.commitEnd_lift, block.commitEnd_entry_prepend suffix boundary]
  let initial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨addresses, canonical, exclusions, metadata⟩ :=
    decoded.2.2.instructions_closed_lift setup.program initial suffix lift ranks
    actors (fun point player => menus player point) steps start rfl rfl wholeCommit ending.le
    positive
  obtain ⟨canonicalTrace, canonicalReached, _canonicalLength, canonicalInstructions,
    canonicalAddresses⟩ := setup.recoveryInstructionPath_information initial canonical priorTrace
  have nonempty : decoded.2.2.joints ≠ [] := by
    intro empty
    have length := decoded.2.2.joints_length
    rw [empty] at length
    simp only [List.length_nil] at length
    omega
  have lastAddress := canonical.last_address nonempty
  have chosenLength := congrArg List.length instructions
  simp only [List.length_reverse, List.length_append, CommitPrefix.Attempt.joints_length,
    setup.recoveryJointRecall_length] at chosenLength
  have window := block.length_le_commit_window suffix source
  rw [← origin.commitEnd_lift, ← ranks] at window
  change block.length + ProtocolState.commitEnd setup.program start.point ≤
    ProtocolState.remaining setup.program start.point at window
  have same := setup.commitRecovery_history_eq_of_commit_window start priorTrace wholeCommit
    closed.trace canonicalTrace reached canonicalReached
    (instructions.trans canonicalInstructions.symm) (by omega)
  exact ⟨canonicalTrace, canonicalReached, canonicalInstructions, same,
    addresses, canonicalAddresses, exclusions, metadata, lastAddress⟩

/-- The actual chosen close contributes one literal numeric address suffix,
whose exclusion scan is the original completed native omission mask. -/
theorem RecoverySourceCheckpoint.chosen_commit_addresses
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord native).reverse ++
        setup.recoveryJointRecall checkpoint.trace) :
    ∃ addresses, setup.recoveryAddressWord closed.trace =
      setup.recoveryAddressWord checkpoint.trace ++ addresses ∧
      addresses.map (fun address => address.2.1) = checkpoint.commitExclusionWord native ∧
      (CommitRecoveryState.atPoint
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
        state.entry.excluded state.generation).IntervalAddresses addresses ∧
      addresses.getLast? = closed.state.map CommitRecoveryState.publicAddress := by
  have chosen := checkpoint.chosen_commit_trace native committing closed reached instructions
  unfold RecoverySourceCheckpoint.commitExclusionWord
  generalize decomposition : commitPhase checkpoint.residual.tail = segment at chosen ⊢
  rcases segment with ⟨Δ, O, suffix, block, reconstruct, boundary⟩
  dsimp only at chosen ⊢
  obtain ⟨canonical, _path, _word, same, addresses, addressWord, exclusions, metadata,
    lastAddress⟩ := chosen
  cases same
  exact ⟨addresses, addressWord, exclusions, metadata, lastAddress⟩

/-- Every interior signal in the genuinely chosen completed commitment
chunk is read from the native public failure scan at that exact source rank.
The final signal is the actual close, including exhausted restore. -/
theorem RecoverySourceCheckpoint.chosen_commit_public_scan [Fintype Player]
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (frontier : state.Frontier)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (archives : state.ArchivedExclusions) (savedFailures : state.PublicFailureCheckpoint)
    (finished : phase.Finished (phase.drain state.current))
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace) :
    ∃ addresses, setup.recoveryAddressWord closed.trace =
        setup.recoveryAddressWord checkpoint.trace ++ addresses ∧
      (∀ index (beforeLast : index + 1 < addresses.length),
        addresses[index]'(by omega) =
          (some (state.attempt.phase + index + 1),
            PhaseRuntimeState.archivedFailureOwners state.retired ∪
              (phase.drain state.current).native.failureOwnersBefore
                (state.attempt.phase + index + 1), state.generation, state.attempt.phase)) ∧
      addresses.getLast? = closed.state.map CommitRecoveryState.publicAddress ∧
      addresses.dropLast = (List.range (phase.high - phase.low - 1)).map (fun index =>
        (some (state.attempt.phase + index + 1),
          PhaseRuntimeState.archivedFailureOwners state.retired ∪
            (phase.drain state.current).native.failureOwnersBefore
              (state.attempt.phase + index + 1), state.generation, state.attempt.phase)) := by
  let native := (phase.drain state.current).native
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  have committing := checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations
    checkpoint.registry checkpoint.embedding checkpoint.before state.attempt.phase
    phase kind low checkpoint.source
  have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    have positioned := frontier.positioned
    rw [installed] at positioned
    rw [← low]
    exact positioned.1
  have extension : state.entry.native.PublicFailureExtension native :=
    savedFailures.trans (phase.drain_publicFailureExtension state.current)
  have geometry := checkpoint.commit_phase_geometry phase remaining installed kind frontier maximal
  have completed : match commitPhase checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ native.config.cut.completed := by
    generalize decomposition : commitPhase checkpoint.residual.tail = segment at geometry ⊢
    rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
    dsimp only at geometry ⊢
    intro index inside
    exact finished (geometry.2 index inside)
  have wordLength : (checkpoint.commitInstructionWord native).length =
      phase.high - phase.low := by
    unfold RecoverySourceCheckpoint.commitInstructionWord
    generalize decomposition : commitPhase checkpoint.residual.tail = segment at geometry ⊢
    rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
    dsimp only at geometry ⊢
    rw [CommitPrefix.Attempt.joints_length]
    exact geometry.1
  obtain ⟨addresses, word, exclusions, metadata, ending⟩ :=
    checkpoint.chosen_commit_addresses native committing closed reached instructions
  have scanned := checkpoint.commit_exclusion_scan native archives saved extension completed
  have fullScan := exclusions.trans scanned
  have length : addresses.length = (checkpoint.commitInstructionWord native).length := by
    have lengths := congrArg List.length fullScan
    simpa only [List.length_map, List.length_range] using lengths
  have interior : ∀ index (beforeLast : index + 1 < addresses.length),
      addresses[index]'(by omega) =
        (some (state.attempt.phase + index + 1),
          PhaseRuntimeState.archivedFailureOwners state.retired ∪
            native.failureOwnersBefore (state.attempt.phase + index + 1),
          state.generation, state.attempt.phase) := by
    intro index beforeLast
    obtain ⟨rank, generation, boundary⟩ := metadata index beforeLast
    have excluded := congrArg (fun values : List (Finset Player) => values[index]?) fullScan
    have bound : index < addresses.length := by omega
    have otherBound : index < (checkpoint.commitInstructionWord native).length := by omega
    simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
      List.getElem?_range otherBound, Option.map_some] at excluded
    have sameExcluded := Option.some.inj excluded
    have position := checkpoint.saved_position
    change instructionCount setup.program - ProtocolState.remaining setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) =
      state.attempt.phase at position
    dsimp only [CommitRecoveryState.atPoint] at rank generation boundary
    rw [position] at rank boundary
    apply Prod.ext rank
    exact Prod.ext sameExcluded (Prod.ext generation boundary)
  refine ⟨addresses, word, interior, ending, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_dropLast, List.length_map, List.length_range, length, wordLength]
  · intro index bound _
    have beforeLast : index + 1 < addresses.length := by
      simp only [List.length_dropLast] at bound
      omega
    simpa only [List.getElem_dropLast, List.getElem_map, List.getElem_range] using
      interior index beforeLast

/-- The original decoded instruction word fixes the control of its genuinely
chosen close. A retry keeps the saved instruction rank and increments generation;
a clean or exhausted close moves to the exact maximal block end. -/
theorem RecoverySourceCheckpoint.chosen_commit_control
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord native).reverse ++
        setup.recoveryJointRecall checkpoint.trace) :
    ∃ next : CommitRecoveryState setup.program, closed.state = some next ∧
      next.saved = next.point ∧
      ((next.generation = state.generation + 1 ∧
        ProtocolState.remaining setup.program next.saved =
          ProtocolState.remaining setup.program (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) ∨
      (next.generation = state.generation ∧
        ProtocolState.remaining setup.program next.saved =
          ProtocolState.commitEnd setup.program (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))) := by
  have chosen := checkpoint.chosen_commit_trace native committing closed reached instructions
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord] at instructions
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, priorTrace, views,
    historyAlignment, origin⟩
  dsimp only at committing instructions chosen ⊢
  generalize decomposition : commitPhase program = segment at instructions chosen ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only at instructions chosen ⊢
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [CommitPrefix.length]; omega
  let start := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) source)) state.entry.excluded state.generation
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding native source
    state.entry.excluded
  let final := (start.install
    (lift (block.liftPoint suffix (ProtocolState.entry suffix decoded.1)), decoded.2.1)
      (fun _ member => decoded.2.2.excluded_subset member)).close
  have wholeCommit : ProtocolState.atCommit setup.program start.point = true :=
    (commits _).trans committing
  have ending : ProtocolState.commitEnd setup.program start.saved = instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (block.prepend suffix) source)) = _
    rw [origin.commitEnd_lift, block.commitEnd_entry_prepend suffix boundary]
  obtain ⟨canonicalTrace, _canonicalReached, _canonicalInstructions, same, _addresses⟩ := chosen
  have states := congrArg (fun result : setup.commitRecoveryProtocol.History => result.state) same
  have rawRank : ProtocolState.remaining setup.program
      (lift (block.liftPoint suffix (ProtocolState.entry suffix decoded.1))) =
      instructionCount suffix := by
    rw [ranks, block.liftPoint_remaining, ProtocolState.remaining_entry]
  have complete : (start.install
      (lift (block.liftPoint suffix (ProtocolState.entry suffix decoded.1)), decoded.2.1)
        (fun _ member => decoded.2.2.excluded_subset member)).Finished := by
    exact ⟨wholeCommit, rawRank.trans ending.symm⟩
  refine ⟨final, states, ?_, finished_close_control _ complete⟩
  change (CommitRecoveryState.close _).saved = (CommitRecoveryState.close _).point
  unfold CommitRecoveryState.close
  simp only [complete, ↓reduceIte]
  split
  · split <;> rfl
  · rfl

end Vegas

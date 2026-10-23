/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhasePublicSourceChronology
import Vegas.Game.RecoveryInitialCheckpoint
import Vegas.Game.RecoveryChosenCommitControl

/-! # The initialized native scan of the retained chosen source chronology -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace RecoverySourceCheckpoint

/-- The genuine chosen source prefix has precisely the native-observable
logical addresses through its saved boundary. -/
structure PublicChronology
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode)) : Prop where
  addresses : setup.recoveryAddressWord checkpoint.trace =
    state.sourcePublicAddressWord plan state.attempt.phase
  consumed : plan.sourceArchiveCursor (PhaseRuntimeState.sourceControlRecords state.retired)
    0 ∅ ≤ state.attempt.phase

/-- Unfinished physical effects preserve the same actual source prefix and
its public scan. Only completed events below the saved cutoff are used. -/
theorem PublicChronology.current
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (valid : checkpoint.PublicChronology plan)
    (current : RecoveryState ((toEventGraph setup.program).withMode mode))
    (extension : state.current.native.PublicFailureExtension current.native)
    (completed : ∀ event, event.val < state.attempt.phase →
      event ∈ state.current.native.config.cut.completed) :
    PublicChronology
      (checkpoint.transfer (other := {state with current := current}) rfl rfl rfl) plan := by
  refine ⟨?_, valid.consumed⟩
  change setup.recoveryAddressWord checkpoint.trace = _
  exact valid.addresses.trans (PhaseRuntimeState.sourcePublicAddressWord_eq_of_prefix
    (first := state) (second := {state with current := current}) plan rfl rfl
    (fun rank bounded => extension.failureOwnersBefore_eq_below state.attempt.phase
      completed rank bounded) state.attempt.phase)

/-- A genuine public-instruction chunk extends the initialized scan. Its
exclusions are derived from the saved native prefix and per-slot annotations. -/
theorem PublicChronology.advance_public
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode nextState)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (valid : checkpoint.PublicChronology plan)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (member : phase ∈ plan.phases)
    (noncommit : phase.kind ≠ .commitment)
    (frontier : state.Frontier) (archives : state.ArchivedExclusions)
    (savedFailures : state.PublicFailureCheckpoint)
    (extension : state.current.native.PublicFailureExtension nextState.entry.native)
    (sameArchives : nextState.retired = state.retired)
    (sameGeneration : nextState.generation = state.generation)
    (boundary : nextState.attempt.phase = phase.high)
    (fresh : nextState.current = nextState.entry)
    (chunk : ∃ states : List (ProtocolState setup.program × Finset Player),
      ((checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
        state.entry.excluded) :: states).IsChain
          (NativePublicSourceStep nextState.entry.native 0 setup.program) ∧
      ((checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
        state.entry.excluded) :: states).getLast (List.cons_ne_nil _ _) =
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
            nextState.entry.excluded) ∧
      setup.recoveryAddressWord next.trace = setup.recoveryAddressWord checkpoint.trace ++
        states.map (fun point =>
          (CommitRecoveryState.atPoint point.1 point.2 state.generation).publicAddress)) :
    next.PublicChronology plan := by
  obtain ⟨states, chain, ending, word⟩ := chunk
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  have positioned := frontier.positioned
  rw [installed] at positioned
  have complete : ∀ event, event.val < state.attempt.phase →
      event ∈ state.current.native.config.cut.completed := by
    rw [low]
    exact positioned.2.1
  have moved := PublicChronology.current checkpoint plan valid nextState.entry extension complete
  have movedWord : setup.recoveryAddressWord checkpoint.trace =
      [(some 0, (∅, 0, 0))] ++ plan.sourceArchiveAddresses
        nextState.entry.native.failureOwnersBefore state.generation state.attempt.phase
        (PhaseRuntimeState.sourceControlRecords state.retired) 0 ∅ := by
    exact moved.addresses.trans
      (PhaseRuntimeState.sourcePublicAddressWord_saved plan {state with current := nextState.entry})
  have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    rw [low]
    exact positioned.1
  have retained := savedFailures.trans extension
  have excluded : state.entry.excluded =
      PhaseRuntimeState.archivedFailureOwners state.retired ∪
        nextState.entry.native.failureOwnersBefore state.attempt.phase := by
    rw [archives.saved_eq, ← retained.failureOwnersBefore_eq state.attempt.phase saved]
  have firstPosition := checkpoint.saved_position
  have lastPosition := next.saved_position
  have length := NativePublicSourceStep.path_length _ _ states chain ending
  rw [firstPosition, lastPosition, low, boundary] at length
  have count : states.length = phase.high - phase.low := by omega
  have scan := native_public_path_addresses setup mode nextState.entry.native
    (PhaseRuntimeState.archivedFailureOwners state.retired) state.generation _ states chain
    (by simpa only [firstPosition] using excluded)
  rw [firstPosition, low, count] at scan
  have interval : states.map (fun point =>
        (CommitRecoveryState.atPoint point.1 point.2 state.generation).publicAddress) =
      plan.sourceAddressInterval nextState.entry.native.failureOwnersBefore
        (PhaseRuntimeState.archivedFailureOwners state.retired) state.generation
        phase.low phase.high := by
    rw [scan]
    apply List.map_congr_left
    intro index inside
    have bound := List.mem_range.mp inside
    have rankLow : phase.low < phase.low + index + 1 := by omega
    have rankHigh : phase.low + index + 1 ≤ phase.high := by omega
    simp only [plan.sourceSavedRank_of_public_interval
      phase member noncommit _ rankLow rankHigh]
  have cursorBound : plan.sourceArchiveCursor
      (PhaseRuntimeState.sourceControlRecords state.retired) 0 ∅ ≤ phase.low := by
    simpa only [low] using valid.consumed
  have joined := plan.sourceArchiveAddresses_extend nextState.entry.native.failureOwnersBefore
    state.generation phase.low phase.high
    (PhaseRuntimeState.sourceControlRecords state.retired) 0 ∅ cursorBound phase.nonempty.le
  have failures := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords state.retired
  unfold RuntimePhasePlan.sourceRecordFailures at failures
  rw [Finset.empty_union, failures] at joined
  refine ⟨?_, ?_⟩
  · rw [word, interval, movedWord,
      PhaseRuntimeState.sourcePublicAddressWord_saved]
    rw [low, List.append_assoc, ← joined]
    rw [fresh, sameArchives, sameGeneration, boundary]
  · rw [sameArchives, boundary]
    exact cursorBound.trans phase.nonempty.le

/-- A real failed commitment close appends its original completed archive
once. Retry and exhausted restore use their actual, different close cursors. -/
theorem PublicChronology.failed_commit
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode nextState)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (valid : checkpoint.PublicChronology plan)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (member : phase ∈ plan.phases)
    (kind : phase.kind = .commitment) (frontier : state.Frontier)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (archives : state.ArchivedExclusions) (savedFailures : state.PublicFailureCheckpoint)
    (finished : phase.Finished (phase.drain state.current))
    (nextArchives : nextState.retired = state.retired ++
      [⟨⟨phase.low, state.generation⟩, (phase.drain state.current).native⟩])
    (nextExcluded : nextState.entry.excluded = (phase.drain state.current).excluded)
    (nextGeneration : nextState.generation = state.generation +
      if (phase.owners \ (phase.drain state.current).excluded).Nonempty then 1 else 0)
    (nextRank : nextState.attempt.phase =
      if (phase.owners \ (phase.drain state.current).excluded).Nonempty
        then phase.low else phase.high)
    {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (instructions : setup.recoveryJointRecall next.trace =
      (checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace) :
    next.PublicChronology plan := by
  let image := phase.drain state.current
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  have positioned := frontier.positioned
  rw [installed] at positioned
  have complete : ∀ event, event.val < state.attempt.phase →
      event ∈ state.current.native.config.cut.completed := by
    rw [low]
    exact positioned.2.1
  have moved := PublicChronology.current checkpoint plan valid image
    (phase.drain_publicFailureExtension state.current) complete
  have movedWord : setup.recoveryAddressWord checkpoint.trace =
      [(some 0, (∅, 0, 0))] ++ plan.sourceArchiveAddresses
        image.native.failureOwnersBefore state.generation state.attempt.phase
        (PhaseRuntimeState.sourceControlRecords state.retired) 0 ∅ := by
    exact moved.addresses.trans
      (PhaseRuntimeState.sourcePublicAddressWord_saved plan {state with current := image})
  obtain ⟨addresses, word, _interior, ending, interiorWord⟩ :=
    checkpoint.chosen_commit_public_scan phase remaining installed kind frontier maximal
      archives savedFailures finished ⟨_, next.trace⟩ reached instructions
  let closeRank := if (phase.owners \ image.excluded).Nonempty then phase.low else phase.high
  let closeGeneration := state.generation +
    if (phase.owners \ image.excluded).Nonempty then 1 else 0
  let closeAddress := (some closeRank, image.excluded, closeGeneration, closeRank)
  have lastAddress : addresses.getLast? = some closeAddress := by
    rw [ending]
    change some (some (instructionCount setup.program - ProtocolState.remaining setup.program
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source))),
      nextState.entry.excluded, nextState.generation,
      instructionCount setup.program - ProtocolState.remaining setup.program
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source))) = _
    rw [next.saved_position, nextRank, nextExcluded, nextGeneration]
  have rebuilt := List.dropLast_append_getLast? closeAddress (by
    rw [lastAddress]
    exact Option.mem_some_iff.mpr rfl)
  have interval := plan.sourceAddressInterval_commit_dropLast image.native.failureOwnersBefore
    (PhaseRuntimeState.archivedFailureOwners state.retired) state.generation phase member kind
  rw [low] at interiorWord
  rw [← rebuilt, interiorWord, ← interval, movedWord] at word
  have parsed := PhaseRuntimeState.sourceArchiveAddresses_after_completed plan state phase
    member kind archives nextState.current.native.failureOwnersBefore nextState.generation
    nextState.attempt.phase
  rw [nextRank] at parsed
  change plan.sourceArchiveAddresses _ _ closeRank _ 0 ∅ = _ at parsed
  simp only [RuntimePhasePlan.sourceAddressInterval, Nat.sub_self, List.range_zero,
    List.map_nil, List.append_nil] at parsed
  refine ⟨?_, ?_⟩
  · rw [PhaseRuntimeState.sourcePublicAddressWord_saved, nextArchives, nextRank, parsed]
    rw [low] at word
    simpa only [image, closeRank, closeGeneration, closeAddress, List.append_assoc,
      RuntimePhasePlan.sourceAddressInterval] using word
  · rw [nextArchives, PhaseRuntimeState.sourceArchiveCursor_after_completed plan state phase
      member kind archives, nextRank]

/-- A successful commitment block consumes its whole interval without
appending an archive. Its last signal is the saved high boundary. -/
theorem PublicChronology.clean_commit
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode nextState)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (valid : checkpoint.PublicChronology plan)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (member : phase ∈ plan.phases)
    (kind : phase.kind = .commitment) (frontier : state.Frontier)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (archives : state.ArchivedExclusions) (savedFailures : state.PublicFailureCheckpoint)
    (finished : phase.Finished (phase.drain state.current))
    (sameArchives : nextState.retired = state.retired)
    (sameGeneration : nextState.generation = state.generation)
    (boundary : nextState.attempt.phase = phase.high)
    (nextEntry : nextState.entry = phase.drain state.current)
    (fresh : nextState.current = nextState.entry)
    {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (instructions : setup.recoveryJointRecall next.trace =
      (checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace) :
    next.PublicChronology plan := by
  let image := phase.drain state.current
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  have positioned := frontier.positioned
  rw [installed] at positioned
  have complete : ∀ event, event.val < state.attempt.phase →
      event ∈ state.current.native.config.cut.completed := by
    rw [low]
    exact positioned.2.1
  have moved := PublicChronology.current checkpoint plan valid image
    (phase.drain_publicFailureExtension state.current) complete
  have movedWord : setup.recoveryAddressWord checkpoint.trace =
      [(some 0, (∅, 0, 0))] ++ plan.sourceArchiveAddresses
        image.native.failureOwnersBefore state.generation state.attempt.phase
        (PhaseRuntimeState.sourceControlRecords state.retired) 0 ∅ := by
    exact moved.addresses.trans
      (PhaseRuntimeState.sourcePublicAddressWord_saved plan {state with current := image})
  obtain ⟨addresses, word, _interior, ending, interiorWord⟩ :=
    checkpoint.chosen_commit_public_scan phase remaining installed kind frontier maximal
      archives savedFailures finished ⟨_, next.trace⟩ reached instructions
  have lastAddress : addresses.getLast? =
      some (some phase.high, image.excluded, state.generation, phase.high) := by
    rw [ending]
    change some (some (instructionCount setup.program - ProtocolState.remaining setup.program
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source))),
      nextState.entry.excluded, nextState.generation,
      instructionCount setup.program - ProtocolState.remaining setup.program
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source))) = _
    rw [next.saved_position, boundary, nextEntry, sameGeneration]
  have rebuilt := List.dropLast_append_getLast? _ (by
    rw [lastAddress]
    exact Option.mem_some_iff.mpr rfl)
  have interval := plan.sourceAddressInterval_commit_dropLast image.native.failureOwnersBefore
    (PhaseRuntimeState.archivedFailureOwners state.retired) state.generation phase member kind
  rw [low] at interiorWord
  have within := phase.drain_within state.current positioned.2
  have completedPrefix := phase.finished_prefix image within finished
  have failurePrefix := (State.PublicFailureExtension.refl image.native).failureOwnersBefore_eq
    phase.high completedPrefix
  have exclusion := (archives.active.phase_drain phase).failureOwners_union
  rw [← failurePrefix] at exclusion
  have whole := plan.sourceAddressInterval_last image.native.failureOwnersBefore
    (PhaseRuntimeState.archivedFailureOwners state.retired) state.generation phase member
  have intervalEq : addresses = plan.sourceAddressInterval image.native.failureOwnersBefore
      (PhaseRuntimeState.archivedFailureOwners state.retired) state.generation
        phase.low phase.high := by
    rw [← rebuilt, interiorWord, ← interval]
    simpa only [← exclusion] using whole.symm
  have bound : plan.sourceArchiveCursor
      (PhaseRuntimeState.sourceControlRecords state.retired) 0 ∅ ≤ phase.low := by
    simpa only [low] using valid.consumed
  have joined := plan.sourceArchiveAddresses_extend image.native.failureOwnersBefore
    state.generation phase.low phase.high
    (PhaseRuntimeState.sourceControlRecords state.retired) 0 ∅ bound phase.nonempty.le
  have failures := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords state.retired
  unfold RuntimePhasePlan.sourceRecordFailures at failures
  rw [Finset.empty_union, failures] at joined
  refine ⟨?_, ?_⟩
  · rw [word, intervalEq, movedWord,
      PhaseRuntimeState.sourcePublicAddressWord_saved]
    rw [low, List.append_assoc, ← joined, fresh, nextEntry, sameArchives,
      sameGeneration, boundary]
  · rw [sameArchives, boundary]
    exact bound.trans phase.nonempty.le

private theorem publicChronology_cast
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state other : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (same : state = other) (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (valid : checkpoint.PublicChronology plan) :
    (cast (congrArg (RecoverySourceCheckpoint setup mode) same) checkpoint).PublicChronology
      plan := by
  cases same
  exact valid

/-- The original supported setup is the one actual initialization transition;
no native phase or retry introduces an additional source setup signal. -/
theorem initialized_publicChronology
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
    (RecoverySourceCheckpoint.initialized setup mode plan initial supported).PublicChronology
      plan := by
  unfold RecoverySourceCheckpoint.initialized
  apply publicChronology_cast (phaseInitial_eq_raw plan (encodeInputs initial)).symm
    (RecoverySourceCheckpoint.initial setup mode plan initial supported) plan
  let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
    ⟨plan.phases, 0, ⟨EventGraphRuntime.State.initial (encodeInputs initial), ∅⟩,
      ⟨EventGraphRuntime.State.initial (encodeInputs initial), ∅⟩, []⟩
  have position := RecoverySourceCheckpoint.saved_position
    (RecoverySourceCheckpoint.initial setup mode plan initial supported)
  have offset : raw.attempt.phase = 0 := by
    simpa only [RecoverySourceCheckpoint.initial, id_eq, ProtocolState.remaining_entry,
      Nat.sub_self] using position.symm
  refine ⟨?_, Nat.zero_le _⟩
  change setup.recoveryAddressWord
    (RecoverySourceCheckpoint.initial setup mode plan initial supported).trace =
      raw.sourcePublicAddressWord plan raw.attempt.phase
  rw [offset]
  change [(CommitRecoveryState.atPoint
    (ProtocolState.entry setup.program (setup.initialConfig initial)) ∅ 0).publicAddress] = _
  simp only [PhaseRuntimeState.sourcePublicAddressWord, offset]
  simp only [CommitRecoveryState.publicAddress, CommitRecoveryState.atPoint,
    ProtocolState.remaining_entry, Nat.sub_self,
    raw, PhaseRuntimeState.sourceControlRecords, List.map_nil,
    RuntimePhasePlan.sourceArchiveAddresses, RuntimePhasePlan.sourceAddressInterval,
    List.range_zero, List.map_nil, List.append_nil, List.foldr_nil]

end RecoverySourceCheckpoint
end Vegas

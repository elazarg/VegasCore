/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryRevealCheckpoint
import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Game.SequentialRuntimePhases
import Vegas.Compile.CommitPrefixView
import Vegas.Game.PhaseSurvivingSourceView
import Vegas.Game.RecoverySourceReadout

/-! # Current source cursors inside sequential disclosure intervals -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A completed strict prefix of an actual disclosure phase advances its
saved source checkpoint to the genuine current sequential cursor. -/
theorem RecoverySourceCheckpoint.current_reveal_prefix
    {setup : Setup (Player := Player) (L := L)}
    {state : PhaseRuntimeState (serviceGraph setup .sequential)}
    (checkpoint : RecoverySourceCheckpoint setup .sequential state)
    (phase : RuntimePhase (serviceGraph setup .sequential))
    (remaining : List (RuntimePhase (serviceGraph setup .sequential)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .reveal)
    (exclusion : state.ExclusionRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint) {inputs}
    (reachable : state.current.native.config.Reachable inputs)
    (ordered : state.current.OrderedPublicFailures phase.low state.entry.excluded)
    (event : (serviceGraph setup .sequential).EventId)
    (ready : state.current.native.config.cut.Ready event)
    (lower : phase.low < event.val) (upper : event.val < phase.high) :
    ∃ (nextState : PhaseRuntimeState (serviceGraph setup .sequential))
      (next : RecoverySourceCheckpoint setup .sequential nextState),
      nextState.entry = state.current ∧ nextState.current = state.current ∧
      nextState.generation = state.generation ∧ nextState.retired = state.retired ∧
      nextState.attempt.phase = event.val ∧
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩) ∧
      (∃ states : List (ProtocolState setup.program × Finset Player),
        ((checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
          state.entry.excluded) :: states).IsChain
            (NativePublicSourceStep state.current.native 0 setup.program) ∧
        ((checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
          state.entry.excluded) :: states).getLast (List.cons_ne_nil _ _) =
            (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
              state.current.excluded) ∧
        setup.recoveryAddressWord next.trace = setup.recoveryAddressWord checkpoint.trace ++
          states.map (fun point =>
            (CommitRecoveryState.atPoint point.1 point.2 state.generation).publicAddress)) ∧
      (∀ who, who ∉ state.current.excluded →
        next.source.history who = checkpoint.source.history who ++
          (decodeHistory setup.program (state.current.native.config.history.map
            ((toEventGraph setup.program).fromModeCompletion .sequential)) who).drop
              (decodeHistory setup.program (state.entry.native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion .sequential)) who).length) := by
  let first : RuntimePhase (serviceGraph setup .sequential) :=
    { phase with
      high := event.val
      nonempty := lower
      bounded := event.isLt.le
      fields := fun selected low high => phase.fields selected low (high.trans upper)
      sample_singleton := fun impossible => False.elim (by
        rw [kind] at impossible
        cases impossible) }
  let later : RuntimePhase (serviceGraph setup .sequential) :=
    { phase with
      low := event.val
      nonempty := upper
      fields := fun selected low high => phase.fields selected (lower.le.trans low) high
      sample_singleton := fun impossible => False.elim (by
        rw [kind] at impossible
        cases impossible) }
  let split : PhaseRuntimeState (serviceGraph setup .sequential) :=
    { state with phases := first :: later :: remaining }
  have sameOffset : split.attempt.phase = state.attempt.phase := by
    simp only [split, first, PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  let saved := checkpoint.transfer (other := split) rfl rfl sameOffset
  have currentPrefix : state.current.native.config.cut.IsPrefix event.val :=
    ⟨event.isLt.le, fun selected =>
      (toEventGraph setup.program).sequentialize_mem_completed_iff_lt_of_ready
        state.current.native.config.cut ready⟩
  have finished : first.Finished state.current := by
    intro selected member
    exact (currentPrefix.2 selected).mpr ((first.mem_events selected).mp member).2
  have drained : first.drain state.current = state.current := by
    apply first.drain_eq_of_clear
    intro selected eligible
    exact eligible.2.1.1 (finished eligible.1)
  have position := exclusion.frontier.positioned
  have adjacent := exclusion.frontier.adjacent
  have last := exclusion.frontier.last
  rw [installed] at position adjacent last
  have splitAdjacent : (first :: later :: remaining).IsChain
      (fun before after => before.high = after.low) := by
    rw [List.isChain_cons_cons]
    refine ⟨rfl, ?_⟩
    cases remaining with
    | nil => exact .singleton _
    | cons next rest =>
        simpa only [List.isChain_cons_cons, later] using adjacent
  have splitLast : ∀ final ∈ (first :: later :: remaining).getLast?,
      final.high = (serviceGraph setup .sequential).order.eventCount := by
    cases remaining with
    | nil =>
        intro final member
        have same : final = later := by
          symm
          simpa only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff]
            using member
        subst final
        exact last phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
    | cons next rest =>
        simpa only [List.getLast?_cons_cons] using last
  have splitRecord : split.ExclusionRecord := by
    refine ⟨⟨splitAdjacent, splitLast, position.1, ?_⟩, exclusion.saved, exclusion.active, ?_⟩
    · exact ⟨position.2.1, fun selected completed => (currentPrefix.2 selected).mp completed⟩
    · intro selected member
      have same : selected = first := by
        symm
        simpa only [split, List.head?_cons, Option.mem_some_iff] using member
      subst selected
      exact exclusion.installed phase (by rw [installed]; exact Option.mem_some_iff.mpr rfl)
  obtain ⟨next, path, _steps, addresses, word, _intended, _replay⟩ := saved.after_reveal first
    (later :: remaining) rfl kind splitRecord stored remembered
      (by rwa [drained]) (by rwa [drained]) (by rwa [drained])
  refine ⟨_, next, drained, drained, rfl, rfl, ?_, path, ?_, ?_⟩
  · simp only [PhaseRuntimeState.attempt, List.head?_cons, Option.map_some,
      Option.getD_some, later]
  · simpa [split, drained, saved, RecoverySourceCheckpoint.transfer] using addresses
  · simpa [split, drained, saved, RecoverySourceCheckpoint.transfer] using word

omit [DecidableEq Player] in
private theorem config_history_eq_of_prefix_cut_eq {graph : Vegas.EventGraph Player L}
    (first second : graph.Config) (retained : first.history.IsPrefix second.history)
    (completed : first.cut.completed = second.cut.completed) : first.history = second.history := by
  classical
  have domains : (first.history.map EventGraph.Completion.event).toFinset =
      (second.history.map EventGraph.Completion.event).toFinset := by
    ext event
    simp only [List.mem_toFinset]
    rw [first.history_exact, second.history_exact, completed]
  have lengths := congrArg Finset.card domains
  rw [List.toFinset_card_of_nodup first.history_nodup,
    List.toFinset_card_of_nodup second.history_nodup, List.length_map, List.length_map] at lengths
  obtain ⟨later, joined⟩ := retained
  have zero : later = [] := by
    apply List.eq_nil_of_length_eq_zero
    have same := congrArg List.length joined
    simp only [List.length_append] at same
    omega
  simpa only [zero, List.append_nil] using joined

/-- At an exact current checkpoint, the whole typed syntax decoder reads
its source entry view at the actual next native event. -/
theorem RecoverySourceCheckpoint.entry_event_view
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (agree : checkpoint.refs.Agrees checkpoint.source.state
      state.current.native.config.store)
    (event : (serviceGraph setup mode).EventId)
    (rank : event.val = state.attempt.phase) (who : Player) :
    decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event
      ((serviceGraph setup mode).playerStore who state.current.native.config.store)
      (checkpoint.source.history who) =
      some (ProtocolState.observe who setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) := by
  have total := checkpoint.compiled.countEq
  have positive : 0 < eventCount checkpoint.residual.tail := by
    have bounded := event.isLt
    change event.val < eventCount setup.program at bounded
    omega
  let selected : Fin (eventCount checkpoint.residual.tail) := ⟨0, positive⟩
  have selectedEq : checkpoint.embedding.event selected = event := by
    apply Fin.ext
    rw [checkpoint.compiled.rankEq, rank]
    exact Nat.add_zero _
  have visible := (decodeObservation?_playerStore (graph := toEventGraph setup.program)
    who checkpoint.refs state.current.native.config.store).trans
      (decodeObservation?_eq_some _ who checkpoint.source.state _ agree)
  have localView := decodeEventView?_commitPrefix_entry setup.program
    (.nil : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names
      checkpoint.residual.context checkpoint.residual.names) checkpoint.residual.tail
        checkpoint.embedding checkpoint.refs
          ((toEventGraph setup.program).playerStore who state.current.native.config.store)
          checkpoint.source who selected rfl visible
  have localView' : decodeEventView? checkpoint.residual.tail checkpoint.refs
      checkpoint.embedding.ref who selected
      ((toEventGraph setup.program).playerStore who state.current.native.config.store)
      (checkpoint.source.history who) = some (ProtocolState.observe who checkpoint.residual.tail
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) := by
    simpa only [SourceProgram.CommitPrefix.prepend, SourceProgram.CommitPrefix.liftPoint]
      using localView
  rw [← selectedEq]
  exact (checkpoint.views.decode who selected _ _).trans
    ((congrArg (Option.map (checkpoint.views.view who)) localView').trans
      (congrArg some (checkpoint.views.observe who _).symm))

/-- The compiled next event and the source entry at an exact checkpoint
have the same actor, including actual public disclosure ownership. -/
theorem RecoverySourceCheckpoint.entry_event_actor
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (event : (serviceGraph setup mode).EventId) (rank : event.val = state.attempt.phase) :
    ProtocolState.actor setup.program (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) =
        (serviceGraph setup mode).actor? event := by
  rw [checkpoint.actor]
  have total := checkpoint.compiled.countEq
  have positive : 0 < eventCount checkpoint.residual.tail := by
    have bounded := event.isLt
    change event.val < eventCount setup.program at bounded
    omega
  let selected : Fin (eventCount checkpoint.residual.tail) := ⟨0, positive⟩
  have selectedEq : checkpoint.embedding.event selected = event := by
    apply Fin.ext
    rw [checkpoint.compiled.rankEq, rank]
    exact Nat.add_zero _
  have actor := (EventCode.actor_cast (checkpoint.embedding.layout_eq selected)
    ((toEventGraph setup.program).nodes (checkpoint.embedding.event selected))).symm.trans
      (congrArg EventCode.actor (checkpoint.compiled.nodeEq selected))
  rw [← selectedEq]
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, _origin⟩
  dsimp only at positive actor ⊢
  cases program with
  | ret => simp only [eventCount] at positive; omega
  | sample => exact actor.symm
  | commit => exact actor.symm
  | reveal => exact actor.symm

namespace EventGraphRuntime.PhaseRuntimeState

variable [Fintype Player] {graph : Vegas.EventGraph Player L}

/-- Public disclosures save the new cursor after each original instruction. -/
def sourceCurrentRevealAddressWord (plan : RuntimePhasePlan graph)
    (state : PhaseRuntimeState graph) (eventRank : Nat) :
    List (Option Nat × (Finset Player × Nat × Nat)) :=
  state.sourcePublicAddressWord plan state.attempt.phase ++
    (List.range (eventRank - state.attempt.phase)).map fun index =>
      let rank := state.attempt.phase + index + 1
      (some rank, archivedFailureOwners state.retired ∪
        state.current.native.failureOwnersBefore rank, state.generation, rank)

end EventGraphRuntime.PhaseRuntimeState

/-- The actual surviving source cursor at any initialized sequential disclosure
request, including earlier failed openings and all retained attempt words. -/
theorem phase_ready_reveal_current_source [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (serviceGraph setup .sequential))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup .sequential)))
    (plan : RuntimePhasePlan (serviceGraph setup .sequential))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (publication : (serviceGraph setup .sequential).outputLayout event = .publication payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.current.excluded ∧
      source.generation = control.execution.application.generation ∧
      setup.commitRecoveryPublic (some source) =
        (control.execution.application.current.excluded,
          control.execution.application.generation, event.val) ∧
      ProtocolState.actor setup.program source.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      phaseSurvivingSourceView? setup .sequential runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) =
          some (ProtocolState.observe who setup.program source.point) ∧
      setup.recoveryAddressWord sourceTrace =
        control.execution.application.sourceCurrentRevealAddressWord plan event.val := by
  classical
  let state := control.execution.application
  obtain ⟨phase, member, inside⟩ := request.2.1
  change phase ∈ state.phases.head? at member
  obtain ⟨remaining, installed⟩ : ∃ remaining, state.phases = phase :: remaining := by
    cases listEq : state.phases with
    | nil => simp only [listEq, List.head?_nil, Option.not_mem_none] at member
    | cons selected rest =>
        have same : selected = phase := by
          simpa only [listEq, List.head?_cons, Option.mem_some_iff] using member
        exact ⟨rest, by rw [same]⟩
  have interval := (phase.mem_events event).mp inside
  have typed := phase.fields event interval.1 interval.2
  have kind : phase.kind = .reveal := by
    cases kind : phase.kind with
    | commitment =>
        rw [kind] at typed
        obtain ⟨owner, value, layout⟩ := typed
        rw [publication] at layout
        cases layout
    | reveal => rfl
    | sample =>
        rw [kind] at typed
        obtain ⟨value, layout⟩ := typed
        rw [publication] at layout
        cases layout
  let inputs : PMF (serviceGraph setup .sequential).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨checkpoint, aligned, chronology, _origins⟩ := recoverySourceCheckpoint_history setup
    .sequential runtime leaks plan maximal horizon scheduler trace
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have remembered := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have archives := PhaseRuntimeState.archivesBefore_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have archiveExclusions := phaseArchivedExclusions_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have savedFailures := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  obtain ⟨_input, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler physicalTrace
  have order := phasePublicFailureOrder_history runtime leaks
    (serviceGraph_revealRelaxedOrdered setup .sequential) plan inputs horizon scheduler
      physicalTrace
  have low : phase.low = state.attempt.phase := by
    simp only [state, PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have savedPrefix : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    have position := exclusion.frontier.positioned
    rw [installed] at position
    simpa only [← low] using position.1
  have active : who ∉ state.current.excluded := request.2.2.2.2
  have entryActive : who ∉ state.entry.excluded :=
    fun excluded => active (order.coverage.inherited excluded)
  have before : state.entry.excluded =
      PhaseRuntimeState.archivedFailureOwners state.retired ∪
        state.current.native.failureOwnersBefore state.attempt.phase := by
    rw [archiveExclusions.saved_eq,
      ← savedFailures.failureOwnersBefore_eq state.attempt.phase savedPrefix]
  by_cases positive : phase.low < event.val
  · obtain ⟨nextState, next, entryEq, currentEq, generationEq, retiredEq, position,
      path, addresses, word⟩ := checkpoint.current_reveal_prefix phase remaining installed kind
      exclusion stored remembered native.active.reachable (order.publicationOrder phase member)
      event request.2.2.1 positive interval.2
    let source := CommitRecoveryState.atPoint (next.residual.lift
      (ProtocolState.entry next.residual.tail next.source)) nextState.entry.excluded
        nextState.generation
    have sourceActive : who ∉ source.excluded := by
      change who ∉ nextState.entry.excluded
      rwa [entryEq]
    have actor := (next.entry_event_actor event position.symm).trans request.2.2.2.1
    have sourcePublic : setup.commitRecoveryPublic (some source) =
        (state.current.excluded, state.generation, event.val) := by
      change (nextState.entry.excluded, nextState.generation,
        instructionCount setup.program - ProtocolState.remaining setup.program
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source))) = _
      rw [next.saved_position, entryEq, generationEq, position]
    have ownWord : next.source.history who = decodeHistory setup.program
        ((PhaseRuntimeState.archivedHistory state.retired state.current.native.config.history).map
          ((toEventGraph setup.program).fromModeCompletion .sequential)) who := by
      rw [word who active, aligned who entryActive]
      exact (decodeArchivedHistory_checkpoint_extension setup.program .sequential state.retired
        state.entry.native.config state.current.native.config state.attempt.phase archives
          savedPrefix remembered who).symm
    have agreement : next.refs.Agrees next.source.state nextState.current.native.config.store := by
      rw [currentEq, ← entryEq]
      exact next.agrees
    have decoded := next.entry_event_view agreement event position.symm who
    rw [currentEq, ownWord] at decoded
    obtain ⟨states, chain, ending, numeric⟩ := addresses
    have oldRank := checkpoint.saved_position
    have nextRank := next.saved_position
    rw [position] at nextRank
    have count := NativePublicSourceStep.path_length _ _ states chain ending
    rw [oldRank, nextRank] at count
    change event.val = state.attempt.phase + states.length at count
    have length : states.length = event.val - state.attempt.phase := by omega
    have actualAddresses := native_public_path_addresses setup .sequential state.current.native
      (PhaseRuntimeState.archivedFailureOwners state.retired) state.generation _ states chain
        (by rwa [oldRank])
    rw [oldRank, length] at actualAddresses
    refine ⟨source, next.trace, ?_, generationEq, sourcePublic, actor,
      commitRecovery_isDecisionInfo_of_surviving_actor setup source next.trace who sourceActive
        actor, ?_, ?_⟩
    · exact congrArg RecoveryState.excluded entryEq
    · rw [phaseSurvivingSourceView?_observed_of_history setup .sequential runtime leaks plan inputs
        horizon scheduler physicalTrace who event]
      exact decoded
    · rw [numeric, actualAddresses, chronology.addresses]
      rfl
  · have sameRank : event.val = state.attempt.phase := by omega
    have currentPrefix : state.current.native.config.cut.IsPrefix state.attempt.phase := by
      refine ⟨savedPrefix.1, ?_⟩
      intro selected
      rw [← sameRank]
      exact (toEventGraph setup.program).sequentialize_mem_completed_iff_lt_of_ready
        state.current.native.config.cut request.2.2.1
    have sameCut : state.entry.native.config.cut.completed =
        state.current.native.config.cut.completed := by
      ext selected
      rw [savedPrefix.2, currentPrefix.2]
    have historyEq := config_history_eq_of_prefix_cut_eq state.entry.native.config
      state.current.native.config remembered sameCut
    have excludedEq : state.current.excluded = state.entry.excluded := by
      ext owner
      rw [(exclusion.installed phase member).excluded]
      constructor
      · rintro (old | ⟨failed, lower, _acting, failure⟩)
        · exact old
        · have upper := (currentPrefix.2 failed).mp failure.completed
          omega
      · exact Or.inl
    let source := CommitRecoveryState.atPoint (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) state.entry.excluded
        state.generation
    have actor := (checkpoint.entry_event_actor event sameRank).trans request.2.2.2.1
    have ownWord : checkpoint.source.history who = decodeHistory setup.program
        ((PhaseRuntimeState.archivedHistory state.retired state.current.native.config.history).map
          ((toEventGraph setup.program).fromModeCompletion .sequential)) who := by
      rw [← historyEq]
      exact aligned who entryActive
    have decoded := checkpoint.entry_event_view (checkpoint.current_agrees stored) event
      sameRank who
    rw [ownWord] at decoded
    refine ⟨source, checkpoint.trace, excludedEq.symm, rfl, ?_, actor,
      commitRecovery_isDecisionInfo_of_surviving_actor setup source checkpoint.trace who entryActive
        actor, ?_, ?_⟩
    · change (state.entry.excluded, state.generation,
        instructionCount setup.program - ProtocolState.remaining setup.program
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) = _
      rw [checkpoint.saved_position, sameRank, excludedEq]
    · rw [phaseSurvivingSourceView?_observed_of_history setup .sequential runtime leaks plan inputs
        horizon scheduler physicalTrace who event]
      exact decoded
    · rw [chronology.addresses]
      simp only [state] at sameRank
      simp only [PhaseRuntimeState.sourceCurrentRevealAddressWord, sameRank, Nat.sub_self,
        List.range_zero, List.map_nil, List.append_nil]

end Vegas

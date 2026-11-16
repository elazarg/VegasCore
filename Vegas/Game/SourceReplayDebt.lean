module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceDecodedDebt
public import Vegas.Game.SourceDebtObservation
public import Vegas.Source.CellSwapDebt
public import Vegas.EventGraph.RecordedReplay
public import Vegas.EventGraph.BindingPrefixObservation

@[expose] public section

/-! # Owed failures along source replay continuations

An existing source residual transports debt through arbitrary supported graph
continuations. At completion this produces an owned failed reveal. A matching
initialized source trace also supplies public-default provenance, yielding the
fixed-exit branch. Debt can be transferred from another source point through
its own observation without identifying hidden foreign values.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem point_eq_of_terminal_readout :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    (final : Config Player L program.terminalCtx) →
    ProtocolState.readout program left = some final →
    ProtocolState.readout program right = some final → left = right
  | _, _, .ret _, _, _, _, leftRead, rightRead =>
      Option.some.inj (leftRead.trans rightRead.symm)
  | _, _, .sample _ _ _ next, left, right, final, leftRead, rightRead
  | _, _, .commit _ _ _ _ next, left, right, final, leftRead, rightRead
  | _, _, .reveal _ _ _ _ _ _ next, left, right, final, leftRead, rightRead => by
      cases left with
      | inl _ => cases leftRead
      | inr left =>
          cases right with
          | inl _ => cases rightRead
          | inr right =>
              exact congrArg Sum.inr (point_eq_of_terminal_readout next left right final
                leftRead rightRead)

private theorem SourceResidual.terminal_owed_of_replay_prefix
    {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {before final : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank before)
    (path : Relation.ReflTransGen EventGraph.Config.Step before final)
    (terminal : final.cut.Terminal) (who : Player) (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (owed : ProtocolState.OwesFailure who setup.program point) :
    ∃ finalPoint : ProtocolState setup.program,
      ProtocolState.OwesFailure who setup.program finalPoint ∧
      ProtocolState.readout setup.program finalPoint =
        some (terminalConfig setup.program ⟨final, terminal⟩) := by
  have holds : DecodedHolds (ProtocolState.OwesFailure who setup.program) rank before := by
    intro state read
    rw [decoded, Option.some.injEq] at read
    exact read ▸ owed
  obtain ⟨lastRank, ⟨lastResidual⟩, remains⟩ :=
    residual.decodedHolds_path (owesFailure_stepClosed who) holds path
  have full : final.cut.IsPrefix (eventCount setup.program) := by
    refine ⟨le_rfl, fun event => ?_⟩
    rw [terminal]
    exact iff_of_true (Finset.mem_univ _) event.isLt
  have atEnd := lastResidual.checkpoint.ordered.unique full
  subst lastRank
  let finalPoint := lastResidual.lift (ProtocolState.entry lastResidual.program lastResidual.source)
  have finalOwed : ProtocolState.OwesFailure who setup.program finalPoint :=
    remains _ lastResidual.decode
  have read := sourceServicePrefix?_terminal_readout setup final
  rw [lastResidual.decode, decodeConfig?_terminal setup.program ⟨final, terminal⟩] at read
  exact ⟨finalPoint, finalOwed, read⟩

/-- Debt is the same at a replay prefix and any source point with matching own view
and static metadata. The replay prefix's static metadata comes from its decoder. -/
theorem owesFailure_of_sourcePrefix_observe_eq
    {setup : Setup (Player := Player) (L := L)}
    {rank : Nat}
    {before : setup.informationGraph.Config}
    (who : Player) (point other : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (otherStatic : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context)
      other)
    (same : ProtocolState.observe who setup.program other =
      ProtocolState.observe who setup.program point)
    (owed : ProtocolState.OwesFailure who setup.program other) :
    ProtocolState.OwesFailure who setup.program point := by
  have pointStatic := decodeSourcePrefix?_staticAt rank setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) before.store
    (decodeHistory setup.program before.history) before.defaults point decoded
  exact (ProtocolState.owesFailure_iff_of_observe_eq who setup.program []
    (Revelations.initial setup.context) other point otherStatic pointStatic same).mp owed

/-- Debt at a genuine source replay prefix forces a failed reveal at completion. -/
theorem SourceResidual.failedReveals_of_owesFailure_path
    {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {before final : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank before)
    (path : Relation.ReflTransGen EventGraph.Config.Step before final)
    (terminal : final.cut.Terminal) (who : Player) (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (owed : ProtocolState.OwesFailure who setup.program point) :
    1 ≤ failedReveals setup.program who
      (publicOutcome setup.program (terminalConfig setup.program ⟨final, terminal⟩)) := by
  obtain ⟨finalPoint, finalOwed, read⟩ :=
    residual.terminal_owed_of_replay_prefix path terminal who point decoded owed
  exact ProtocolState.failedReveals_pos_of_owesFailure who setup.program finalPoint finalOwed read

/-- A matching terminal source trace turns source debt into an actual public default. -/
theorem SourceResidual.defaulted_of_owesFailure_path
    {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {before final : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank before)
    (path : Relation.ReflTransGen EventGraph.Config.Step before final)
    (terminal : final.cut.Terminal) (who : Player) (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (owed : ProtocolState.OwesFailure who setup.program point)
    (initial : State L setup.context)
    (history : (executionProtocol setup.program (CommitmentInterface.forfeiture setup.program)
      (Config.initial initial)).History)
    (historyRead : ProtocolState.readout setup.program history.state =
      some (terminalConfig setup.program ⟨final, terminal⟩)) :
    who ∈ final.defaulted := by
  obtain ⟨finalPoint, finalOwed, read⟩ :=
    residual.terminal_owed_of_replay_prefix path terminal who point decoded owed
  have same := point_eq_of_terminal_readout setup.program finalPoint history.state
    (terminalConfig setup.program ⟨final, terminal⟩) read historyRead
  rw [same] at finalOwed
  exact ProtocolState.defaulted_of_owesFailure_trace setup.program
    (CommitmentInterface.forfeiture setup.program) (Config.initial initial) history.trace who
    finalOwed historyRead

section

open SourceProgram EventGraph

private theorem decodeSourcePrefix?_replace_history {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history replacement : History Player L)
      (defaults nextDefaults : DefaultHistory Player) (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
        some point →
      ∃ changed, decodeSourcePrefix? program refs registry revelations outputs count store
          replacement nextDefaults = some changed ∧
        ProtocolState.SameCells program point changed
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, replacement,
      defaults, nextDefaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨state, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      refine ⟨ProtocolState.entry program
        ⟨state, registry, revelations, replacement, nextDefaults⟩, ?_, ?_⟩
      · simp only [decodeSourcePrefix?, read, Option.map_some]
      · cases program <;> rfl
  | _ + 1, _, _, .ret _, _, _, _, _, _, _, _, _, _, _, decoded => by
      cases decoded
  | count + 1, _, _, .sample _ _ _ next, refs, registry, revelations, outputs, store, history,
      replacement, defaults, nextDefaults, point, decoded
  | count + 1, _, _, .commit _ _ _ _ next, refs, registry, revelations, outputs, store, history,
      replacement, defaults, nextDefaults, point, decoded
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, refs, registry, revelations, outputs, store,
      history, replacement, defaults, nextDefaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      obtain ⟨changed, changedRead, same⟩ := decodeSourcePrefix?_replace_history count next
        _ _ _ _ store history replacement defaults nextDefaults rest read
      exact ⟨.inr changed, congrArg (Option.map Sum.inr) changedRead, same⟩

/-- Debt at a decoded program position depends only on the masked store. Own-action
and public-default histories may differ, including defaults of unrelated players. -/
theorem owesFailure_of_decoded_playerStore_eq {graph : EventGraph Player L} (who : Player)
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (refs : ContextRefs graph.layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef graph.layout (outputLayout program event))
    (count : Nat) (left right : EventGraph.Store graph.layout)
    (leftHistory rightHistory : History Player L)
    (leftDefaults rightDefaults : DefaultHistory Player) (first last : ProtocolState program)
    (firstRead : decodeSourcePrefix? program refs registry revelations outputs count left
      leftHistory leftDefaults = some first)
    (lastRead : decodeSourcePrefix? program refs registry revelations outputs count right
      rightHistory rightDefaults = some last)
    (same : graph.playerStore who left = graph.playerStore who right)
    (owed : ProtocolState.OwesFailure who program first) :
    ProtocolState.OwesFailure who program last := by
  obtain ⟨changed, changedRead, cells⟩ := decodeSourcePrefix?_replace_history count program refs
    registry revelations outputs left leftHistory rightHistory leftDefaults rightDefaults first
    firstRead
  have firstStatic := decodeSourcePrefix?_staticAt count program refs registry revelations outputs
    left leftHistory leftDefaults first firstRead
  have changedStatic := decodeSourcePrefix?_staticAt count program refs registry revelations
    outputs left rightHistory rightDefaults changed changedRead
  have lastStatic := decodeSourcePrefix?_staticAt count program refs registry revelations outputs
    right rightHistory rightDefaults last lastRead
  have changedOwed := (ProtocolState.owesFailure_iff_of_sameCells who program registry revelations
    first changed firstStatic changedStatic cells).mp owed
  have leftView := decodeViewPrefix?_eq_observe who count program refs registry revelations outputs
    left rightHistory rightDefaults changed changedRead
  have rightView := decodeViewPrefix?_eq_observe who count program refs registry revelations outputs
    right rightHistory rightDefaults last lastRead
  have viewEq : ProtocolState.observe who program changed =
      ProtocolState.observe who program last := by
    apply Option.some.inj
    rw [← leftView, ← rightView,
      ← decodeViewPrefix?_playerStore who count program refs outputs left,
      ← decodeViewPrefix?_playerStore who count program refs outputs right, same]
  exact (ProtocolState.owesFailure_iff_of_observe_eq who program registry revelations changed last
    changedStatic lastStatic viewEq).mp changedOwed


/-- Source debt in a private prefix is irrevocable on every actual terminal path
with matching own binding records. Foreign private values, omissions and scheduling
may differ from the source prefix. -/
theorem SourceResidual.failedReveals_of_matching_binding_records
    {setup : Setup (Player := Player) (L := L)}
    (deps : setup.dataflowGraph.Dependencies)
    (serial : (setup.dataflowGraph.withDependencies deps).ActorSerial)
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {sourceGhost : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank sourceGhost)
    (initial : State L setup.context) (focal : Player)
    (origin ghost final : (setup.dataflowGraph.withDependencies deps).Config) (start : Nat)
    (originReach : EventGraph.Config.Reachable (graph := setup.dataflowGraph.withDependencies deps)
      (setup.eventInputs initial) origin)
    (before : origin.cut.IsPrefix start)
    (ghostPath : Relation.ReflTransGen EventGraph.Config.Step origin ghost)
    (ghostKey : runKey ghost = runKey
      ((setup.dataflowGraph.withDependencies deps).fromSequentialConfig sourceGhost))
    (finalPath : Relation.ReflTransGen EventGraph.Config.Step origin final)
    (terminal : final.cut.Terminal)
    (bindings : ∀ event : (setup.dataflowGraph.withDependencies deps).EventId,
      start ≤ event.val → event.val < rank →
      ∃ owner payload, (setup.dataflowGraph.withDependencies deps).outputLayout event =
        .binding owner payload)
    (records : ∀ event : (setup.dataflowGraph.withDependencies deps).EventId,
      start ≤ event.val → event.val < rank →
      (setup.dataflowGraph.withDependencies deps).actor? event = some focal →
      completionOf ghost event = completionOf final event)
    (owed : ProtocolState.OwesFailure focal setup.program
      (residual.lift (ProtocolState.entry residual.program residual.source))) :
    1 ≤ failedReveals setup.program focal
      (publicOutcome setup.program (terminalConfig setup.program
        ⟨rankedConfig (graph := setup.dataflowGraph.withDependencies deps) final terminal,
          rankedConfig_terminal (graph := setup.dataflowGraph.withDependencies deps)
            final terminal⟩)) := by
  let G := setup.dataflowGraph.withDependencies deps
  let orderedFinal : setup.informationGraph.Config := rankedConfig (graph := G) final terminal
  have finalReach := Config.Step.path_reachable finalPath originReach
  have orderedReach : EventGraph.Config.Reachable (graph := setup.informationGraph)
      (setup.eventInputs initial) orderedFinal :=
    serial.rankedConfig_reachable _ final finalReach terminal
  have initialPath : Relation.ReflTransGen EventGraph.Config.Step
      (Config.initial (graph := setup.informationGraph) (setup.eventInputs initial))
      orderedFinal := by
    have all (state : setup.informationGraph.Config)
        (reachable : EventGraph.Config.Reachable (graph := setup.informationGraph)
          (setup.eventInputs initial) state) :
        Relation.ReflTransGen EventGraph.Config.Step
          (Config.initial (graph := setup.informationGraph) (setup.eventInputs initial)) state := by
      induction reachable with
      | initial => exact .refl
      | step previous event ready action next member ih =>
          exact ih.tail ⟨event, ready, action, member⟩
    exact all orderedFinal orderedReach
  have orderedTerminal : orderedFinal.cut.IsPrefix (eventCount setup.program) := by
    refine ⟨le_rfl, ?_⟩
    intro event
    exact iff_of_true (Finset.mem_univ _) event.isLt
  obtain ⟨replay, replayOrdered, prefixPath, suffixPath⟩ :=
    Config.Step.path_prefix_at (graph := G) initialPath (EventOrder.Cut.empty_isPrefix _)
      orderedTerminal (Nat.zero_le rank) residual.checkpoint.ordered.1
  have restrictedInfo := Config.restrictionOf_path replayOrdered suffixPath
  let replayNative := G.fromSequentialConfig replay
  have restricted : replayNative.RestrictionOf (fun event => event.val < rank) final := by
    constructor
    · intro event
      have record := restrictedInfo.records event
      rw [completionOf_rankedConfig] at record
      exact record
    · intro field
      have store := restrictedInfo.store field
      cases field <;> exact store
  have ghostOrdered : ghost.cut.IsPrefix rank := by
    refine ⟨residual.checkpoint.ordered.1, ?_⟩
    intro event
    have same := congrArg (fun key => event ∈ key.1.completed) ghostKey
    exact same ▸ residual.checkpoint.ordered.2 event
  have masked := playerStore_eq_of_binding_replay_prefix focal origin ghost final replayNative
    start rank originReach before ghostOrdered ghostPath finalPath restricted bindings records
  have ghostStore : ghost.store = sourceGhost.store := by
    funext field
    have same := congrArg (fun key => key.2.1 field) ghostKey
    cases field <;> exact same
  have replayStore : replayNative.store = replay.store := by
    funext field
    cases field <;> rfl
  have maskedSource : setup.informationGraph.playerStore focal sourceGhost.store =
      setup.informationGraph.playerStore focal replay.store := by
    rw [ghostStore, replayStore] at masked
    exact masked
  obtain ⟨nextRank, ⟨nextResidual⟩⟩ :=
    (SourceResidual.initial setup profile initial).path prefixPath
  have sameRank : nextRank = rank := nextResidual.checkpoint.ordered.unique replayOrdered
  subst nextRank
  have replayOwed := owesFailure_of_decoded_playerStore_eq (graph := setup.informationGraph)
    focal setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) rank
    sourceGhost.store replay.store
    (decodeHistory setup.program sourceGhost.history) (decodeHistory setup.program replay.history)
    sourceGhost.defaults replay.defaults _ _ residual.decode nextResidual.decode maskedSource owed
  exact nextResidual.failedReveals_of_owesFailure_path suffixPath
    (rankedConfig_terminal (graph := G) final terminal) focal _ nextResidual.decode replayOwed

end

end Vegas

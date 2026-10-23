/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Game.CompiledCommitPartialView
import Vegas.Compile.CommitPrefixView
import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.PhaseFrontier

/-! # Genuine source recovery histories at partially completed commitment prefixes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A genuinely ready native event has a unique address in the saved source
suffix. Completed earlier ranks cannot be offered again. -/
theorem RecoverySourceCheckpoint.native_event_index
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (frontier : state.Frontier)
    (event : (serviceGraph setup mode).EventId)
    (ready : state.current.native.config.cut.Ready event) :
    ∃ index : Fin (eventCount checkpoint.residual.tail),
      checkpoint.embedding.event index = event := by
  have lower : state.attempt.phase ≤ event.val := by
    have positioned := frontier.positioned
    cases installed : state.phases with
    | nil =>
        rw [installed] at positioned
        exact (ready.1 ((positioned.2 event).mpr event.isLt)).elim
    | cons phase remaining =>
        rw [installed] at positioned
        have notEarlier : ¬ event.val < phase.low := fun below =>
          ready.1 (positioned.2.1 event below)
        simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some] using Nat.le_of_not_gt notEarlier
  have total := checkpoint.compiled.countEq
  let index : Fin (eventCount checkpoint.residual.tail) :=
    ⟨event.val - state.attempt.phase, by
      change state.attempt.phase + eventCount checkpoint.residual.tail =
        (serviceGraph setup mode).order.eventCount at total
      have bounded := event.isLt
      omega⟩
  refine ⟨index, Fin.ext ?_⟩
  rw [checkpoint.compiled.rankEq]
  dsimp only [index]
  omega

/-- The actual filled predecessor decodes to its full focal source observation.
Only the focal own word is identified; hidden foreign cells remain unchanged. -/
theorem RecoverySourceCheckpoint.filled_prefix_view
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (stored : state.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (past : List (OwnAction Player L))
    (historyAligned :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
        state.current.native.config.store checkpoint.source).history owner = past) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier (.commit name owner fresh guard next)
      embedding state.current.native.config.store checkpoint.source
    decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref owner (checkpoint.embedding.event selected)
      ((serviceGraph setup mode).playerStore owner state.current.native.config.store) past =
        some (ProtocolState.observe owner setup.program (checkpoint.residual.lift
          (cast (congrArg (fun program => ProtocolState program) reconstruct)
            (earlier.liftPoint (.commit name owner fresh guard next)
              (ProtocolState.entry (.commit name owner fresh guard next) filled))))) := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, _origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at entry
  change ContextRefs (graphLayout setup.program) Γ at refs
  change Registry Γ at registry
  change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
    at embedding
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change Fin (eventCount program) at selected
  change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
  subst program
  let suffix : SourceProgram Player L Δ P := .commit name owner fresh guard next
  let filled := fillCommitPrefix setup.program earlier suffix embedding
    state.current.native.config.store entry
  have currentAgreement : refs.Agrees entry.state state.current.native.config.store := by
    intro selectedName selectedCell selected
    apply (refs.get selected).get?_preserved state.entry.native.config.store
      state.current.native.config.store stored
    exact agrees selected
  have decoded : decodeObservation? owner refs state.current.native.config.store =
      some (sourceObserve owner entry.state) :=
    decodeObservation?_eq_some refs owner entry.state state.current.native.config.store
      currentAgreement
  have filledObservation := fillCommitPrefix_observation_of_ready setup mode earlier suffix
    embedding refs state.current.native.config entry owner decoded selected atEnd ready acting
      notPublication
  have visibleDecode : decodeObservation? owner
      (commitBlockRefs setup.program earlier suffix embedding refs)
      ((toEventGraph setup.program).playerStore owner state.current.native.config.store) =
        some (sourceObserve owner filled.state) := by
    exact (decodeObservation?_playerStore (graph := toEventGraph setup.program) owner
      (commitBlockRefs setup.program earlier suffix embedding refs)
        state.current.native.config.store).trans filledObservation
  have localView := decodeEventView?_commitPrefix_entry setup.program earlier suffix embedding
    refs ((toEventGraph setup.program).playerStore owner state.current.native.config.store) filled
    owner selected atEnd visibleDecode
  have wholeView := (views.decode owner selected
    ((toEventGraph setup.program).playerStore owner state.current.native.config.store)
      (filled.history owner)).trans
    ((congrArg (Option.map (views.view owner)) localView).trans
      (congrArg some (views.observe owner
        (earlier.liftPoint suffix (ProtocolState.entry suffix filled)))).symm)
  change filled.history owner = past at historyAligned
  rw [← historyAligned]
  exact wholeView

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinaryStoppedSourceWord
import Vegas.Game.PhaseProposalBindingEntry
import Vegas.Game.CompiledCommitMaximality

/-! # The chronological ordinary cursor at an actual fresh binding installation -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual fresh installation and its selected checkpoint supply the
whole finite source cursor. Its enriched trace is the literal archive lift
of that checkpoint's original initialized trace. The ordinary hypothesis is
only usability of surviving source values; private guards remain arbitrary. -/
theorem RecoverySourceWitness.ordinary_installed_binding_cursor
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (ordinary : ∀ who, who ∉ anchor.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues who) :
    ∃ (Δ : SourceCtx Player L) (P : Finset VarId)
      (block : SourceProgram.CommitPrefix witness.checkpoint.residual.context
        witness.checkpoint.residual.names Δ P)
      (suffix : SourceProgram Player L Δ P)
      (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
        block suffix),
      block.length = phase.high - phase.low ∧
      cursor.source = witness.checkpoint.source ∧
      cursor.config = anchor.execution.application.current.native.config ∧
      (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
          witness.checkpoint.trace⟩ ∧
      cursor.refs = witness.checkpoint.refs ∧
      ∃ reconstruct : block.prepend suffix = witness.checkpoint.residual.tail,
        cursor.embedding = cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            witness.checkpoint.embedding ∧
        ∀ point, cursor.lift point = witness.checkpoint.residual.lift
          (cast (congrArg ProtocolState reconstruct) point) := by
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let app := phaseApplication runtime leaks
  let graph := serviceGraph setup mode
  have raw := menu.toRawTrace initial horizon scheduler anchorTrace
  obtain ⟨noInputs, _emissions, origins⟩ := phaseProposal_fresh_entry_binding_origins setup mode
    runtime leaks bounds plan inputs horizon scheduler anchor anchorTrace phase installed
      commitment fresh
  have noAccepted : ∀ event : graph.EventId,
      anchor.execution.application.attempt.phase ≤ event.val →
        anchor.execution.application.current.native.accepted (.inr event) = none := by
    intro event after
    by_contra present
    obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
    have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
    rcases stamped event candidate accepted with past |
      ⟨message, authored, _sender, _named, attempted⟩
    · omega
    · have member : message ∈ anchor.execution.network.inputs := by
        change message ∈ app.outputs (anchor.execution.recall candidate.1) at authored
        rw [← app.history_inputRecall initial horizon scheduler raw candidate.1] at authored
        exact (List.mem_filter.mp authored).1
      exact noInputs message member attempted
  cases phases : anchor.execution.application.phases with
  | nil => simp only [phases, List.head?_nil, reduceCtorEq] at installed
  | cons first rest =>
    have samePhase : first = phase := by
      simpa only [phases, List.head?_cons, Option.some.injEq] using installed
    subst first
    have low : anchor.execution.application.attempt.phase = phase.low := by
      simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some]
    have committing := witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
      witness.checkpoint.residual.tail witness.checkpoint.refs witness.checkpoint.source.revelations
      witness.checkpoint.registry witness.checkpoint.embedding witness.checkpoint.before
      anchor.execution.application.attempt.phase phase commitment low.symm witness.checkpoint.source
    have savedControl := PhaseRuntimeState.saved_excluded_eq_public_failures witness.exclusions
      witness.failures witness.receipts.exclusion.frontier phase rest phases
    have inherited :
        (anchor.execution.application.publicView.retired.map fun record =>
          record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ =
          PhaseRuntimeState.archivedFailureOwners anchor.execution.application.retired := by
      have retained := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
        anchor.execution.application.retired
      simpa only [RuntimePhasePlan.sourceRecordFailures, PhaseRuntimeState.sourceControlRecords,
        PhaseRuntimeState.publicView, List.map_map, Function.comp_def,
        State.sourceFailureFootprint_read, State.sourceFailureFootprint] using retained
    have position := witness.checkpoint.saved_position
    rcases witness with ⟨checkpoint, aligned, chronology, sourceOrigins, native, binding, receipts,
      stored, remembered, order, suffixMember, archives, exclusions, failures⟩
    dsimp only at ordinary archived committing position ⊢
    let priorTrace := checkpoint.trace
    have addresses := chronology.addresses
    rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
      compiled, terminalAlignment, agrees, guards, preserves, unique, remaining, actor, atCommit,
      owners, commitEnd, automatic, history, withHistory, step, menus, readout, sourceTrace, views,
      historyAlignment, origin⟩
    dsimp only at ordinary archived committing position addresses ⊢
    generalize decomposition : commitPhase program = segment at ⊢
    rcases segment with ⟨Δ, P, tail, block, reconstruct, boundary⟩
    subst program
    have positive : 0 < block.length := by
      cases block with
      | nil =>
          cases tail with
          | ret => cases committing
          | sample => cases committing
          | reveal => cases committing
          | commit => cases boundary
      | commit => simp only [SourceProgram.CommitPrefix.length]; omega
    have adjacent := receipts.exclusion.frontier.adjacent
    have ending := receipts.exclusion.frontier.last
    have chain := maximal.suffix suffixMember
    rw [phases] at adjacent ending chain
    have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block tail embedding
      compiled positive boundary phase rest adjacent ending chain low.symm
    have positioned := receipts.exclusion.frontier.positioned
    rw [phases] at positioned
    have blockSize : block.length = phase.high - phase.low := by
      rw [phaseEq]
      simp only [compiledCommitPhase]
      omega
    let current := CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend tail) source))
      anchor.execution.application.entry.excluded anchor.execution.application.generation
    let trace := setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
      sourceTrace
    have agreement : refs.Agrees source.state
        anchor.execution.application.current.native.config.store := by
      intro readName cell selected
      exact (refs.get selected).get?_preserved _ _ stored _ (agrees selected)
    have ahead : ExcludedCommitFieldsAhead setup mode current.excluded
        anchor.execution.application.attempt.phase block.length
        anchor.execution.application.current.native.config := by
      intro event completed after
      have bounded := positioned.2.2 event completed
      have inside : event ∈ phase.events := (phase.mem_events event).mpr ⟨by omega, bounded⟩
      obtain ⟨owner, payload, typed⟩ := commitment ▸ phase.fields event
        ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
      have inherited : owner ∈ anchor.execution.application.current.excluded := by
        rcases origins event completed with earlier | ⟨actor, excluded, acted⟩
        · omega
        · have same := (actor?_of_outputLayout_binding graph typed).symm.trans acted
          exact (Option.some.inj same).symm ▸ excluded
      refine ⟨by rw [phaseEq] at bounded; exact bounded, owner, payload, typed, ?_, ?_⟩
      · simpa only [current, CommitRecoveryState.atPoint, entryExcluded] using inherited
      · let field : FieldRef (graphLayout setup.program) (.binding owner payload) :=
          ⟨.inr event, typed⟩
        have read := binding.active.binding_read field event rfl completed
        rw [noAccepted event after] at read
        exact read
    let cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
        block tail :=
      { source := source
        offset := anchor.execution.application.attempt.phase
        current := current
        trace := trace
        refs := refs
        revelations := source.revelations
        registry := registry
        embedding := embedding
        before := before
        compiled := compiled
        lift := lift
        origin := origin
        views := views
        config := anchor.execution.application.current.native.config
        point := rfl
        agrees := agreement
        excluded := entryExcluded
        entryExcluded := entryExcluded
        savedCommit := fun _ => (atCommit _).trans committing
        savedEnd := fun _ => (commitEnd _).trans
          (block.commitEnd_entry_prepend tail boundary source)
        live := fun who surviving => ordinary who (entryExcluded ▸ surviving)
        smaller := by rw [low]; exact positioned.2.1
        ahead := ahead
        interval := by
          intro index inside
          rw [phaseEq]
          exact (compiledCommitPhase_mem_iff setup.program mode block tail embedding compiled
            positive _).mpr ⟨index, inside, rfl⟩
        low := Nat.le_refl _
        controls := by
          intro _
          change (anchor.execution.application.entry.excluded,
            anchor.execution.application.generation, instructionCount setup.program -
              ProtocolState.remaining setup.program
                (lift (ProtocolState.entry (block.prepend tail) source))) = _
          rw [position, inherited]
          simp only [State.sourceFailureFootprint_read, State.sourceFailureFootprint]
          rw [savedControl]
          rfl
        addresses := by
          intro _ who
          rw [setup.proposalRecoveryEraseTrace_lift,
            setup.commitRecovery_publicRecall_addresses, addresses,
            PhaseRuntimeState.sourcePublicAddressWord_read]
        proposals := by
          intro who surviving
          exact RecoverySourceCheckpoint.ArchivedProposals.binding runtime leaks bounds plan inputs
            horizon scheduler anchor anchorTrace _ archived phase installed commitment who
              (entryExcluded ▸ surviving) }
    exact ⟨Δ, P, block, tail, cursor, blockSize, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end Vegas

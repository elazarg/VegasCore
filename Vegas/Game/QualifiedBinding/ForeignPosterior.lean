/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.QualifiedBinding.OrdinaryContinuation
import Vegas.Game.AsyncDeviationForeign
import Vegas.Game.PhaseBindingRecallMeaning
import GameTheoryExtensions.Math.Probability.RestrictedDisintegration

/-! # Issued-word source posterior disintegration -/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))

open scoped ENNReal

attribute [local implicit_reducible] InformationModel.InformationSite

section ForeignPosterior

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler

theorem transport_indexed
    {α : Type} {β : α → Type} (predicate : (a : α) → β a → Prop)
    {a b : α} (same : a = b) (value : β b) (proof : predicate b value) :
    predicate a (same.symm ▸ value) := by
  cases same
  exact proof

private theorem transport_two_indexed
    {α : Type} {β γ : α → Type}
    (relation : (a : α) → β a → γ a → Prop)
    {a b : α} (same : a = b) (first : β b) (second : γ b)
    (proof : relation b first second) :
    relation a (same.symm ▸ first) (same.symm ▸ second) := by
  cases same
  exact proof

private theorem cast_roundtrip {α : Type} {β : α → Type}
    {a b : α} (same : a = b) (value : β b) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

def issuedBindingObservation
    (control : (nativeApplication).Control)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (key : (serviceGraph setup .concurrent).SemanticKey) : Bool := by
  classical
  exact decide (∀ message ∈ control.execution.network.inputs,
    message.payload.attempt = control.execution.application.attempt →
    ∀ event ∈ phase.events, ∀ candidate,
      message.payload.packet.call = .commitment event candidate →
      ∀ owner payload (binding :
          (serviceGraph setup .concurrent).outputLayout event = .binding owner payload),
        (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
          (.binding owner payload)).get? key.2.1 =
            some (control.execution.application.current.native.bindingResult candidate payload))

/-- Every proper selected value has a positive issued-ledger cylinder at
the original frozen graph entry. Its conditional law is the completed emitted
frontier, independently of the historical probability of that response. -/
theorem binding_value_frontier_posterior
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (unsentBinding : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (value : L.Val payload) :
    let profile := phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
      implementation.leaks implementation.plan entry.entry.execution entry.phase values
    let original := (serviceGraph setup .concurrent).canonicalContinuation profile
      entry.entry.execution.application.current.native.config
    let observed := fun key => issuedBindingObservation setup implementation control entry.phase
      key &&
      decide ((⟨.inr event, unsentBinding.binding⟩ :
        FieldRef (serviceGraph setup .concurrent).layout
        (.binding who payload)).get? key.2.1 = some (.success value))
    let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
        entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
          implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler trace)
    ∃ ready : frontier.cut.Ready event,
      true ∈ (original.map observed).support ∧
        (serviceGraph setup .concurrent).canonicalContinuation profile
          (phaseProposalBindingFrontierDrain setup .concurrent implementation.runtime
            implementation.leaks entry.entry.execution entry.phase
              (frontier.complete event ready
                (cast (congrArg EventField.Action unsentBinding.binding.symm) (.success value))
                (cast (congrArg EventField.Value unsentBinding.binding.symm) (.success value)))) =
          fiberPosterior original observed true ∧
      (original.map observed) true =
        (original.map (issuedBindingObservation setup implementation control entry.phase)) true *
          phaseProposalBindingResults setup .concurrent implementation.runtime implementation.leaks
            implementation.plan values PhaseProposalRates.zero who event payload
              unsentBinding.binding (control.execution.recall who)
                (control.execution.observe nativeApplication who) (.success value) := by
  classical
  intro profile original observed frontier
  let derivedInitial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : derivedInitial = nativeInitial := PMF.map_comp _ _ _
  let counted : ((nativeMenu).protocol derivedInitial implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  let earlier : ((nativeMenu).protocol derivedInitial implementation.horizon
      implementation.scheduler).Trace (some entry.entry) := initialEq.symm ▸ entry.entryTrace
  have frame := entry.callback_frame setup implementation operational control trace who event
  have proper := entry.frontier_proper setup implementation operational control trace who
    event payload unsentBinding foreign
  have retainedCast : TracePrefix earlier counted :=
    transport_two_indexed
      (fun law
        (before : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some entry.entry))
        (after : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some control)) => TracePrefix before after)
      initialEq entry.entryTrace trace entry.retained
  have properCast : ∀ named ∈ entry.phase.events,
      ∀ owner ∉ entry.entry.execution.application.current.excluded,
        ∀ (domain : L.Ty)
          (binding : (serviceGraph setup .concurrent).outputLayout named =
            .binding owner domain) result,
          (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
            (.binding owner domain)).get? (phaseProposalEmissionFrontier setup .concurrent
              implementation.runtime implementation.leaks entry.entry.execution entry.phase
              earlier.length entry.entry.execution.application.current.native.config
              derivedInitial implementation.horizon implementation.scheduler
              ((nativeMenu).toRawTrace derivedInitial implementation.horizon
                implementation.scheduler counted)).store = some result →
            ∃ value, result = .success value :=
    transport_two_indexed
      (fun law
        (before : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some entry.entry))
        (after : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some control)) =>
        ∀ named ∈ entry.phase.events,
          ∀ owner ∉ entry.entry.execution.application.current.excluded,
            ∀ (domain : L.Ty)
              (binding : (serviceGraph setup .concurrent).outputLayout named =
                .binding owner domain) result,
              (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
                (.binding owner domain)).get? (phaseProposalEmissionFrontier setup .concurrent
                  implementation.runtime implementation.leaks entry.entry.execution entry.phase
                  before.length entry.entry.execution.application.current.native.config
                  law implementation.horizon implementation.scheduler
                  ((nativeMenu).toRawTrace law implementation.horizon
                    implementation.scheduler after)).store = some result →
                ∃ value, result = .success value)
      initialEq entry.entryTrace trace proper
  obtain ⟨oldPresent, oldLaw⟩ := emitted_frontier_conditional setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan values
      operational.completePending operational.maximalPhases fullValues implementation.horizon
      implementation.scheduler entry.entry earlier entry.phase entry.entryInstalled entry.commitment
      entry.entryExcluded entry.fresh control counted retainedCast
      entry.sameAttempt.symm entry.excluded properCast
  have frontierEq : frontier = phaseProposalEmissionFrontier setup .concurrent
      implementation.runtime implementation.leaks entry.entry.execution entry.phase
      entry.entryTrace.length entry.entry.execution.application.current.native.config
      nativeInitial implementation.horizon implementation.scheduler
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace) := by
    simp only [frontier]
  have request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩ := by
    obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history implementation.runtime
      implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler
          ((nativeMenu).toRawTrace derivedInitial implementation.horizon
            implementation.scheduler counted)
    exact (control.execution.application.requests_publicView invariant who _).mp
      unsentBinding.request
  have code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout)
      unsentBinding.binding) ((serviceGraph setup .concurrent).nodes event) =
        .bind who payload := by
    cases nodeView (serviceGraph setup .concurrent) event with
    | bind owner domain shape code =>
        obtain ⟨rfl, rfl⟩ := EventField.binding.inj (shape.symm.trans unsentBinding.binding)
        exact code
    | resolve owner domain source checks shape code => cases shape.symm.trans unsentBinding.binding
    | sample domain law shape code => cases shape.symm.trans unsentBinding.binding
  have nativeActive : who ∉ entry.entry.execution.application.current.excluded := by
    rw [← entry.excluded]
    exact request.2.2.2.2
  have unsent : ∀ message ∈ (nativeApplication).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩ := by
    have attemptEq : (control.execution.observe nativeApplication who).application.2.attempt =
        control.execution.application.attempt := rfl
    simpa only [attemptEq] using unsentBinding.unsent
  have traceActive : ((nativeMenu).protocol nativeInitial implementation.horizon
      implementation.scheduler).Trace
        (some ⟨control.remaining, some who, control.execution⟩) := by
    simpa only [← active] using trace
  have frameActive : PhaseProposalBindingCallbackFrame setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase control.execution frontier
        (some who) := by
    simpa only [frontier, active] using frame
  obtain ⟨ready, rowPresent, rowLaw, rowAtom⟩ := binding_frontier_proper_posterior setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan values
      operational.completePending operational.maximalPhases fullValues implementation.horizon
      implementation.scheduler control.remaining who control.execution entry.entry.execution
      traceActive entry.phase entry.commitment frontier frameActive entry.sameAttempt.symm
      event payload unsentBinding.binding code entry.inside nativeActive request unsent value
  have beforeEq :
      (serviceGraph setup .concurrent).canonicalContinuation profile frontier =
        fiberPosterior original
          (issuedBindingObservation setup implementation control entry.phase) true := by
      have transported := transport_two_indexed
        (fun law
          (before : ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some entry.entry))
          (after : ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some control)) =>
          (serviceGraph setup .concurrent).canonicalContinuation profile
            (phaseProposalEmissionFrontier setup .concurrent implementation.runtime
              implementation.leaks entry.entry.execution entry.phase before.length
              entry.entry.execution.application.current.native.config law
              implementation.horizon implementation.scheduler
              ((nativeMenu).toRawTrace law implementation.horizon
                implementation.scheduler after)) =
            fiberPosterior original
              (issuedBindingObservation setup implementation control entry.phase) true)
        initialEq.symm earlier counted
        (by
          unfold issuedBindingObservation
          simpa [profile, original, entry.phase.mem_events, Prod.forall,
            derivedInitial] using oldLaw)
      have earlierBack : initialEq ▸ earlier = entry.entryTrace := by
        simpa only [earlier] using cast_roundtrip
          (β := fun law => ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some entry.entry)) initialEq entry.entryTrace
      have countedBack : initialEq ▸ counted = trace := by
        simpa only [counted] using cast_roundtrip
          (β := fun law => ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some control)) initialEq trace
      simpa only [earlierBack, countedBack, profile, original, frontier]
        using transported
  have oldSupported : true ∈ (original.map
      (issuedBindingObservation setup implementation control entry.phase)).support := by
    simpa [original, profile, issuedBindingObservation] using oldPresent
  let field : FieldRef (serviceGraph setup .concurrent).layout (.binding who payload) :=
    ⟨.inr event, unsentBinding.binding⟩
  have same : ∀ key ∈ original.support, observed key = true ↔
      issuedBindingObservation setup implementation control entry.phase key = true ∧
        field.get? key.2.1 = some (.success value) := by
    intro key _
    simp only [observed, Bool.and_eq_true, decide_eq_true_eq, field]
  have appended := posterior_append_observation original
    (issuedBindingObservation setup implementation control entry.phase) observed
    (fun key => field.get? key.2.1) (some (.success value))
    ((serviceGraph setup .concurrent).canonicalContinuation profile frontier)
    _ oldSupported beforeEq rowPresent rowLaw.symm same
  refine ⟨ready, appended.1, appended.2, ?_⟩
  have mass := observation_fiber_mass original
    (issuedBindingObservation setup implementation control entry.phase) observed
    (fun key => field.get? key.2.1) (some (.success value)) same
  rw [← beforeEq, rowAtom] at mass
  exact mass

/-- The maximal ordinary cursor at the callback uses the literal selected
checkpoint's block, maps and views. Its graph configuration remains the
original frozen entry configuration. -/
theorem selected_binding_cursor
    (operational : implementation.Operational)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (atCallback : Bool) :
    let anchor := if atCallback then control else entry.entry
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    ∃ cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan anchor entry.phase block.block block.suffix,
      (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
        canonicalSource setup implementation operational ⟨some control, trace⟩ ∧
      cursor.offset = control.execution.application.attempt.phase ∧
      cursor.source = checkpoint.source ∧ cursor.refs = checkpoint.refs ∧
      cursor.embedding = cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          block.reconstruct.symm) checkpoint.embedding ∧
      (∀ point, cursor.lift point = checkpoint.residual.lift
        (cast (congrArg ProtocolState block.reconstruct) point)) ∧
      (∀ owner view, cursor.views.view owner view = checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) ∧
      cursor.config = entry.cursor.config ∧
      block.block.length = entry.phase.high - entry.phase.low := by
  classical
  intro anchor checkpoint block
  let cursorFor := fun checkpoint : RecoverySourceCheckpoint setup .concurrent
      entry.entry.execution.application =>
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    ∃ cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan anchor entry.phase block.block block.suffix,
      (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
        canonicalSource setup implementation operational ⟨some control, trace⟩ ∧
      cursor.offset = control.execution.application.attempt.phase ∧
      cursor.source = checkpoint.source ∧ cursor.refs = checkpoint.refs ∧
      cursor.embedding = cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          block.reconstruct.symm) checkpoint.embedding ∧
      (∀ point, cursor.lift point = checkpoint.residual.lift
        (cast (congrArg ProtocolState block.reconstruct) point)) ∧
      (∀ owner view, cursor.views.view owner view = checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) ∧
      cursor.config = entry.cursor.config ∧
      block.block.length = entry.phase.high - entry.phase.low
  have prior : cursorFor entry.witness.checkpoint := by
    have maximum (program : SourceProgram Player L entry.witness.checkpoint.residual.context
        entry.witness.checkpoint.residual.names)
        (reconstruct : entry.block.prepend entry.suffix = program) :
        SourceProgram.commitPhase program =
          ⟨entry.targetContext, entry.targetNames, entry.suffix, entry.block,
            reconstruct, entry.boundary⟩ := by
      cases reconstruct
      exact maximal_commit_phase entry.block entry.suffix entry.boundary
    dsimp only [cursorFor]
    rw [maximum entry.witness.checkpoint.residual.tail entry.reconstruct]
    have low : control.execution.application.attempt.phase = entry.phase.low := by
      obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
      simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some]
    cases atCallback with
    | false =>
        exact ⟨entry.cursor, entry.canonicalHistory, entry.offset.trans low.symm, entry.source,
          entry.refs, entry.embedding, entry.lift, entry.views, rfl, entry.size⟩
    | true =>
        exact ⟨entry.decision_cursor setup implementation operational control trace who
          event,
          entry.canonicalHistory, entry.offset.trans low.symm, entry.source, entry.refs,
          entry.embedding, entry.lift, entry.views, rfl, entry.size⟩
  obtain ⟨saved, represented⟩ := entry.selected
  have transported : cursorFor (checkpoint.transfer saved
      (congrArg CommitAttemptId.generation entry.sameAttempt)
      (congrArg CommitAttemptId.phase entry.sameAttempt)) := represented ▸ prior
  exact transported

/-- Every history with the selected entry's closed key retains its complete
erased source history. Its ordinary cursor uses the same physical anchor and
compiler references; only hidden publication memories can change. -/
theorem closed_key_entry_erased_history
    (operational : implementation.Operational)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (target : setup.proposalRecoveryProtocol.History)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩)
    (sameKey : setup.proposalRecoveryClosedKey who target =
      setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational ⟨some control, trace⟩)) :
    ∃ (current : CommitRecoveryState setup.program)
        (targetTrace : setup.proposalRecoveryProtocol.Trace (some current)),
        target = ⟨some current, targetTrace⟩ ∧
        setup.proposalRecoveryForeignGood who target ∧
        setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
          setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩ := by
  classical
  have canonicalGood := canonicalSource_foreignGood setup implementation operational who
    ⟨some control, trace⟩ foreign
  have same : setup.proposalRecoveryClosedKey who target =
      setup.proposalRecoveryClosedKey who ⟨some entry.cursor.current, entry.cursor.trace⟩ :=
    sameKey.trans (congrArg (setup.proposalRecoveryClosedKey who) entry.canonicalHistory.symm)
  have entryGood : setup.proposalRecoveryForeignGood who
      ⟨some entry.cursor.current, entry.cursor.trace⟩ :=
    entry.canonicalHistory.symm ▸ canonicalGood
  have targetGood : setup.proposalRecoveryForeignGood who target := by
    have bit := congrArg (fun key => key.2.2.2) same
    simpa only [Setup.proposalRecoveryClosedKey, entryGood, decide_true,
      decide_eq_true_eq] using bit
  rcases target with ⟨state, targetTrace⟩
  cases state with
  | none =>
      have base := congrArg Prod.fst same
      simp only [Setup.proposalRecoveryClosedKey, Option.map_none, Option.map_some] at base
      cases base
  | some current =>
      obtain ⟨first, prior, refines⟩ := setup.proposalRecovery_refinement_of_closed_key who
        operational.wellFormed entry.cursor.current current entry.cursor.trace targetTrace
          same.symm entryGood targetGood
      exact ⟨current, targetTrace, rfl, targetGood, refines.erasedHistory⟩

/-- A positive annotation supplies the same whole-history cursor transfer,
without an assumption on the historical policy outside its actual support. -/
theorem annotated_entry_erased_history
    (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (unsentBinding : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload) :
    ∃ entry : NativeBindingEntry setup implementation operational control trace who event,
      ∃ (current : CommitRecoveryState setup.program)
        (targetTrace : setup.proposalRecoveryProtocol.Trace (some current)),
        target = ⟨some current, targetTrace⟩ ∧
        setup.proposalRecoveryForeignGood who target ∧
        setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
          setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩ := by
  have foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at positive
    dsimp only at positive
    have selected := (mul_ne_zero_iff.mp positive).2
    split at selected
    · rename_i qualified
      exact qualified.1
    · simp only [ne_eq, not_true_eq_false] at selected
  have support := annotatedPrefixWeight_support setup values implementation operational
    sourceProfile nativeProfile who ⟨some control, trace⟩ tape target word canonicalSupported
      positive
  obtain ⟨entry⟩ := qualified_binding_entry setup implementation operational control
    trace who event payload unsentBinding foreign
  obtain ⟨current, targetTrace, targetEq, good, erased⟩ :=
    closed_key_entry_erased_history setup implementation operational who control trace
      event entry target foreign support.1
  exact ⟨entry, current, targetTrace, targetEq, good, erased⟩

open Classical in
/-- Conditioning the complete source/graph coupling on all literal issued
bindings and a proper selected value retains the whole chronological block
word on both marginals. Already excluded rows remain automatic source slots. -/
theorem ordinary_binding_conditioned_word_coupling
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (anchor : (nativeApplication).Control)
    (anchorTrace : (nativeProtocol).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase block suffix)
    (entryExcluded : cursor.current.excluded = control.execution.application.entry.excluded)
    (phaseLow : phase.low = cursor.offset)
    (phaseHigh : phase.high = cursor.offset + block.length)
    (who : Player) (active : who ∉ control.execution.application.entry.excluded)
    (index : Fin (eventCount (block.prepend suffix))) (inside : index.val < block.length)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout (cursor.embedding.event index) =
      .binding who payload) (value : L.Val payload) :
    let completed := fun history : setup.proposalRecoveryProtocol.History =>
      history.state.bind fun current => residualEntry? suffix
        (fun point => cursor.lift (block.liftPoint suffix point)) current.point
    let sourceObserved := fun history : setup.proposalRecoveryProtocol.History =>
      match completed history with
      | none => false
      | some finished => decide (
          (∀ owner, issuedLedger setup implementation block cursor.offset control
            (cursor.offset + block.length) owner (finished.view owner)) ∧
          block.wordAction who index.val (finished.view who) =
            decodeEventAction setup.program (cursor.embedding.event index)
              (cast (congrArg EventField.Action binding.symm) (PublicationResult.success value)))
    let graphObserved := fun key : (serviceGraph setup .concurrent).SemanticKey =>
      decide ((∀ message ∈ control.execution.network.inputs,
        message.payload.attempt = control.execution.application.attempt →
        ∀ event ∈ phase.events, ∀ candidate,
          message.payload.packet.call = .commitment event candidate →
          ∀ owner domain (shape : (serviceGraph setup .concurrent).outputLayout event =
              .binding owner domain),
            (⟨.inr event, shape⟩ : FieldRef (graphLayout setup.program)
              (.binding owner domain)).get? key.2.1 =
                some (control.execution.application.current.native.bindingResult candidate
                  domain)) ∧
        (⟨.inr (cursor.embedding.event index), binding⟩ :
          FieldRef (graphLayout setup.program) (.binding who payload)).get? key.2.1 =
            some (.success value))
    true ∈ (((serviceGraph setup .concurrent).canonicalContinuation
      (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
        implementation.leaks implementation.plan anchor.execution phase values)
      cursor.config).map graphObserved).support →
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
        (serviceGraph setup .concurrent).SemanticKey),
      joint.map Prod.fst = fiberPosterior
        (setup.proposalRecoveryModel.runBehavioralFrom
          (sourceUnflaggedStrategy setup values) block.length
            ⟨some cursor.current, cursor.trace⟩) sourceObserved true ∧
      joint.map Prod.snd = fiberPosterior
        ((serviceGraph setup .concurrent).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
            implementation.leaks implementation.plan anchor.execution phase values)
          cursor.config) graphObserved true ∧
      ∀ pair ∈ joint.support,
        PhaseProposalOrdinarySourceBlockResult setup .concurrent block suffix cursor.refs
          cursor.embedding cursor.lift cursor.source cursor.current cursor.trace pair ∧
        sourceObserved pair.1 = true ∧ graphObserved pair.2 = true ∧
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace pair.1.trace)).take
          block.length).reverse =
          phaseProposalBindingWord setup.program block suffix cursor.embedding
            cursor.current.excluded pair.2.2.1 cursor.source := by
    classical
  intro completed sourceObserved graphObserved present
  have observes (pair : setup.proposalRecoveryProtocol.History ×
      (serviceGraph setup .concurrent).SemanticKey)
      (related : PhaseProposalOrdinarySourceBlockResult setup .concurrent block suffix
        cursor.refs cursor.embedding cursor.lift cursor.source cursor.current cursor.trace pair) :
      sourceObserved pair.1 = graphObserved pair.2 := by
    obtain ⟨finished, last, lastTrace, attempt, history, point, excluded, _generation,
      _live, agreement, _word, _labels⟩ := related
    have pulled : residualEntry? suffix
        (fun point => cursor.lift (block.liftPoint suffix point)) last.point = some finished :=
      (residualEntry?_eq_some_iff (cursor.origin.compose (block.protocolSuffix suffix))
        last.point finished).mpr point.symm
    rw [entryExcluded] at attempt excluded
    have ledger := issuedLedger_iff_emitted_bindings setup implementation block suffix
      cursor.embedding cursor.refs cursor.offset cursor.compiled.rankEq cursor.views.actionEq
        control trace phase phaseLow phaseHigh pair.2.2.1 cursor.source finished last.excluded
          attempt excluded agreement
    have selected := commitAttempt_selected_binding setup block suffix cursor.embedding
      cursor.refs cursor.views.actionEq pair.2.2.1 cursor.source
        control.execution.application.entry.excluded finished last.excluded attempt excluded
          agreement who active index inside payload binding value
    simp only [sourceObserved, completed, history, Option.bind_some, pulled]
    exact decide_eq_decide.mpr (and_congr ledger selected)
  obtain ⟨joint, sourceMarginal, graphMarginal, supported⟩ :=
    phaseProposalBindingPotentialProfile_conditioned_source_block_coupling setup .concurrent
      implementation.runtime implementation.leaks implementation.plan values nativeInitial
        implementation.horizon implementation.scheduler anchor
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler anchorTrace) phase block suffix cursor sourceObserved
              graphObserved observes present
  refine ⟨joint, sourceMarginal, graphMarginal, ?_⟩
  intro pair member
  obtain ⟨related, sourceTrue, graphTrue⟩ := supported pair member
  refine ⟨related, sourceTrue, graphTrue, ?_⟩
  obtain ⟨finished, last, lastTrace, attempt, history, _point, excluded, _generation,
    _live, agreement, word, _labels⟩ := related
  have read := phaseProposalBindingWord_of_ordinary_attempt setup.program block suffix
    cursor.embedding cursor.refs pair.2.2.1 cursor.source cursor.source cursor.current.excluded
      finished last.excluded attempt excluded agreement
  rw [read, history, word]
  rw [← attempt.joints_length, ← List.length_reverse, List.take_left, List.reverse_reverse]

/-- The original source run and its structural owner words have one joint
law. The structural coordinate is the actual attempt with synthetic excluded
rows inserted; the source coordinate keeps its automatic NONE instructions. -/
theorem ordinary_source_structural_joint
    (anchor : (nativeApplication).Control)
    (anchorTrace : (nativeProtocol).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase block suffix) :
    let controls : Finset Player × Nat × Nat :=
      ((anchor.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
            anchor.execution.application.attempt.phase,
        anchor.execution.application.attempt.generation,
        anchor.execution.application.attempt.phase)
    let profile := ordinaryBlockProfile setup .concurrent implementation.plan values
      block suffix cursor.embedding (fun owner view => cursor.views.view owner view)
        controls anchor.execution.application.publicView
          (PhaseProposal.sourceArchive anchor.execution.network.inputs)
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History × SourceProgram.Config Player L Δ),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) block.length
          ⟨some cursor.current, cursor.trace⟩ ∧
      joint.map Prod.snd = block.prefixLaw suffix profile cursor.source ∧
      ∀ pair ∈ joint.support,
        ∃ (finished : SourceProgram.Config Player L Δ)
          (last : CommitRecoveryState setup.program)
          (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
          (attempt : block.Attempt cursor.source cursor.current.excluded finished last.excluded),
          pair.1 = ⟨some last, lastTrace⟩ ∧
          pair.2 = attempt.withoutMisses ∅ cursor.source ∧
          last.point = cursor.lift (block.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
          last.excluded = cursor.current.excluded ∧ last.generation = cursor.current.generation ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
            attempt.joints.reverse ++ setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace cursor.trace) ∧
          setup.proposalRecoveryJointRecall lastTrace =
            attempt.joints.reverse.map
              (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) ++
                setup.proposalRecoveryJointRecall cursor.trace ∧
          ∀ owner, owner ∉ last.excluded → finished.view owner = pair.2.view owner := by
  classical
  intro controls profile
  obtain ⟨coupling, sourceMarginal, graphMarginal, supported, fillMarginal⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup .concurrent
      implementation.runtime implementation.leaks implementation.plan nativeInitial
        implementation.horizon implementation.scheduler anchor
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler anchorTrace) phase values block suffix cursor
  let project := fun pair : setup.proposalRecoveryProtocol.History ×
      (serviceGraph setup .concurrent).SemanticKey =>
    (pair.1, fillCommitPrefix setup.program block suffix cursor.embedding pair.2.2.1 cursor.source)
  let joint := coupling.map project
  refine ⟨joint, ?_, ?_, ?_⟩
  · simpa only [joint, project, PMF.map_comp, Function.comp_def,
      sourceUnflaggedStrategy] using sourceMarginal
  · have marginal := fillMarginal cursor.source (fun _ _ => rfl)
    simpa only [joint, project, PMF.map_comp, Function.comp_def, profile, controls] using marginal
  · intro pair member
    obtain ⟨original, reached, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    obtain ⟨finished, last, lastTrace, attempt, history, point, excluded, generation,
      _live, agreement, word, labeled⟩ := supported original reached
    refine ⟨finished, last, lastTrace, attempt, history, ?_, point, excluded,
      generation, word, labeled, ?_⟩
    · exact fillCommitPrefix_eq_withoutMisses setup.program block suffix cursor.embedding
        cursor.refs original.2.2.1 cursor.source cursor.current.excluded finished last.excluded
          attempt cursor.source agreement
    · intro owner active
      exact fillCommitPrefix_view_of_attempt_agrees setup.program block suffix cursor.embedding
        cursor.refs original.2.2.1 cursor.source cursor.current.excluded finished last.excluded
          attempt agreement owner active

def residualBindingObservation
    (residual : ResidualProgram setup.program)
    (control : (nativeApplication).Control) (who : Player)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (value : L.Val payload) (completed : setup.proposalRecoveryProtocol.History) : Bool := by
  classical
  let block := SourceProgram.commitPhase residual.tail
  exact match completed.state.bind (fun current => residualEntry? block.suffix
      (fun point => residual.lift
        (cast (congrArg ProtocolState block.reconstruct)
          (block.block.liftPoint block.suffix point))) current.point) with
    | none => false
    | some finished => decide (
        (∀ owner, issuedLedger setup implementation block.block
          control.execution.application.attempt.phase control
          (control.execution.application.attempt.phase + block.block.length) owner
          (finished.view owner)) ∧
        block.block.wordAction who (event.val - control.execution.application.attempt.phase)
          (finished.view who) = decodeEventAction setup.program event
            (cast (congrArg EventField.Action binding.symm) (.success value)))

def bindingCompletedObservation
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (control : (nativeApplication).Control) (who : Player)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (value : L.Val payload) (completed : setup.proposalRecoveryProtocol.History) : Bool :=
  residualBindingObservation setup implementation checkpoint.residual control who event payload
    binding value completed

open Classical in
/-- The literal selected checkpoint and its backward-transferred entry
checkpoint parse precisely the same maximal complete binding observation. -/
theorem selected_binding_observation
    (operational : implementation.Operational)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (value : L.Val payload) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    (SourceProgram.commitPhase checkpoint.residual.tail).block.length = entry.block.length ∧
    bindingCompletedObservation setup implementation checkpoint control who event payload binding
      value =
      (fun completed : setup.proposalRecoveryProtocol.History =>
        match completed.state.bind (fun current => residualEntry? entry.suffix
            (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point))
              current.point) with
        | none => false
        | some finished => decide (
            (∀ owner, issuedLedger setup implementation entry.block
              control.execution.application.attempt.phase control
              (control.execution.application.attempt.phase + entry.block.length) owner
              (finished.view owner)) ∧
            entry.block.wordAction who (event.val - control.execution.application.attempt.phase)
              (finished.view who) = decodeEventAction setup.program event
                (cast (congrArg EventField.Action binding.symm) (.success value)))) := by
  classical
  intro checkpoint
  have maximum (program : SourceProgram Player L entry.witness.checkpoint.residual.context
      entry.witness.checkpoint.residual.names)
      (reconstruct : entry.block.prepend entry.suffix = program) :
      SourceProgram.commitPhase program =
        ⟨entry.targetContext, entry.targetNames, entry.suffix, entry.block, reconstruct,
          entry.boundary⟩ := by
    cases reconstruct
    exact maximal_commit_phase entry.block entry.suffix entry.boundary
  obtain ⟨saved, represented⟩ := entry.selected
  have length : (SourceProgram.commitPhase checkpoint.residual.tail).block.length =
      (SourceProgram.commitPhase entry.witness.checkpoint.residual.tail).block.length := by
    rw [represented]
    rfl
  have observed : bindingCompletedObservation setup implementation checkpoint control who event
      payload binding value = bindingCompletedObservation setup implementation
        entry.witness.checkpoint
        control who event payload binding value := by
    rw [represented]
    unfold bindingCompletedObservation
    rfl
  refine ⟨length.trans ?_, observed.trans ?_⟩
  · rw [maximum _ entry.reconstruct]
  · unfold bindingCompletedObservation
    let evaluate := fun phase : SourceProgram.CommitPhase
        entry.witness.checkpoint.residual.tail =>
      fun completed : setup.proposalRecoveryProtocol.History =>
        match completed.state.bind (fun current => residualEntry? phase.suffix
            (fun point => entry.witness.checkpoint.residual.lift
              (cast (congrArg ProtocolState phase.reconstruct)
                (phase.block.liftPoint phase.suffix point))) current.point) with
        | none => false
        | some finished => decide (
            (∀ owner, issuedLedger setup implementation phase.block
              control.execution.application.attempt.phase control
              (control.execution.application.attempt.phase + phase.block.length) owner
              (finished.view owner)) ∧
            phase.block.wordAction who (event.val - control.execution.application.attempt.phase)
              (finished.view who) = decodeEventAction setup.program event
                (cast (congrArg EventField.Action binding.symm) (.success value)))
    have identity : residualBindingObservation setup implementation
        entry.witness.checkpoint.residual control who event payload binding value =
          evaluate (SourceProgram.commitPhase entry.witness.checkpoint.residual.tail) := by
      funext completed
      unfold residualBindingObservation
      dsimp only [evaluate]
      split <;> split
      all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    have moved := congrArg evaluate (maximum _ entry.reconstruct)
    rw [identity, moved]
    have lift : (fun point => entry.witness.checkpoint.residual.lift
        (cast (congrArg ProtocolState entry.reconstruct)
          (entry.block.liftPoint entry.suffix point))) =
        (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point)) := by
      funext point
      exact (entry.lift _).symm
    funext completed
    dsimp only [evaluate]
    rw [lift]
    split <;> split
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]

omit [Fintype Player] in
private theorem binding_word_entry_independent
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (excluded : Finset Player) (store : Store (graphLayout setup.program))
    (first second : SourceProgram.Config Player L Γ) :
    phaseProposalBindingWord setup.program block suffix embedding excluded store first =
      phaseProposalBindingWord setup.program block suffix embedding excluded store second := by
  classical
  unfold phaseProposalBindingWord
  apply List.map_congr_left
  intro position member
  have inside := List.mem_range.mp member
  let index : Fin (eventCount (block.prepend suffix)) :=
    ⟨position, by have count := block.eventCount_prepend suffix; omega⟩
  funext who
  by_cases inactive : who ∈ excluded
  · simp only [inactive, ↓reduceIte]
  · simp only [inactive, ↓reduceIte]
    obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix index inside
    by_cases same : owner = who
    · subst owner
      have binding := (embedding.layout_eq index).trans layout
      rw [fillCommitPrefix_wordAction setup.program block suffix embedding actions store first who
        index inside payload binding,
        fillCommitPrefix_wordAction setup.program block suffix embedding actions store second who
          index inside payload binding]
    · have unowned : eventOwner? (block.prepend suffix) index ≠ some who := by
        rw [eventOwner?_eq_actor, EventGraph.actor?_of_outputLayout_binding _ layout]
        exact fun equal => same (Option.some.inj equal)
      rw [compiledCommitPrefix_wordAction_none_of_unowned block suffix who index
        unowned, compiledCommitPrefix_wordAction_none_of_unowned block suffix who
          index unowned]

open Classical in
/-- Every compatible closed entry has the same conditional complete-word
law, obtained by conditioning one source/graph joint before the static cut. -/
theorem closed_entry_binding_word
    (operational : implementation.Operational)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (alive : who ∉ control.execution.application.entry.excluded)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (value : L.Val payload)
    (current : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (erased : setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
      setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩)
    (present : true ∈ (((serviceGraph setup .concurrent).canonicalContinuation
      (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
        implementation.leaks implementation.plan entry.entry.execution entry.phase values)
      entry.entry.execution.application.current.native.config).map
      (fun key => issuedBindingObservation setup implementation control entry.phase key &&
        decide ((⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
          (.binding who payload)).get? key.2.1 = some (.success value)))).support) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let observed := bindingCompletedObservation setup implementation checkpoint control who event
      payload binding value
    let ordinary := setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) entry.block.length ⟨some current, targetTrace⟩
    let sourceLaw := fiberPosterior ordinary observed true
    let graphLaw := fiberPosterior
      ((serviceGraph setup .concurrent).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
          implementation.leaks implementation.plan entry.entry.execution entry.phase values)
        entry.entry.execution.application.current.native.config)
      (fun key => issuedBindingObservation setup implementation control entry.phase key &&
        decide ((⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
          (.binding who payload)).get? key.2.1 = some (.success value))) true
    true ∈ (ordinary.map observed).support ∧
      sourceLaw.map (fun completed =>
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace completed.trace)).take
          entry.block.length).reverse) =
        graphLaw.map (fun key => phaseProposalBindingWord setup.program entry.block entry.suffix
          entry.cursor.embedding control.execution.application.current.excluded key.2.1
            entry.cursor.source) ∧
      ∀ completed ∈ sourceLaw.support,
        ∃ (last : CommitRecoveryState setup.program)
          (lastTrace : setup.proposalRecoveryProtocol.Trace (some last)),
          completed = ⟨some last, lastTrace⟩ ∧ TracePrefix targetTrace lastTrace ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
            (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace)).take
              entry.block.length ++
                setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetTrace) ∧
          ∀ owner, owner ∉ control.execution.application.current.excluded →
            ProtocolState.BindingsHoldValues owner setup.program last.point := by
  classical
  intro checkpoint observed ordinary sourceLaw graphLaw
  let cursor := PhaseProposalOrdinarySourceCursor.of_erasedHistory setup .concurrent
    implementation.runtime implementation.leaks implementation.plan entry.entry entry.phase
    entry.block entry.suffix entry.cursor current targetTrace erased
  have cursorEmbedding : cursor.embedding = entry.cursor.embedding := rfl
  have cursorLift : cursor.lift = entry.cursor.lift := rfl
  have cursorConfig : cursor.config = entry.cursor.config := rfl
  have cursorOffset : cursor.offset = entry.cursor.offset := rfl
  have low : control.execution.application.attempt.phase = entry.phase.low := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have offset : cursor.offset = control.execution.application.attempt.phase := entry.offset.trans
    low.symm
  have originalOffset : entry.cursor.offset = control.execution.application.attempt.phase :=
    entry.offset.trans low.symm
  have length : entry.phase.high = cursor.offset + entry.block.length := by
    have size := entry.size
    have nonempty := entry.phase.nonempty
    have start : cursor.offset = entry.phase.low := entry.offset
    omega
  have selectedInside : event.val - cursor.offset < entry.block.length := by
    have bounds := (entry.phase.mem_events event).mp entry.inside
    have start := entry.offset
    change cursor.offset = entry.phase.low at start
    omega
  let index : Fin (eventCount (entry.block.prepend entry.suffix)) :=
    ⟨event.val - cursor.offset, by have count := entry.block.eventCount_prepend entry.suffix; omega⟩
  have named : cursor.embedding.event index = event := by
    apply Fin.ext
    rw [cursor.compiled.rankEq]
    have bounds := (entry.phase.mem_events event).mp entry.inside
    have start := entry.offset
    change cursor.offset = entry.phase.low at start
    dsimp only [index]
    omega
  have originalNamed : entry.cursor.embedding.event index = event := by
    simpa only [cursorEmbedding] using named
  have saved := Classical.choose entry.selected
  have cursorExcluded : cursor.current.excluded = control.execution.application.entry.excluded :=
    cursor.excluded.trans (entry.entryExcluded.symm.trans (congrArg RecoveryState.excluded saved))
  have selectedBinding : (serviceGraph setup .concurrent).outputLayout
      (cursor.embedding.event index) = .binding who payload := by
    rw [named]
    exact binding
  let sourceObserved := fun completed : setup.proposalRecoveryProtocol.History =>
    match completed.state.bind (fun last => residualEntry? entry.suffix
        (fun point => cursor.lift (entry.block.liftPoint entry.suffix point)) last.point) with
    | none => false
    | some finished => decide (
        (∀ owner, issuedLedger setup implementation entry.block cursor.offset control
          (cursor.offset + entry.block.length) owner (finished.view owner)) ∧
        entry.block.wordAction who index.val (finished.view who) =
          decodeEventAction setup.program (cursor.embedding.event index)
            (cast (congrArg EventField.Action selectedBinding.symm) (.success value)))
  have observation : observed = sourceObserved := by
    have equal := (selected_binding_observation setup implementation operational control
      trace
      who event payload binding entry value).2
    change bindingCompletedObservation setup implementation checkpoint control who event
      payload binding value = sourceObserved
    rw [equal]
    funext completed
    dsimp only [sourceObserved]
    split <;> split
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    all_goals
      apply decide_eq_decide.mpr
      have decodeTransport {first second : (serviceGraph setup .concurrent).EventId}
          (same : first = second)
          (layout : (serviceGraph setup .concurrent).outputLayout second = .binding who payload)
          (result : PublicationResult (L.Val payload)) :
          decodeEventAction setup.program first
              (cast (congrArg EventField.Action (same.symm ▸ layout).symm) result) =
            decodeEventAction setup.program second
              (cast (congrArg EventField.Action layout.symm) result) := by
        cases same
        rfl
      have decoded : decodeEventAction setup.program (cursor.embedding.event index)
          (cast (congrArg EventField.Action selectedBinding.symm) (.success value)) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action binding.symm) (.success value)) :=
        decodeTransport (show cursor.embedding.event index = event from originalNamed)
          binding (.success value)
      have rankEq : index.val = event.val - entry.phase.low := by
        change event.val - cursor.offset = event.val - entry.phase.low
        exact congrArg (fun low => event.val - low) offset
      rw [decoded, rankEq]
  obtain ⟨joint, sourceMarginal, graphMarginal, supported⟩ :=
    ordinary_binding_conditioned_word_coupling setup values implementation control trace
      entry.entry entry.entryTrace entry.phase entry.block entry.suffix cursor cursorExcluded
      entry.offset.symm length who alive index selectedInside payload selectedBinding value (by
        simpa [issuedBindingObservation, cursorConfig, cursorEmbedding,
          originalNamed, entry.config] using
          present)
  have sourceMarginal' : joint.map Prod.fst = sourceLaw := by
    dsimp only [sourceLaw]
    rw [observation]
    dsimp only [ordinary, cursor, PhaseProposalOrdinarySourceCursor.of_erasedHistory]
      at sourceMarginal ⊢
    refine sourceMarginal.trans ?_
    apply congrArg (fun test : setup.proposalRecoveryProtocol.History → Bool =>
      fiberPosterior ordinary test true)
    funext completed
    dsimp only [sourceObserved]
    split <;> split
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    all_goals
      exact decide_eq_decide.mpr Iff.rfl
  have graphMarginal' : joint.map Prod.snd = graphLaw := by
    simpa [graphLaw, cursorConfig, cursorEmbedding, originalNamed,
      issuedBindingObservation, entry.config]
      using graphMarginal
  have sourcePresent : true ∈ (ordinary.map observed).support := by
    obtain ⟨pair, member⟩ := joint.support_nonempty
    have reached : pair.1 ∈ sourceLaw.support := by
      rw [← sourceMarginal']
      exact (PMF.mem_support_map_iff ..).mpr ⟨pair, member, rfl⟩
    have observedTrue : observed pair.1 = true := by
      rw [observation]
      apply Eq.trans ?_ (supported pair member).2.1
      dsimp only [sourceObserved]
      split <;> split
      all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    by_contra absent
    change pair.1 ∈ (fiberPosterior ordinary observed true).support at reached
    rw [fiberPosterior_of_not_mem_support ordinary observed absent] at reached
    exact absent ((PMF.mem_support_map_iff ..).mpr ⟨pair.1, reached, observedTrue⟩)
  refine ⟨sourcePresent, ?_, ?_⟩
  · rw [← sourceMarginal', ← graphMarginal', PMF.map_comp, PMF.map_comp]
    apply map_congr_on_support joint
    intro pair member
    have read := (supported pair member).2.2.2
    have sameSource := binding_word_entry_independent setup entry.block entry.suffix
      entry.cursor.embedding entry.cursor.views.actionEq cursor.current.excluded pair.2.2.1
      cursor.source entry.cursor.source
    exact read.trans (by simpa [cursor,
      PhaseProposalOrdinarySourceCursor.of_erasedHistory, Function.comp_def,
      ← cursor.excluded, entry.excluded] using sameSource)
  · intro completed completedSupported
    have original := (mem_support_fiberPosterior sourcePresent completedSupported).2
    have member : completed ∈ (joint.map Prod.fst).support := by
      rw [sourceMarginal']
      exact completedSupported
    obtain ⟨pair, pairSupported, equal⟩ := (PMF.mem_support_map_iff ..).mp member
    obtain ⟨finished, last, lastTrace, attempt, stateEq, point, excluded, _generation,
      live, _agreement, word, _labels⟩ := (supported pair pairSupported).1
    have completedEq : completed = ⟨some last, lastTrace⟩ := equal.symm.trans stateEq
    have past := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
      (sourceUnflaggedStrategy setup values) entry.block.length ⟨some current, targetTrace⟩
      completed original).tracePrefix
    refine ⟨last, lastTrace, completedEq, ?_, ?_, ?_⟩
    · cases completedEq
      exact past
    · have take : (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace)).take
          entry.block.length = attempt.joints.reverse := by
        rw [word, ← attempt.joints_length, ← List.length_reverse, List.take_left]
      rw [take]
      exact word
    · intro owner active
      rw [point]
      apply (cursor.origin.bindingsHoldValues_lift owner _).mpr
      apply ((entry.block.protocolSuffix entry.suffix).bindingsHoldValues_lift owner _).mpr
      apply (ProtocolState.bindingsHoldValues_entry owner entry.suffix finished).mpr
      exact live owner (by
        rw [excluded, cursor.excluded, ← entry.excluded]
        exact active)

omit [Fintype Player] [L.ResultTypes] in
theorem structural_replay_eq_of_joints
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (first second : SourceProgram.Config Player L Δ) (firstAfter secondAfter : Finset Player)
    (left : block.Attempt entry excluded first firstAfter)
    (right : block.Attempt entry excluded second secondAfter)
    (same : left.joints = right.joints)
    (replacement : SourceProgram.Config Player L Γ) :
    left.withoutMisses ∅ replacement = right.withoutMisses ∅ replacement := by
  induction block generalizing excluded with
  | nil => cases left; cases right; rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
    cases left with
    | active active result missed valid later =>
      cases right with
      | excluded inactive other => exact (active inactive).elim
      | active otherActive otherResult otherMissed otherValid other =>
        have heads := congrFun (List.cons.inj same).1 owner
        simp only [ite_true,
          Option.some.injEq, CommitRecoveryMove.mk.injEq, OwnAction.commit.injEq,
          heq_eq_eq, true_and] at heads
        obtain ⟨rfl, rfl⟩ := heads
        exact ih _ _ _ _ later other (List.cons.inj same).2 _
    | excluded inactive later =>
      cases right with
      | active active result missed valid other => exact (active inactive).elim
      | excluded otherInactive other =>
        simpa only [SourceProgram.CommitPrefix.Attempt.withoutMisses,
          Finset.notMem_empty, ↓reduceIte] using
            ih _ _ _ _ later other (List.cons.inj same).2 _

/-- At a fixed ordinary entry, the complete retained source word determines
the structural block configuration. Automatic excluded instructions determine
their synthetic structural failures without changing the actual source word. -/
private theorem ordinary_source_structural_projection
    (anchor : (nativeApplication).Control)
    (anchorTrace : (nativeProtocol).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase block suffix) :
    let law := setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length ⟨some cursor.current, cursor.trace⟩
    let controls : Finset Player × Nat × Nat :=
      ((anchor.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
            anchor.execution.application.attempt.phase,
        anchor.execution.application.attempt.generation,
        anchor.execution.application.attempt.phase)
    let profile := ordinaryBlockProfile setup .concurrent implementation.plan values
      block suffix cursor.embedding (fun owner view => cursor.views.view owner view)
        controls anchor.execution.application.publicView
          (PhaseProposal.sourceArchive anchor.execution.network.inputs)
    ∃ reconstruct : setup.proposalRecoveryProtocol.History → SourceProgram.Config Player L Δ,
      law.map reconstruct = block.prefixLaw suffix profile cursor.source ∧
      ∀ history ∈ law.support,
        ∃ (finished : SourceProgram.Config Player L Δ)
          (last : CommitRecoveryState setup.program)
          (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
          (attempt : block.Attempt cursor.source cursor.current.excluded finished last.excluded),
          history = ⟨some last, lastTrace⟩ ∧
          reconstruct history = attempt.withoutMisses ∅ cursor.source ∧
          last.point = cursor.lift (block.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
          last.excluded = cursor.current.excluded ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
            attempt.joints.reverse ++ setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace cursor.trace) ∧
          setup.proposalRecoveryJointRecall lastTrace =
            attempt.joints.reverse.map
              (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) ++
                setup.proposalRecoveryJointRecall cursor.trace ∧
          (∀ owner, owner ∉ last.excluded →
            finished.view owner = (reconstruct history).view owner) ∧
          ∀ row ∈ attempt.joints, ∀ owner move, row owner = some move →
            move.missing = false ∧ ¬ move.action.IsFailure := by
  classical
  intro law controls profile
  obtain ⟨joint, sourceMarginal, structuralMarginal, related⟩ :=
    ordinary_source_structural_joint setup values implementation anchor anchorTrace phase
      block suffix cursor
  have functional (history : setup.proposalRecoveryProtocol.History)
      (first second : SourceProgram.Config Player L Δ)
      (left : (history, first) ∈ joint.support)
      (right : (history, second) ∈ joint.support) : first = second := by
    obtain ⟨firstConfig, firstState, firstTrace, firstAttempt, firstHistory, firstReplay,
      _firstPoint, _firstExcluded, _firstGeneration, firstWord, _firstLabels, _firstViews⟩ :=
        related (history, first) left
    obtain ⟨secondConfig, secondState, secondTrace, secondAttempt, secondHistory, secondReplay,
      _secondPoint, _secondExcluded, _secondGeneration, secondWord, _secondLabels, _secondViews⟩ :=
        related (history, second) right
    have words : firstAttempt.joints = secondAttempt.joints := by
      have read : setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace firstTrace) =
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace secondTrace) :=
        congrArg (fun retained : setup.proposalRecoveryProtocol.History =>
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retained.trace))
            (firstHistory.symm.trans secondHistory)
      rw [firstWord, secondWord] at read
      exact List.reverse_injective (List.append_cancel_right read)
    exact firstReplay.trans ((structural_replay_eq_of_joints block cursor.source
      cursor.current.excluded firstConfig secondConfig firstState.excluded secondState.excluded
        firstAttempt secondAttempt words cursor.source).trans secondReplay.symm)
  let default := Classical.choose joint.support_nonempty
  let reconstruct := fun history : setup.proposalRecoveryProtocol.History =>
    if witness : ∃ finished, (history, finished) ∈ joint.support then Classical.choose witness
    else default.2
  have reconstructEq (pair : setup.proposalRecoveryProtocol.History ×
      SourceProgram.Config Player L Δ) (member : pair ∈ joint.support) :
      reconstruct pair.1 = pair.2 := by
    have witness : ∃ finished, (pair.1, finished) ∈ joint.support := ⟨pair.2, member⟩
    dsimp only [reconstruct]
    split
    · next present =>
        exact functional pair.1 _ pair.2 (Classical.choose_spec present) member
    · next absent => exact (absent witness).elim
  refine ⟨reconstruct, ?_, ?_⟩
  · calc
      law.map reconstruct = (joint.map Prod.fst).map reconstruct :=
        congrArg (PMF.map reconstruct) sourceMarginal.symm
      _ = joint.map (reconstruct ∘ Prod.fst) := PMF.map_comp _ _ _
      _ = joint.map Prod.snd :=
        map_congr_on_support joint (fun pair member => reconstructEq pair member)
      _ = block.prefixLaw suffix profile cursor.source := structuralMarginal
  · intro history member
    have mapped : history ∈ (joint.map Prod.fst).support := sourceMarginal.symm ▸ member
    obtain ⟨pair, reached, sourceEq⟩ := (PMF.mem_support_map_iff ..).mp mapped
    obtain ⟨finished, last, lastTrace, attempt, historyEq, replay, point, excluded,
      _generation, word, labels, views⟩ := related pair reached
    refine ⟨finished, last, lastTrace, attempt, sourceEq.symm.trans historyEq,
      ?_, point, excluded, word, labels, ?_, ?_⟩
    · rw [← sourceEq, reconstructEq pair reached]
      exact replay
    · intro owner active
      rw [← sourceEq, reconstructEq pair reached]
      exact views owner active
    · obtain ⟨actual, actualState, actualTrace, actualAttempt, actualHistory,
        _actualPoint, _actualExcluded, _actualEntry, _actualGeneration, actualWord,
        _actualLabels, actualProper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values block suffix cursor.lift
          cursor.origin cursor.source cursor.current cursor.trace cursor.point
            (cursor.excluded.trans cursor.entryExcluded.symm) history member
      have words : attempt.joints = actualAttempt.joints := by
        have equal := congrArg (fun retained : setup.proposalRecoveryProtocol.History =>
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retained.trace))
            ((sourceEq.symm.trans historyEq).symm.trans actualHistory)
        rw [word, actualWord] at equal
        exact List.reverse_injective (List.append_cancel_right equal)
      simpa only [words] using actualProper

open Classical in
/-- A supported actual source completion retaining the issued ledgers gives
a positive foreign cylinder in the literal ordinary joint. This implication
is proved before annotation normalization and also applies to every supported
closed-key history. -/
theorem ordinaryForeignJoint_positive_of_source_ledger
    (operational : implementation.Operational)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (saved : control.execution.application.current.excluded =
      control.execution.application.entry.excluded) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    ∀ cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control phase block.block block.suffix,
      0 < block.block.length →
      cursor.embedding = cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          block.reconstruct.symm) checkpoint.embedding →
      (∀ point, cursor.lift point = checkpoint.residual.lift
        (cast (congrArg ProtocolState block.reconstruct) point)) →
      (∀ owner view, cursor.views.view owner view = checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) →
    let observed := fun history : setup.proposalRecoveryProtocol.History =>
      match history.state.bind (fun current => residualEntry? block.suffix
          (fun point => cursor.lift (block.block.liftPoint block.suffix point)) current.point) with
      | none => false
      | some finished => decide (∀ owner, issuedLedger setup implementation block.block
          control.execution.application.attempt.phase control
            (control.execution.application.attempt.phase + block.block.length) owner
              (finished.view owner))
    true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
      block.block.length ⟨some cursor.current, cursor.trace⟩).map observed).support →
    true ∈ ((ordinaryForeignJoint setup values implementation operational who
      ⟨some control, trace⟩ ⟨some cursor.current, cursor.trace⟩).map Prod.snd).support := by
  classical
  intro checkpoint block cursor positive embedding lift views observed present
  obtain ⟨joint, sourceMarginal, structuralMarginal, supported⟩ :=
    ordinary_source_structural_joint setup values implementation control trace phase block.block
      block.suffix cursor
  obtain ⟨history, reached, measured⟩ := (PMF.mem_support_map_iff ..).mp present
  have reachedJoint : history ∈ (joint.map Prod.fst).support := by
    rw [sourceMarginal]
    exact reached
  obtain ⟨pair, member, sourceEq⟩ := (PMF.mem_support_map_iff ..).mp reachedJoint
  obtain ⟨finished, last, lastTrace, attempt, historyEq, structuralEq, point,
    excluded, _generation, _word, _labels, activeViews⟩ := supported pair member
  have pulled : residualEntry? block.suffix
      (fun point => cursor.lift (block.block.liftPoint block.suffix point)) last.point =
        some finished :=
    (residualEntry?_eq_some_iff (cursor.origin.compose (block.block.protocolSuffix block.suffix))
      last.point finished).mpr point.symm
  have sourceObserved : observed pair.1 = true := (congrArg observed sourceEq).trans measured
  have sourceLedger : ∀ owner, issuedLedger setup implementation block.block
      control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + block.block.length) owner
          (finished.view owner) := by
    simpa only [observed, historyEq, Option.bind_some, pulled, decide_eq_true_eq]
      using sourceObserved
  have actualLedger : ∀ owner, issuedLedger setup implementation block.block
      control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + block.block.length) owner
          (pair.2.view owner) := by
    intro owner
    by_cases omitted : owner ∈ control.execution.application.entry.excluded
    · intro event payload binding candidate message emitted attemptMatch packetMatch interval
      have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace
      have inputRecall := (nativeApplication).history_inputRecall nativeInitial
        implementation.horizon
        implementation.scheduler raw owner
      have input : message ∈ control.execution.network.inputs := by
        rw [← inputRecall] at emitted
        exact (List.mem_filter.mp emitted).1
      have active := issued_binding_owner_active setup implementation control trace owner event
        payload binding candidate message input attemptMatch packetMatch
      exact (active omitted).elim
    · have live : owner ∉ last.excluded := by
        rw [excluded, cursor.excluded, saved]
        exact omitted
      rw [← activeViews owner live]
      exact sourceLedger owner
  have footprint :
      (control.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          control.execution.application.current.native.publicView.sourceFailureFootprint.1
            control.execution.application.attempt.phase =
        control.execution.application.entry.excluded := by
    have current := congrArg Prod.fst (cursor.controls positive)
    change cursor.current.excluded = _ at current
    exact current.symm.trans (cursor.excluded.trans saved)
  have structuralSupport : pair.2 ∈
      (block.block.prefixLaw block.suffix
        (ordinaryBlockProfile setup .concurrent implementation.plan values block.block block.suffix
          cursor.embedding (fun owner view => cursor.views.view owner view)
            (control.execution.application.entry.excluded, control.execution.application.generation,
              control.execution.application.attempt.phase) control.execution.application.publicView
                (PhaseProposal.sourceArchive control.execution.network.inputs))
                  cursor.source).support := by
    have mapped : pair.2 ∈ (joint.map Prod.snd).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨pair, member, rfl⟩
    rw [structuralMarginal] at mapped
    rw [footprint] at mapped
    simpa only [PhaseRuntimeState.attempt] using mapped
  rw [ordinaryForeignJoint_of_selected_cursor setup values implementation operational who control
    trace phase cursor positive embedding lift views, PMF.map_comp]
  exact (PMF.mem_support_map_iff ..).mpr
    ⟨pair.2, structuralSupport, decide_eq_true (fun owner _ => actualLedger owner)⟩

omit [Fintype Player] in
/-- A complete history determines its retained cut at a fixed literal depth.
This lifts equality of completion marginals to equality of both coordinates. -/
private theorem source_pair_eq_of_completed
    (left right : PMF
      (setup.proposalRecoveryProtocol.History × setup.proposalRecoveryProtocol.History))
    (depth : Nat)
    (leftPrefix : ∀ pair ∈ left.support, TracePrefix pair.1.trace pair.2.trace)
    (rightPrefix : ∀ pair ∈ right.support, TracePrefix pair.1.trace pair.2.trace)
    (leftDepth : ∀ pair ∈ left.support, pair.1.trace.length = depth)
    (rightDepth : ∀ pair ∈ right.support, pair.1.trace.length = depth)
    (completed : left.map Prod.snd = right.map Prod.snd) : left = right := by
  have lifted := bind_eq_of_map_eq left right Prod.snd Prod.snd completed PMF.pure PMF.pure (by
    intro first firstMember second secondMember same
    apply congrArg PMF.pure
    apply Prod.ext
    · have firstKept := leftPrefix first firstMember
      have secondKept := rightPrefix second secondMember
      rw [← same] at secondKept
      exact firstKept.eq_of_same_length secondKept
        ((leftDepth first firstMember).trans (rightDepth second secondMember).symm)
    · exact same)
  simpa only [PMF.bind_pure] using lifted

/-- The split ordinary run retains the literal cut as a prefix of its
completion, at the exact depth of the first commitment segment. Empty first
segments are included. -/
theorem ordinary_source_pair_geometry
    (anchor : (nativeApplication).Control)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (before : SourceProgram.CommitPrefix Γ O Δ P)
    (after : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase (before.append after) suffix) :
    let profile := sourceUnflaggedStrategy setup values
    let law := (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
      ⟨some cursor.current, cursor.trace⟩).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile after.length cut).map (Prod.mk cut)
    ∀ pair ∈ law.support, TracePrefix pair.1.trace pair.2.trace ∧
      pair.1.trace.length = cursor.trace.length + before.length := by
  classical
  intro profile law pair member
  obtain ⟨cut, first, continued⟩ := (PMF.mem_support_bind_iff ..).mp member
  obtain ⟨completed, last, rfl⟩ := (PMF.mem_support_map_iff ..).mp continued
  refine ⟨(setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
    profile after.length cut completed last).tracePrefix, ?_⟩
  obtain ⟨lift, origin, point⟩ :
      ∃ lift : ProtocolState (before.prepend (after.prepend suffix)) →
          ProtocolState setup.program,
        ProtocolSuffix setup.program (before.prepend (after.prepend suffix)) lift ∧
        cursor.current.point = lift
          (ProtocolState.entry (before.prepend (after.prepend suffix)) cursor.source) := by
    rw [← before.prepend_append after suffix]
    exact ⟨cursor.lift, cursor.origin, cursor.point⟩
  obtain ⟨finished, current, trace, attempt, same, _point, _excluded, _entry,
      _generation, word, _labels, _proper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values before (after.prepend suffix)
      lift origin cursor.source cursor.current cursor.trace point
        (cursor.excluded.trans cursor.entryExcluded.symm) cut first
  change cut.trace.length = cursor.trace.length + before.length
  rw [same]
  have length := congrArg List.length word
  simpa only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
    List.length_append, List.length_reverse, attempt.joints_length,
    Nat.add_comm] using length

/-- The dynamic completion fuel of a listed proper ordinary word is exactly
the remaining length of the original maximal commitment telescope. The cut
may precede its first row. -/
private theorem source_word_pair_fuel
    (anchor : (nativeApplication).Control)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (before : SourceProgram.CommitPrefix Γ O Δ P)
    (after : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (boundary : IsCommitBoundary suffix)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase (before.append after) suffix)
    (word : SourceProgram.History Player L) (views : ∀ owner, DecisionView owner Ξ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, (before.append after).wordAction owner index (views owner) = some action)
    (proper : ∀ owner action, action ∈ word owner → ¬ action.IsFailure) :
    let profile := sourceBlockWordStrategy setup values word
    let varying := (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
      ⟨some cursor.current, cursor.trace⟩).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile (sourceCommitFuel setup cut) cut).map
          (Prod.mk cut)
    let fixed := (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
      ⟨some cursor.current, cursor.trace⟩).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile after.length cut).map (Prod.mk cut)
    varying = fixed ∧ ∀ pair ∈ varying.support,
      TracePrefix pair.1.trace pair.2.trace ∧
        pair.1.trace.length = cursor.trace.length + before.length := by
  classical
  intro profile varying fixed
  let table := fun owner (key : setup.ProposalRecoveryComponent owner) =>
    if offered : ∃ choice : setup.CommitRecoveryValueChoice owner key.1,
        ∃ action ∈ word owner, choice.val.val = some ⟨action, false⟩ then
      PMF.pure (Classical.choose offered)
    else values owner key
  have strategy : profile = sourceUnflaggedStrategy setup table :=
    source_word_strategy_table setup values (before.append after) word views readout proper
  obtain ⟨lift, origin, point⟩ :
      ∃ lift : ProtocolState (before.prepend (after.prepend suffix)) →
          ProtocolState setup.program,
        ProtocolSuffix setup.program (before.prepend (after.prepend suffix)) lift ∧
        cursor.current.point = lift
          (ProtocolState.entry (before.prepend (after.prepend suffix)) cursor.source) := by
    rw [← before.prepend_append after suffix]
    exact ⟨cursor.lift, cursor.origin, cursor.point⟩
  have remaining (cut : setup.proposalRecoveryProtocol.History)
      (member : cut ∈ (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
        ⟨some cursor.current, cursor.trace⟩).support) : sourceCommitFuel setup cut = after.length
          := by
    rw [strategy] at member
    obtain ⟨finished, last, lastTrace, _attempt, history, lastPoint, _excluded, _entry,
      _generation, _word, _labels, _proper⟩ :=
      proposalRecovery_ordinary_commit_block_support setup table before (after.prepend suffix)
        lift origin cursor.source cursor.current cursor.trace point
          (cursor.excluded.trans cursor.entryExcluded.symm) cut member
    let tailOrigin := origin.compose (before.protocolSuffix (after.prepend suffix))
    rw [history]
    change ProtocolState.remaining setup.program last.point -
      ProtocolState.commitEnd setup.program last.point = after.length
    rw [lastPoint, tailOrigin.remaining_lift, tailOrigin.commitEnd_lift,
      ProtocolState.remaining_entry, after.commitEnd_entry_prepend suffix boundary]
    have length := after.instructionCount_prepend suffix
    omega
  have equality : varying = fixed := by
    apply bind_congr_on_support
    intro cut member
    rw [remaining cut member]
  refine ⟨equality, ?_⟩
  rw [equality]
  simpa only [fixed, strategy] using ordinary_source_pair_geometry setup table implementation
    anchor phase before after suffix cursor

omit [Fintype Player] in
private theorem binding_material_action
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (response : (nativeApplication).Action)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : response.transmission = some material)
    (candidate : Handle (serviceGraph setup .concurrent))
    (named : material.call.packet = .commitment event candidate) :
    phaseBindingAction? setup.program .concurrent implementation.runtime implementation.leaks
      response = decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm)
          ((material.call.opening.bind fun raw => raw.as? payload).elim
            .failure PublicationResult.success)) := by
  simp only [phaseBindingAction?, transmitted, named]
  split
  · rename_i other domain shape
    cases shape.symm.trans binding
    cases decoded : material.call.opening.bind (fun raw => raw.as? payload) <;> rfl
  · rename_i _ shape
    exact (shape owner payload binding).elim

/-- The actions mentioned in the focal raw recall are exactly the earlier
owned rows of any retained source ledger. This uses the actual signed records
and readiness, and permits arbitrary inherited exclusions. -/
private theorem issued_ledger_recall_actions
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low) (phaseHigh : phase.high = low + block.length)
    (owner : Player) (selected : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout selected = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧ selected.val < low + block.length)
    (reference : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control (low + block.length)
      owner reference) :
    ∀ action, action ∈ phaseCommitRecallWord setup.program .concurrent implementation.runtime
        implementation.leaks low selected.val control.execution.application.generation
          (control.execution.recall owner) ↔
      ∃ position < selected.val - low, block.wordAction owner position reference = some action := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  let initialLaw := inputs.map (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initialLaw = nativeInitial := PMF.map_comp _ _ _
  have counted : ((nativeMenu).protocol initialLaw implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have inputRecall := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler raw owner
  have address : control.execution.application.attempt =
      ⟨low, control.execution.application.generation⟩ := by
    have phaseEq : control.execution.application.attempt.phase = low := by
      simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some, phaseLow]
    exact congrArg (fun phase =>
      (⟨phase, control.execution.application.generation⟩ : CommitAttemptId)) phaseEq
  have clean := (PhaseCount.onePacketMenu_countClean implementation.runtime implementation.leaks
    implementation.bounds implementation.scheduler).history nativeInitial implementation.horizon
      (fun state _ => PhaseCount.countClean_initial implementation.runtime implementation.leaks
        state) trace
  have emissionAction
      (event : (serviceGraph setup .concurrent).EventId) (domain : L.Ty)
      (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner domain)
      (candidate : Handle (serviceGraph setup .concurrent))
      (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
      (emitted : message ∈ (nativeApplication).outputs (control.execution.recall owner))
      (attemptMatch : message.payload.attempt = control.execution.application.attempt)
      (call : message.payload.packet.call = .commitment event candidate)
      (interval : low ≤ event.val ∧ event.val < low + block.length) :
      ∃ record ∈ control.execution.recall owner,
        record.emitted = some message ∧
        phaseBindingAction? setup.program .concurrent implementation.runtime implementation.leaks
          record.action = block.wordAction owner (event.val - low) reference := by
    obtain ⟨serial, opening, evidence, record, slot, recorded, sent, declared, _fresh, result⟩ :=
      retained event domain shape candidate message emitted attemptMatch call interval
    let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
      ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
    have decoded := binding_material_action setup implementation owner event domain shape
      record.action material (by rw [declared]) (owner, .prepared serial) rfl
    have inside : event.val - low < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨event.val - low, by have count := block.eventCount_prepend suffix; omega⟩
    have named : embedding.event index = event := by
      apply Fin.ext
      rw [rank]
      dsimp only [index]
      omega
    have codec := phaseCommitWordAction_decode setup .concurrent block suffix embedding actions
      owner index inside domain (named.symm ▸ shape) reference
    have dataTransport {first second : (serviceGraph setup .concurrent).EventId}
        (same : first = second)
        (layout : (serviceGraph setup .concurrent).outputLayout second = .binding owner domain)
        (word : Option (OwnAction Player L)) :
        (phaseRecoveryBindingData setup .concurrent first owner domain
          (same.symm ▸ layout) (CommitRecoveryMove.lift word)).1 =
        (phaseRecoveryBindingData setup .concurrent second owner domain
          layout (CommitRecoveryMove.lift word)).1 := by
      cases same
      rfl
    have decodeTransport {first second : (serviceGraph setup .concurrent).EventId}
        (same : first = second)
        (layout : (serviceGraph setup .concurrent).outputLayout second = .binding owner domain)
        (result : PublicationResult (L.Val domain)) :
        decodeEventAction setup.program first
            (cast (congrArg EventField.Action (same.symm ▸ layout).symm) result) =
          decodeEventAction setup.program second
            (cast (congrArg EventField.Action layout.symm) result) := by
      cases same
      rfl
    have codec' : decodeEventAction setup.program event
      (cast (congrArg EventField.Action shape.symm)
        (phaseRecoveryBindingData setup .concurrent event owner domain shape
          (CommitRecoveryMove.lift
            (block.wordAction owner (event.val - low) reference))).1) =
        block.wordAction owner (event.val - low) reference := by
      calc
        _ = decodeEventAction setup.program event
            (cast (congrArg EventField.Action shape.symm)
              (phaseRecoveryBindingData setup .concurrent (embedding.event index) owner domain
                (named.symm ▸ shape) (CommitRecoveryMove.lift
                  (block.wordAction owner (event.val - low) reference))).1) := by
              rw [← dataTransport named shape]
        _ = decodeEventAction setup.program (embedding.event index)
            (cast (congrArg EventField.Action (named.symm ▸ shape).symm)
              (phaseRecoveryBindingData setup .concurrent (embedding.event index) owner domain
                (named.symm ▸ shape) (CommitRecoveryMove.lift
                  (block.wordAction owner (event.val - low) reference))).1) :=
            (decodeTransport named shape _).symm
        _ = block.wordAction owner (event.val - low) reference := by
          simpa only [index] using codec
    refine ⟨record, recorded, sent, decoded.trans ?_⟩
    exact (congrArg (fun value => decodeEventAction setup.program event
      (cast (congrArg EventField.Action shape.symm) value)) result).trans codec'
  intro action
  constructor
  · intro member
    obtain ⟨record, recorded, parsed⟩ := List.mem_filterMap.mp member
    split at parsed
    · rename_i attempt
      cases transmitted : record.action.transmission with
      | none => simp only [transmitted, reduceCtorEq] at parsed
      | some material =>
        simp only [transmitted] at parsed
        cases packet : material.call.packet with
        | opening | malformed => simp only [packet, reduceCtorEq] at parsed
        | commitment event candidate =>
          simp only [packet] at parsed
          split at parsed
          · rename_i interval
            obtain ⟨message, emitted, sender, emittedCall⟩ :=
              PhaseCount.recalled_submission_emitted implementation.runtime implementation.leaks
                nativeInitial implementation.horizon implementation.scheduler raw owner record
                  recorded material transmitted
            have output : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
              List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
            have input : message ∈ control.execution.network.inputs := by
              rw [← inputRecall] at output
              exact (List.mem_filter.mp output).1
            have call : message.payload.packet.call = .commitment event candidate :=
              emittedCall.trans packet
            have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
            change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
            simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
            obtain ⟨owned, _evidence, _candidateOwner, _prepared, _unused⟩ := correct
            have typed : ∃ domain,
                (serviceGraph setup .concurrent).outputLayout event = .binding owner domain := by
              cases shape : (serviceGraph setup .concurrent).outputLayout event <;>
                simp only [bindingOwnedBy, shape, Bool.false_eq_true, decide_eq_true_eq] at owned
              rename_i actor domain
              subst actor
              exact ⟨domain, by
                have senderShape := congrArg (fun actor => EventField.binding actor domain) sender
                simpa only [Message.sender] using senderShape⟩
            obtain ⟨domain, shape⟩ := typed
            have attemptMatch : message.payload.attempt = control.execution.application.attempt :=
              (phase_recalled_emission_attempt implementation.runtime implementation.leaks
                nativeInitial implementation.horizon implementation.scheduler raw owner record
                  recorded message emitted).trans (attempt.trans address.symm)
            obtain ⟨actual, actualMember, actualSent, decoded⟩ := emissionAction event domain shape
              candidate message output attemptMatch call ⟨interval.1, by omega⟩
            have same := recorded_emission_unique setup implementation trace owner actual record
              actualMember recorded message actualSent emitted
            rw [same, parsed] at decoded
            exact ⟨event.val - low, by omega, decoded.symm⟩
          · cases parsed
    · cases parsed
  · rintro ⟨position, before, selectedAction⟩
    have inside : position < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨position, by have count := block.eventCount_prepend suffix; omega⟩
    have owns : eventOwner? (block.prepend suffix) index = some owner := by
      by_contra absent
      have none := compiledCommitPrefix_wordAction_none_of_unowned block suffix owner index
        absent reference
      rw [selectedAction] at none
      cases none
    obtain ⟨actor, domain, _member, layout⟩ := block.binding_before_length suffix index inside
    have sameOwner : actor = owner := by
      have actorEq := EventGraph.actor?_of_outputLayout_binding
        (toEventGraph (block.prepend suffix)) layout
      rw [eventOwner?_eq_actor, actorEq] at owns
      exact Option.some.inj owns
    subst actor
    have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
        .binding owner domain := (embedding.layout_eq index).trans layout
    have interval : low ≤ (embedding.event index).val ∧
        (embedding.event index).val < low + block.length := by
      rw [rank]
      dsimp only [index]
      omega
    have phaseMember : embedding.event index ∈ phase.events := (phase.mem_events _).mpr (by
      simpa only [phaseLow, phaseHigh] using interval)
    have earlier : (embedding.event index).val < selected.val := by
      rw [rank]
      dsimp only [index]
      omega
    obtain ⟨candidate, owned, accepted, _read⟩ := phase_ready_earlier_binding_read
      implementation.runtime implementation.leaks implementation.bounds implementation.plan inputs
        implementation.horizon implementation.scheduler counted
          (serviceGraph_revealRelaxedOrdered setup .concurrent) phase installed owner selected
            payload binding request.2.2.1 request.2.2.2.2 (embedding.event index) domain shape
              phaseMember earlier
    have stamped := phaseLiveBindingStamp_history implementation.runtime implementation.leaks
      implementation.plan inputs implementation.horizon implementation.scheduler
        ((nativeMenu).toRawTrace initialLaw implementation.horizon implementation.scheduler counted)
    rcases stamped (embedding.event index) candidate accepted with old |
        ⟨message, output, _sender, call, attemptMatch⟩
    · have lower : control.execution.application.attempt.phase = low :=
        congrArg CommitAttemptId.phase address
      rw [lower] at old
      omega
    · rw [owned] at output
      obtain ⟨record, recorded, emitted, decoded⟩ := emissionAction (embedding.event index)
        domain shape candidate message output attemptMatch call interval
      obtain ⟨serial, opening, evidence, actual, slot, actualMember, actualSent, declared,
          _fresh, _result⟩ := retained (embedding.event index) domain shape candidate message
            output attemptMatch call interval
      have same := recorded_emission_unique setup implementation trace owner actual record
        actualMember recorded message actualSent emitted
      subst actual
      have atRecord := phase_recalled_emission_attempt implementation.runtime implementation.leaks
        nativeInitial implementation.horizon implementation.scheduler raw owner record recorded
          message emitted
      have offset : (embedding.event index).val - low = position := by
        rw [rank]
        dsimp only [index]
        omega
      apply phaseCommitRecallWord_mem setup.program .concurrent implementation.runtime
        implementation.leaks low selected.val control.execution.application.generation
          (control.execution.recall owner) record recorded
            (atRecord.symm.trans (attemptMatch.trans address))
              ⟨⟨.commitment (embedding.event index) (owner, .prepared serial), opening⟩, evidence⟩
                (by rw [declared]) (embedding.event index) (owner, .prepared serial) rfl
                  ⟨interval.1, earlier⟩ action
      exact decoded.trans (offset ▸ selectedAction)

/-- Keeping the completed coordinate of a conditioned split run gives the
conditioned unsplit source continuation. Both histories in the split run
start from the same original source entry. -/
theorem source_split_pair_completed_posterior
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (before after : Nat) (entry : setup.proposalRecoveryProtocol.History)
    (observed : setup.proposalRecoveryProtocol.History → Bool)
    (present : true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom profile
      (before + after) entry).map observed).support) :
    (fiberPosterior
      ((setup.proposalRecoveryModel.runBehavioralFrom profile before entry).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile after cut).map (Prod.mk cut))
      (observed ∘ Prod.snd) true).map Prod.snd =
      fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom profile
        (before + after) entry) observed true := by
  let pair := (setup.proposalRecoveryModel.runBehavioralFrom profile before entry).bind
    fun cut => (setup.proposalRecoveryModel.runBehavioralFrom profile after cut).map (Prod.mk cut)
  have completed : pair.map Prod.snd =
      setup.proposalRecoveryModel.runBehavioralFrom profile (before + after) entry := by
    dsimp only [pair]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp only [show (fun x : setup.proposalRecoveryProtocol.History => x) = id from rfl,
      PMF.map_id]
    exact (setup.proposalRecoveryModel.runBehavioralFrom_add profile before after entry).symm
  have paired : true ∈ (pair.map (observed ∘ Prod.snd)).support := by
    rw [← PMF.map_comp, completed]
    exact present
  change (fiberPosterior pair (observed ∘ Prod.snd) true).map Prod.snd = _
  rw [map_fiberPosterior_readout pair Prod.snd observed true paired, completed]

open Classical in
/-- The actual ordinary source cut and completion under the issued ledger,
and under the focal ledger alone, use the same original foreign-word kernel. -/
def ForeignPosteriorCutPair : Prop :=
  ∀ (operational : implementation.Operational)
    (_fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History)
    (supportedWord : SourceProgram.History Player L)
    (_canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (_positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target supportedWord ≠ 0)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (_information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (_admitted : bindingAdmissionBit setup implementation who event
      ⟨some control, trace⟩ tape = true)
    (value : L.Val payload),
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    let low := control.execution.application.attempt.phase
    let high := low + block.block.length
    let k := event.val - low
    let q0 := sourceUnflaggedStrategy setup values
    let pair := (setup.proposalRecoveryModel.runBehavioralFrom q0 k target).bind fun cut =>
      (setup.proposalRecoveryModel.runBehavioralFrom q0 (block.block.length - k) cut).map
        (Prod.mk cut)
    let completed := fun history : setup.proposalRecoveryProtocol.History =>
      history.state.bind fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point
    let observed := fun pair : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completed pair.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who
            (finished.view who) ∧
          block.block.wordAction who k (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action cleanSite.binding.symm)
                (PublicationResult.success value)) ∧
          ∀ owner, owner ≠ who → issuedLedger setup implementation block.block low
            control high owner (finished.view owner))
    let foreign := ordinaryForeignJoint setup values implementation operational who
      ⟨some control, trace⟩ target
    let ownObserved := fun pair : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completed pair.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who
            (finished.view who) ∧
          block.block.wordAction who k (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action cleanSite.binding.symm)
                (PublicationResult.success value)))
    true ∈ (pair.map observed).support ∧
      true ∈ (foreign.map Prod.snd).support ∧
      (fiberPosterior pair observed true =
        (fiberPosterior foreign Prod.snd true).bind fun word =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload target word.1 value) ∧
      true ∈ (pair.map ownObserved).support ∧
      fiberPosterior pair ownObserved true =
        (foreign.map Prod.fst).bind fun word =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload target word value

open Classical in
/-- The actual source pair also exposes its issued mass and individual
foreign-word atoms through the completed source history. -/
def ForeignPosteriorCutPairAtoms : Prop :=
  ∀ (operational : implementation.Operational)
    (_fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History)
    (supportedWord : SourceProgram.History Player L)
    (_canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (_positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target supportedWord ≠ 0)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (_information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (_admitted : bindingAdmissionBit setup implementation who event
      ⟨some control, trace⟩ tape = true)
    (value : L.Val payload),
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    let low := control.execution.application.attempt.phase
    let high := low + block.block.length
    let k := event.val - low
    let q0 := sourceUnflaggedStrategy setup values
    let pair := (setup.proposalRecoveryModel.runBehavioralFrom q0 k target).bind fun cut =>
      (setup.proposalRecoveryModel.runBehavioralFrom q0 (block.block.length - k) cut).map
        (Prod.mk cut)
    let completed := fun history : setup.proposalRecoveryProtocol.History =>
      history.state.bind fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point
    let observed := fun point : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completed point.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who
            (finished.view who) ∧
          block.block.wordAction who k (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action cleanSite.binding.symm)
                (PublicationResult.success value)) ∧
          ∀ owner, owner ≠ who → issuedLedger setup implementation block.block low
            control high owner (finished.view owner))
    let foreign := ordinaryForeignJoint setup values implementation operational who
      ⟨some control, trace⟩ target
    let ownObserved := fun point : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completed point.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who
            (finished.view who) ∧
          block.block.wordAction who k (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action cleanSite.binding.symm)
                (PublicationResult.success value)))
    true ∈ (pair.map observed).support ∧
      true ∈ (foreign.map Prod.snd).support ∧
      (fiberPosterior pair observed true =
        (fiberPosterior foreign Prod.snd true).bind fun word =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload target word.1 value) ∧
      true ∈ (pair.map ownObserved).support ∧
      fiberPosterior pair ownObserved true =
        (foreign.map Prod.fst).bind (fun word =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload target word value) ∧
      (pair.map observed) true =
        (pair.map ownObserved) true * (foreign.map Prod.snd) true ∧
      ∃ sourceRead : setup.proposalRecoveryProtocol.History →
          SourceProgram.History Player L,
        foreign.map Prod.fst = pair.map (fun point => sourceRead point.2) ∧
        (∀ word point, (word, true) ∈ foreign.support →
          (pair.map observed) true *
            ((fiberPosterior foreign Prod.snd true) (word, true) *
              (sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
                event payload target word value) point) =
              if observed point = true ∧ sourceRead point.2 = word then pair point else 0) ∧
        ∃ (phase : RuntimePhase (serviceGraph setup .concurrent))
          (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
            implementation.leaks implementation.plan control phase block.block block.suffix),
          target = (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) ∧
          (∀ point, cursor.lift point = checkpoint.residual.lift
            (cast (congrArg ProtocolState block.reconstruct) point)) ∧
          ∀ history ∈ (pair.map Prod.snd).support,
            ∃ (finished : SourceProgram.Config Player L block.context)
              (last : CommitRecoveryState setup.program)
              (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
              (attempt : block.block.Attempt cursor.source cursor.current.excluded finished
                last.excluded),
              history = ⟨some last, lastTrace⟩ ∧
              sourceRead history = (fun owner => if owner = who then [] else
                (attempt.withoutMisses ∅ cursor.source).history owner) ∧
              setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
                attempt.joints.reverse ++ setup.recoveryJointRecall
                  (setup.proposalRecoveryEraseTrace cursor.trace) ∧
              setup.proposalRecoveryJointRecall lastTrace = attempt.joints.reverse.map
                (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) ++
                  setup.proposalRecoveryJointRecall cursor.trace ∧
              last.point = cursor.lift (block.block.liftPoint block.suffix
                (ProtocolState.entry block.suffix finished)) ∧
              last.excluded = cursor.current.excluded ∧ cursor.offset = low

omit [Fintype Player] [L.ResultTypes] in
private theorem structural_owned_history_of_joints
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player)
    (first second : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (leftFinal rightFinal : SourceProgram.Config Player L Δ)
    (left : block.Attempt first excluded leftFinal excluded)
    (right : block.Attempt second excluded rightFinal excluded)
    (entryHistory : first.history who = second.history who)
    (same : left.joints.map (fun joint => joint who) =
      right.joints.map (fun joint => joint who)) :
    (left.withoutMisses ∅ first).history who =
      (right.withoutMisses ∅ second).history who := by
  have replay : ∀ {Α Β : SourceCtx Player L} {R S : Finset VarId}
      (segment : SourceProgram.CommitPrefix Α R Β S)
      (sourceFirst sourceSecond replacementFirst replacementSecond :
        SourceProgram.Config Player L Α) (saved : Finset Player)
      (finalFirst finalSecond : SourceProgram.Config Player L Β)
      (attemptFirst : segment.Attempt sourceFirst saved finalFirst saved)
      (attemptSecond : segment.Attempt sourceSecond saved finalSecond saved),
      replacementFirst.history who = replacementSecond.history who →
      attemptFirst.joints.map (fun joint => joint who) =
        attemptSecond.joints.map (fun joint => joint who) →
      (attemptFirst.withoutMisses ∅ replacementFirst).history who =
        (attemptSecond.withoutMisses ∅ replacementSecond).history who := by
    intro Α Β R S segment
    induction segment with
    | nil =>
      intro sourceFirst sourceSecond replacementFirst replacementSecond saved finalFirst
        finalSecond attemptFirst attemptSecond sameHistory _
      cases attemptFirst
      cases attemptSecond
      exact sameHistory
    | @commit Α R Β S name actor payload fresh guard rest ih =>
      intro sourceFirst sourceSecond replacementFirst replacementSecond saved finalFirst
        finalSecond attemptFirst attemptSecond sameHistory sameJoints
      cases attemptFirst with
      | active active result missed valid later =>
        have noMiss : missed = false := by
          cases missed with
          | false => rfl
          | true =>
            have added : actor ∈ excludeCommit saved actor true := by
              simp only [excludeCommit, ↓reduceIte, Finset.mem_insert, true_or]
            exact (active (later.excluded_subset added)).elim
        subst missed
        cases attemptSecond with
        | excluded inactive other => exact (active inactive).elim
        | active otherActive otherResult otherMissed otherValid other =>
          have noOtherMiss : otherMissed = false := by
            cases otherMissed with
            | false => rfl
            | true =>
              have added : actor ∈ excludeCommit saved actor true := by
                simp only [excludeCommit, ↓reduceIte, Finset.mem_insert, true_or]
              exact (otherActive (other.excluded_subset added)).elim
          subst otherMissed
          have heads := (List.cons.inj sameJoints).1
          have tails := (List.cons.inj sameJoints).2
          apply ih _ _ _ _ saved _ _ later other ?_ tails
          by_cases own : who = actor
          · subst who
            have resultEq : result = otherResult := by
              simpa only [SourceProgram.CommitPrefix.Attempt.joints, ↓reduceIte,
                Option.some.injEq, CommitRecoveryMove.mk.injEq, OwnAction.commit.injEq,
                heq_eq_eq, true_and, and_true] using heads
            simp only [commitSuccessor, Function.update_self, resultEq, sameHistory]
          · simpa only [commitSuccessor, Function.update_of_ne own] using sameHistory
      | excluded inactive later =>
        cases attemptSecond with
        | active active result missed valid other => exact (active inactive).elim
        | excluded otherInactive other =>
          have tails := (List.cons.inj sameJoints).2
          simp only [SourceProgram.CommitPrefix.Attempt.withoutMisses,
            Finset.notMem_empty, ↓reduceIte]
          apply ih _ _ _ _ saved _ _ later other ?_ tails
          by_cases own : who = actor
          · subst who
            simp only [commitSuccessor, Function.update_self, sameHistory]
          · simpa only [commitSuccessor, Function.update_of_ne own] using sameHistory
  exact replay block first second first second excluded leftFinal rightFinal left right
    entryHistory same

omit [Fintype Player] [L.ResultTypes] in
private theorem word_action_name_in_context
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player) (position : Nat)
    (view : DecisionView who Δ) (owner : Player) (name : VarId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload))
    (read : block.wordAction who position view = some (.commit owner name payload result)) :
    name ∈ Δ.map Prod.fst := by
  induction block generalizing position with
  | nil => cases read
  | @commit Γ O Δ P head actor domain fresh guard rest ih =>
    cases position with
    | zero =>
      simp only [SourceProgram.CommitPrefix.wordAction] at read
      split at read
      · have names : head = name := congrArg (fun action : OwnAction Player L =>
          match action with
          | .commit _ named _ _ => named
          | .reveal _ named _ => named) (Option.some.inj read)
        subst name
        have included : ((head, .commitment actor domain) :: Γ).map Prod.fst ⊆
            Δ.map Prod.fst := by
          let rec namesMono : ∀ {Θ : SourceCtx Player L} {R : Finset VarId}
              (segment : SourceProgram.CommitPrefix Θ R Δ P),
              Θ.map Prod.fst ⊆ Δ.map Prod.fst
            | _, _, .nil => fun _ member => member
            | _, _, .commit _ _ _ _ rest =>
              fun _ member => namesMono rest (List.mem_cons_of_mem _ member)
          exact namesMono rest
        exact included (List.mem_cons_self ..)
      · cases read
    | succ position => exact ih position view read

theorem foreign_posterior_cut_pair_atoms :
    ForeignPosteriorCutPairAtoms setup values implementation := by
  classical
  intro operational fullValues sourceProfile nativeProfile who control trace tape target
    supportedWord canonicalSupported positive past view information event payload cleanSite
    admitted value checkpoint block low high k q0 pair completed observed foreign ownObserved
  have active : control.actor = some who := by
    by_contra inactive
    have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simp only [ReactiveApplication.observe, inactive, ↓reduceIte] at observedInfo
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = some (past, view) at information
    rw [observedInfo] at information
    cases information
  have actualInfo : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observedInfo
  have actualViews := Option.some.inj (actualInfo.symm.trans information)
  have cleanSiteProof : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload := by
    obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj actualViews
    rw [pastEq, viewEq]
    exact cleanSite
  have nativeForeign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at positive
    dsimp only at positive
    have qualified := (mul_ne_zero_iff.mp positive).2
    split at qualified
    · rename_i good
      exact good.1
    · simp only [ne_eq, not_true_eq_false] at qualified
  obtain ⟨entry, current, targetTrace, targetEq, _targetGood, erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target supportedWord canonicalSupported positive
        event payload cleanSiteProof
  subst target
  have saved := cleanSiteProof.excluded_eq setup implementation control
    (checkpointSelection setup implementation operational trace).val entry.phase entry.installed
  have request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩ := by
    have initialEq : (setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
    have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace
    rw [← initialEq] at raw
    obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history implementation.runtime
      implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler raw
    exact (control.execution.application.requests_publicView invariant who _).mp
      cleanSiteProof.request
  have alive : who ∉ control.execution.application.entry.excluded := by
    rw [← saved]
    exact request.2.2.2.2
  obtain ⟨baseCursor, canonical, offset, _source, _refs, embedding, lift, views,
      _config, size⟩ :=
    selected_binding_cursor setup implementation operational who control trace event
      entry true
  let cursor := PhaseProposalOrdinarySourceCursor.of_erasedHistory setup .concurrent
    implementation.runtime implementation.leaks implementation.plan control entry.phase
      block.block block.suffix baseCursor current targetTrace
        ((congrArg setup.proposalRecoveryErasedHistory canonical).trans
          ((congrArg setup.proposalRecoveryErasedHistory entry.canonicalHistory).symm.trans erased))
  have cursorCurrent : cursor.current = current := rfl
  have cursorTrace : cursor.trace = targetTrace := rfl
  have cursorStart : (⟨some cursor.current, cursor.trace⟩ :
      setup.proposalRecoveryProtocol.History) = ⟨some current, targetTrace⟩ := rfl
  have cursorExcluded : current.excluded = control.execution.application.entry.excluded :=
    cursor.excluded.trans saved
  have phaseLow : entry.phase.low = low := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [low, PhaseRuntimeState.attempt, phases, List.head?_cons,
      Option.map_some, Option.getD_some]
  have phaseHigh : entry.phase.high = high := by
    have nonempty := entry.phase.nonempty
    have blockSize := size
    change block.block.length = entry.phase.high - entry.phase.low at blockSize
    have lowEq := phaseLow
    dsimp only [high]
    omega
  have inside : k < block.block.length := by
    have bounds := (entry.phase.mem_events event).mp entry.inside
    dsimp only [k]
    omega
  have blockPositive : 0 < block.block.length := by omega
  have rank : ∀ index, (cursor.embedding.event index).val = low + index.val := by
    intro index
    simpa only [cursor, PhaseProposalOrdinarySourceCursor.of_erasedHistory, offset] using
      baseCursor.compiled.rankEq index
  have footprint :
      (control.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          control.execution.application.current.native.publicView.sourceFailureFootprint.1
            control.execution.application.attempt.phase =
        control.execution.application.entry.excluded := by
    have controls := congrArg Prod.fst (cursor.controls blockPositive)
    exact controls.symm.trans cursorExcluded
  let profile := ordinaryBlockProfile setup .concurrent implementation.plan values block.block
    block.suffix cursor.embedding (fun owner view => cursor.views.view owner view)
      (control.execution.application.entry.excluded, control.execution.application.generation, low)
        control.execution.application.publicView
          (PhaseProposal.sourceArchive control.execution.network.inputs)
  let ordinary := setup.proposalRecoveryModel.runBehavioralFrom q0 block.block.length
    ⟨some current, targetTrace⟩
  let structural := block.block.prefixLaw block.suffix profile cursor.source
  obtain ⟨reconstruct, projected, related⟩ :=
    ordinary_source_structural_projection setup values implementation control trace entry.phase
      block.block block.suffix cursor
  have project : ordinary.map reconstruct = structural := by
    rw [cursorStart] at projected
    rw [footprint] at projected
    have generationEq : control.execution.application.attempt.generation =
        control.execution.application.generation := rfl
    simpa only [ordinary, q0, profile, structural, generationEq, low] using projected
  have pairComplete : pair.map Prod.snd = ordinary := by
    simp only [pair, PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp only [show (fun x : setup.proposalRecoveryProtocol.History => x) = id from rfl,
      PMF.map_id]
    rw [← setup.proposalRecoveryModel.runBehavioralFrom_add, Nat.add_sub_of_le inside.le]
  let ownTest := fun final : SourceProgram.Config Player L block.context => decide (
    issuedLedger setup implementation block.block low control high who (final.view who) ∧
      block.block.wordAction who k (final.view who) =
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action cleanSiteProof.binding.symm) (.success value)))
  let foreignTest := fun final : SourceProgram.Config Player L block.context =>
    decide (∀ owner, owner ≠ who → issuedLedger setup implementation block.block low
      control high owner (final.view owner))
  let ownGate := fun word : List (OwnAction Player L) => decide (∃ final ∈ structural.support,
    final.history who = word ∧ ownTest final = true)
  let foreignRead := fun final : SourceProgram.Config Player L block.context =>
    fun owner => if owner = who then [] else final.history owner
  let foreignGate := fun word : SourceProgram.History Player L =>
    decide (∃ final ∈ structural.support, foreignRead final = word ∧ foreignTest final = true)
  let read := fun history : setup.proposalRecoveryProtocol.History =>
    foreignRead (reconstruct history)
  let own := fun history : setup.proposalRecoveryProtocol.History =>
    ownGate ((reconstruct history).history who)
  let words := ordinary.map read
  let ownLaw := ordinary.map own
  have ownGateEq (final : SourceProgram.Config Player L block.context)
      (member : final ∈ structural.support) : ownGate (final.history who) = ownTest final := by
    apply Bool.eq_iff_iff.mpr
    simp only [ownGate, decide_eq_true_eq]
    constructor
    · rintro ⟨other, supported, same, good⟩
      have viewEq := block.block.prefixLaw_view_eq_of_history_eq block.suffix profile profile
        cursor.source cursor.source who rfl other final supported member same
      simpa only [ownTest, viewEq] using good
    · exact fun good => ⟨final, member, rfl, good⟩
  have foreignGateEq (final : SourceProgram.Config Player L block.context)
      (member : final ∈ structural.support) :
      foreignGate (foreignRead final) = foreignTest final := by
    apply Bool.eq_iff_iff.mpr
    simp only [foreignGate, decide_eq_true_eq]
    constructor
    · rintro ⟨other, supported, same, good⟩
      simp only [foreignTest, decide_eq_true_eq] at good ⊢
      intro owner different
      have historyEq : other.history owner = final.history owner := by
        simpa only [foreignRead, ite_eq_right different] using congrFun same owner
      have viewEq := block.block.prefixLaw_view_eq_of_history_eq block.suffix profile profile
        cursor.source cursor.source owner rfl other final supported member historyEq
      rw [← viewEq]
      exact good owner different
    · exact fun good => ⟨final, member, rfl, good⟩
  have reconstructedSupport (history : setup.proposalRecoveryProtocol.History)
      (member : history ∈ ordinary.support) : reconstruct history ∈ structural.support := by
    rw [← project]
    exact (PMF.mem_support_map_iff ..).mpr ⟨history, member, rfl⟩
  have actualTests (history : setup.proposalRecoveryProtocol.History)
      (member : history ∈ ordinary.support) :
      (match completed history with
      | none => false
      | some final => ownTest final) = own history ∧
      (match completed history with
      | none => false
      | some final => foreignTest final) = foreignGate (read history) := by
    obtain ⟨final, last, lastTrace, attempt, historyEq, _replay, point, excluded,
      _word, _labels, activeViews, _proper⟩ := related history member
    have pulled : completed history = some final := by
      rw [historyEq]
      change residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) last.point = some final
      have exactLift : (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) =
          (fun point => cursor.lift (block.block.liftPoint block.suffix point)) := by
        funext point
        exact (lift _).symm
      rw [exactLift]
      exact (residualEntry?_eq_some_iff
        (cursor.origin.compose (block.block.protocolSuffix block.suffix)) _ _).mpr point.symm
    have ledgerEq (owner : Player) :
        issuedLedger setup implementation block.block low control high owner (final.view owner) ↔
          issuedLedger setup implementation block.block low control high owner
            ((reconstruct history).view owner) := by
      by_cases inactive : owner ∈ control.execution.application.entry.excluded
      · have vacuous (word : DecisionView owner block.context) :
            issuedLedger setup implementation block.block low control high owner word := by
          intro named domain shape candidate message emitted attemptMatch call interval
          have inputRecall := (nativeApplication).history_inputRecall nativeInitial
            implementation.horizon implementation.scheduler
              ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                implementation.scheduler trace) owner
          have input : message ∈ control.execution.network.inputs := by
            rw [← inputRecall] at emitted
            exact (List.mem_filter.mp emitted).1
          exact (issued_binding_owner_active setup implementation control trace owner named
            domain shape candidate message input attemptMatch call inactive).elim
        exact iff_of_true (vacuous _) (vacuous _)
      · rw [activeViews owner (by rw [excluded, cursorCurrent, cursorExcluded]; exact inactive)]
    have ownView : final.view who = (reconstruct history).view who :=
      activeViews who (by rw [excluded, cursorCurrent, cursorExcluded]; exact alive)
    dsimp only [own, read]
    rw [pulled, ownGateEq _ (reconstructedSupport history member),
      foreignGateEq _ (reconstructedSupport history member)]
    constructor
    · exact decide_eq_decide.mpr (and_congr (ledgerEq who) (by rw [ownView]))
    · exact decide_eq_decide.mpr (forall_congr' fun owner =>
        imp_congr_right fun _ => ledgerEq owner)
  have pairOwn (point : setup.proposalRecoveryProtocol.History ×
      setup.proposalRecoveryProtocol.History) (member : point ∈ pair.support) :
      ownObserved point = own point.2 := by
    have reached : point.2 ∈ ordinary.support := by
      rw [← pairComplete]
      exact (PMF.mem_support_map_iff ..).mpr ⟨point, member, rfl⟩
    exact (actualTests point.2 reached).1
  have pairObserved (point : setup.proposalRecoveryProtocol.History ×
      setup.proposalRecoveryProtocol.History) (member : point ∈ pair.support) :
      observed point = (own point.2 && foreignGate (read point.2)) := by
    have reached : point.2 ∈ ordinary.support := by
      rw [← pairComplete]
      exact (PMF.mem_support_map_iff ..).mpr ⟨point, member, rfl⟩
    have tests := actualTests point.2 reached
    calc
      observed point = (match completed point.2 with
          | none => false
          | some final => ownTest final && foreignTest final) := by
        dsimp only [observed]
        split
        · rfl
        · rename_i final
          apply Bool.eq_iff_iff.mpr
          simp only [ownTest, foreignTest, Bool.and_eq_true, decide_eq_true_eq,
            and_assoc]
      _ = (own point.2 && foreignGate (read point.2)) := by
        rw [← tests.1, ← tests.2]
        cases completion : completed point.2 <;> rfl
  have foreignEq : foreign = words.map (fun word => (word, foreignGate word)) := by
    have selected := ordinaryForeignJoint_of_selected_cursor setup values implementation
      operational who control trace entry.phase cursor blockPositive embedding lift views
    rw [cursorStart] at selected
    have selected' : foreign = structural.map (fun final =>
        (foreignRead final, foreignTest final)) := by
      simpa only [foreign, structural, profile, foreignRead, foreignTest,
        low, high] using selected
    rw [selected']
    rw [← project, PMF.map_comp]
    change ordinary.map (fun history => (read history, foreignTest (reconstruct history))) = _
    rw [show words.map (fun word => (word, foreignGate word)) =
        ordinary.map (fun history => (read history, foreignGate (read history))) by
      simp only [words, PMF.map_comp, Function.comp_def]]
    exact map_congr_on_support ordinary (fun history member =>
      Prod.ext rfl (foreignGateEq _ (reconstructedSupport history member)).symm)
  have product : ordinary.map (fun history => (reconstruct history).history) =
      independentProduct (fun owner => ordinary.map
        (fun history => (reconstruct history).history owner)) := by
    have all := block.block.prefixLaw_histories_product block.suffix profile cursor.source
    calc
      ordinary.map (fun history => (reconstruct history).history) =
          (ordinary.map reconstruct).map (fun final => final.history) := by
            rw [PMF.map_comp]
            rfl
      _ = structural.map (fun final => final.history) := by rw [project]
      _ = independentProduct (fun owner => structural.map (fun final => final.history owner)) := all
      _ = independentProduct (fun owner => ordinary.map
          (fun history => (reconstruct history).history owner)) := by
            congr 1
            funext owner
            rw [← project, PMF.map_comp]
            rfl
  have independent : ordinary.map (fun history => (own history, read history)) =
      bindPairLaw ownLaw (fun _ => words) :=
    independent_observation_complement ordinary (fun history => (reconstruct history).history)
      who [] ownGate product
  obtain ⟨_ready, graphPresent, _graphLaw, _graphMass⟩ :=
    binding_value_frontier_posterior setup values implementation operational fullValues
      control trace who active event payload cleanSiteProof nativeForeign entry value
  obtain ⟨sourcePresent, _wordLaw, _supported⟩ := closed_entry_binding_word setup values
    implementation operational control trace who event payload cleanSiteProof.binding alive entry
      value
      current targetTrace erased graphPresent
  have lengthEq := (selected_binding_observation setup implementation operational
    control trace who event payload cleanSiteProof.binding entry value).1
  have present : true ∈ (ordinary.map (bindingCompletedObservation setup implementation checkpoint
      control who event payload cleanSiteProof.binding value)).support := by
    simpa only [ordinary, q0, ← lengthEq] using sourcePresent
  obtain ⟨positiveHistory, positiveMember, positiveObservation⟩ :=
    (PMF.mem_support_map_iff ..).mp present
  have positiveOwn : own positiveHistory = true := by
    have tests := (actualTests positiveHistory positiveMember).1
    unfold bindingCompletedObservation residualBindingObservation at positiveObservation
    cases parsed : positiveHistory.state.bind (fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point) with
    | none =>
      simp only [checkpoint, block, parsed] at positiveObservation
      cases positiveObservation
    | some final =>
      have good : (∀ owner, issuedLedger setup implementation block.block low control high
          owner (final.view owner)) ∧
            block.block.wordAction who k (final.view who) =
              decodeEventAction setup.program event
                (cast (congrArg EventField.Action cleanSiteProof.binding.symm)
                  (.success value)) := by
        simpa only [checkpoint, block, parsed, decide_eq_true_eq, low, high, k]
          using positiveObservation
      have completedFinal : completed positiveHistory = some final := by
        simpa only [completed] using parsed
      rw [completedFinal] at tests
      rw [← tests]
      exact decide_eq_true ⟨good.1 who, good.2⟩
  have ownPositive : true ∈ ownLaw.support :=
    (PMF.mem_support_map_iff ..).mpr ⟨positiveHistory, positiveMember, positiveOwn⟩
  have annotationSupport := annotatedPrefixWeight_support setup values implementation operational
    sourceProfile nativeProfile who ⟨some control, trace⟩ tape ⟨some current, targetTrace⟩
      supportedWord canonicalSupported positive
  have foreignPositive : true ∈ (words.map foreignGate).support := by
    have given : (supportedWord, true) ∈ foreign.support := annotationSupport.2.2
    have projected : true ∈ (foreign.map Prod.snd).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨(supportedWord, true), given, rfl⟩
    simpa only [foreignEq, PMF.map_comp, Function.comp_def] using projected
  have pairJoint : pair.map (fun point => (own point.2, read point.2)) =
      bindPairLaw ownLaw (fun _ => words) := by
    have mapped := congrArg (fun law => law.map (fun history => (own history, read history)))
      pairComplete
    simpa only [PMF.map_comp, Function.comp_def, independent] using mapped
  have conditional : ∀ word ∈ words.support,
      sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event payload
        ⟨some current, targetTrace⟩ word value =
      fiberPosterior pair (fun point => (own point.2, read point.2)) (true, word) := by
    intro word wordSupported
    have jointPresent : (true, word) ∈
        (ordinary.map (fun history => (own history, read history))).support := by
      rw [independent, PMF.mem_support_iff, bindPairLaw_apply]
      exact mul_ne_zero ((PMF.mem_support_iff ..).mp ownPositive)
        ((PMF.mem_support_iff ..).mp wordSupported)
    obtain ⟨reference, referenceSupported, referenceObservation⟩ :=
      (PMF.mem_support_map_iff ..).mp jointPresent
    have referenceOwn := (Prod.mk.inj referenceObservation).1
    have referenceForeign := (Prod.mk.inj referenceObservation).2
    let final := reconstruct reference
    have finalSupported : final ∈ structural.support :=
      reconstructedSupport reference referenceSupported
    have referenceGood : ownTest final = true := by
      rw [← ownGateEq final finalSupported]
      exact referenceOwn
    have retained : issuedLedger setup implementation block.block low control high who
        (final.view who) := (decide_eq_true_eq.mp referenceGood).1
    have selected : block.block.wordAction who k (final.view who) =
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action cleanSiteProof.binding.symm) (.success value)) :=
      (decide_eq_true_eq.mp referenceGood).2
    let completeWord : SourceProgram.History Player L := fun owner =>
      if owner ∈ current.excluded then [] else
        (List.range block.block.length).filterMap
          (fun position => block.block.wordAction owner position (final.view owner))
    let imposed : SourceProgram.History Player L := fun owner =>
      if owner ∈ current.excluded then [] else
        (List.range (if owner = who then k + 1 else block.block.length)).filterMap
          (fun position => block.block.wordAction owner position (final.view owner))
    let semantic := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)).take
        block.block.length).reverse
    have rows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        semantic history = (List.range block.block.length).map (fun position owner =>
          if owner ∈ current.excluded then none else
            CommitRecoveryMove.lift
              (block.block.wordAction owner position ((reconstruct history).view owner))) := by
      obtain ⟨finished, last, lastTrace, attempt, historyEq, _replay, _point, excluded,
        recalledRows, _labels, activeViews, _proper⟩ := related history member
      have actual : semantic history = attempt.joints := by
        rw [historyEq]
        dsimp only [semantic]
        rw [recalledRows, ← attempt.joints_length, ← List.length_reverse, List.take_left,
          List.reverse_reverse]
      rw [actual, commitAttempt_wordAction block.block block.suffix cursor.source
        current.excluded finished last.excluded attempt excluded]
      apply List.map_congr_left
      intro position _member
      funext owner
      split
      · rfl
      · rename_i activeOwner
        rw [activeViews owner (by rw [excluded]; exact activeOwner)]
    have enrichedRows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        ((setup.proposalRecoveryJointRecall history.trace).take block.block.length).reverse =
          (semantic history).map (fun row owner => (row owner).map
            ProposalRecoveryMove.ordinary) := by
      obtain ⟨finished, last, lastTrace, attempt, historyEq, _replay, _point, _excluded,
        recalledRows, labels, _activeViews, _proper⟩ := related history member
      have rawRows : semantic history = attempt.joints := by
        rw [historyEq]
        dsimp only [semantic]
        rw [recalledRows, ← attempt.joints_length, ← List.length_reverse,
          List.take_left, List.reverse_reverse]
      rw [rawRows]
      rw [historyEq, labels]
      rw [← attempt.joints_length]
      rw [← List.length_map (f := fun row owner => (row owner).map
        ProposalRecoveryMove.ordinary),
        ← List.length_reverse (as := attempt.joints.map (fun row owner =>
          (row owner).map ProposalRecoveryMove.ordinary)), List.map_reverse, List.take_left,
        List.reverse_reverse]
    have properRows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) : ∀ row ∈ semantic history,
        ∀ owner move, row owner = some move → move.missing = false ∧ ¬ move.action.IsFailure := by
      obtain ⟨finished, last, lastTrace, attempt, historyEq, _replay, _point, _excluded,
        recalledRows, _labels, _activeViews, proper⟩ := related history member
      have rawRows : semantic history = attempt.joints := by
        rw [historyEq]
        dsimp only [semantic]
        rw [recalledRows, ← attempt.joints_length, ← List.length_reverse,
          List.take_left, List.reverse_reverse]
      rw [rawRows]
      exact proper
    have readout (owner : Player) (action : OwnAction Player L)
        (member : action ∈ imposed owner) :
        ∃ position, block.block.wordAction owner position (final.view owner) = some action := by
      by_cases inactive : owner ∈ current.excluded
      · simp only [imposed, inactive, ↓reduceIte, List.not_mem_nil] at member
      · have listed : action ∈
            (List.range (if owner = who then k + 1 else block.block.length)).filterMap
            (fun position => block.block.wordAction owner position (final.view owner)) := by
          simpa only [imposed, inactive, ↓reduceIte] using member
        exact (List.mem_filterMap.mp listed).imp fun _ parts => parts.2
    have completeReadout (owner : Player) (action : OwnAction Player L)
        (member : action ∈ completeWord owner) :
        ∃ position, block.block.wordAction owner position (final.view owner) = some action := by
      by_cases inactive : owner ∈ current.excluded
      · simp only [completeWord, inactive, ↓reduceIte, List.not_mem_nil] at member
      · have listed : action ∈ (List.range block.block.length).filterMap
            (fun position => block.block.wordAction owner position (final.view owner)) := by
          simpa only [completeWord, inactive, ↓reduceIte] using member
        exact (List.mem_filterMap.mp listed).imp fun _ parts => parts.2
    have completeProper : ∀ owner action, action ∈ completeWord owner → ¬ action.IsFailure := by
      intro owner action member
      have activeOwner : owner ∉ current.excluded := by
        intro inactive
        simp only [completeWord, inactive, ↓reduceIte, List.not_mem_nil] at member
      obtain ⟨position, bounded, readAction⟩ := List.mem_filterMap.mp (by
        simpa only [completeWord, activeOwner, ↓reduceIte] using member)
      have rowMember : (fun player => if player ∈ current.excluded then none else
          CommitRecoveryMove.lift
            (block.block.wordAction player position (final.view player))) ∈ semantic reference := by
        rw [rows reference referenceSupported]
        exact List.mem_map.mpr ⟨position, bounded, rfl⟩
      exact (properRows reference referenceSupported _ rowMember owner ⟨action, false⟩
        (by simp only [activeOwner, ↓reduceIte, readAction, CommitRecoveryMove.lift,
          Option.map_some])).2
    have imposedSubset : ∀ owner, imposed owner ⊆ completeWord owner := by
      intro owner action member
      by_cases inactive : owner ∈ current.excluded
      · simp only [imposed, inactive, ↓reduceIte, List.not_mem_nil] at member
      · have listed : action ∈
            (List.range (if owner = who then k + 1 else block.block.length)).filterMap
              (fun position => block.block.wordAction owner position (final.view owner)) := by
          simpa only [imposed, inactive, ↓reduceIte] using member
        obtain ⟨position, bounded, readAction⟩ := List.mem_filterMap.mp listed
        simp only [completeWord, inactive, ↓reduceIte]
        refine List.mem_filterMap.mpr ⟨position, ?_, readAction⟩
        apply List.mem_range.mpr
        have bound := List.mem_range.mp bounded
        by_cases own : owner = who <;> simp only [own, ↓reduceIte] at bound <;> omega
    have imposedProper : ∀ owner action, action ∈ imposed owner → ¬ action.IsFailure :=
      fun owner action member => completeProper owner action (imposedSubset owner member)
    have sameForeign : ∀ owner, owner ≠ who → imposed owner = completeWord owner := by
      intro owner different
      simp only [imposed, completeWord, different, ↓reduceIte]
    obtain ⟨middleContext, middleNames, before, after, beforeLength, afterLength, split⟩ :=
      block.block.exists_split (k + 1) (by omega)
    let startOf (segment : SourceProgram.CommitPrefix checkpoint.residual.context
        checkpoint.residual.names block.context block.pending)
        (c : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
          implementation.leaks implementation.plan control entry.phase segment block.suffix) :
        setup.proposalRecoveryProtocol.History := ⟨some c.current, c.trace⟩
    have castStart {α : Type} {β : α → Type} (f : (x : α) → β x →
        setup.proposalRecoveryProtocol.History) {x y : α} (same : x = y) (value : β x) :
        f y (same ▸ value) = f x value := by
      cases same
      rfl
    let splitCursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control entry.phase (before.append after)
          block.suffix := split.symm ▸ cursor
    have splitStart : startOf (before.append after) splitCursor =
        startOf block.block cursor := by
      exact castStart startOf split.symm cursor
    have splitStartTarget : (⟨some splitCursor.current, splitCursor.trace⟩ :
        setup.proposalRecoveryProtocol.History) = ⟨some current, targetTrace⟩ := by
      exact splitStart.trans (by rfl)
    have referenceSupported' : reference ∈ (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) (before.length + after.length)
          ⟨some current, targetTrace⟩).support := by
      simpa only [ordinary, q0, beforeLength, show k + 1 + after.length = block.block.length by
        omega] using referenceSupported
    rw [setup.proposalRecoveryModel.runBehavioralFrom_add] at referenceSupported'
    obtain ⟨retainedPrefix, prefixSupported, suffixSupported⟩ :=
      (PMF.mem_support_bind_iff ..).mp referenceSupported'
    have prefixWords : ((semantic reference).take before.length =
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retainedPrefix.trace)).take
          before.length).reverse) ∧
        ((setup.proposalRecoveryJointRecall retainedPrefix.trace).take before.length).reverse =
          (((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retainedPrefix.trace)).take
            before.length).reverse).map
              (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) := by
      obtain ⟨lift', origin', point'⟩ :
          ∃ lifted : ProtocolState (before.prepend (after.prepend block.suffix)) →
              ProtocolState setup.program,
            ProtocolSuffix setup.program (before.prepend (after.prepend block.suffix)) lifted ∧
            current.point = lifted (ProtocolState.entry
              (before.prepend (after.prepend block.suffix)) cursor.source) := by
        rw [← before.prepend_append after block.suffix, split]
        exact ⟨cursor.lift, cursor.origin, cursor.point⟩
      obtain ⟨middle, middleState, middleTrace, firstAttempt, prefixEq, middlePoint,
        middleExcluded, middleEntry, _generation, firstWord, firstLabels, _proper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values before
          (after.prepend block.suffix) lift' origin' cursor.source current targetTrace point'
            (cursor.excluded.trans cursor.entryExcluded.symm) retainedPrefix prefixSupported
      obtain ⟨last, lastState, lastTrace, lastAttempt, referenceEq, _lastPoint,
        _lastExcluded, _lastEntry, _lastGeneration, lastWord, _lastLabels, _lastProper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values after block.suffix
          (fun state => lift' (before.liftPoint (after.prepend block.suffix) state))
          (origin'.compose (before.protocolSuffix (after.prepend block.suffix))) middle
          middleState middleTrace middlePoint (middleExcluded.trans middleEntry.symm)
          reference (by simpa only [sourceUnflaggedStrategy, prefixEq] using suffixSupported)
      have totalLength : (firstAttempt.joints ++ lastAttempt.joints).length =
          block.block.length := by
        rw [List.length_append, firstAttempt.joints_length, lastAttempt.joints_length]
        omega
      have joined : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
          (firstAttempt.joints ++ lastAttempt.joints).reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetTrace) := by
        rw [lastWord, firstWord, List.reverse_append, List.append_assoc]
      have firstRead : ((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace middleTrace)).take before.length).reverse =
            firstAttempt.joints := by
        rw [firstWord, ← firstAttempt.joints_length, ← List.length_reverse,
          List.take_left, List.reverse_reverse]
      refine ⟨?_, ?_⟩
      · rw [referenceEq, prefixEq, firstRead]
        dsimp only [semantic]
        rw [joined, ← totalLength, ← List.length_reverse, List.take_left,
          List.reverse_reverse, ← firstAttempt.joints_length, List.take_left]
      · rw [prefixEq, firstRead, firstLabels, ← firstAttempt.joints_length,
          ← List.length_reverse, ← List.length_map (f := fun row owner =>
            (row owner).map ProposalRecoveryMove.ordinary), List.take_left,
          List.map_reverse, List.reverse_reverse]
    have prefixWord := prefixWords.1
    have referenceCovered : ∀ row ∈ ((setup.proposalRecoveryJointRecall reference.trace).take
        (before.length + after.length)).reverse, ∀ owner move, row owner = some move →
          ∃ action ∈ completeWord owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩ := by
      intro row member owner move chosen
      have total : before.length + after.length = block.block.length := by omega
      rw [total, enrichedRows reference referenceSupported] at member
      obtain ⟨rawRow, rawMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨rawMove, rawChosen, rfl⟩ := Option.map_eq_some_iff.mp chosen
      have proper := properRows reference referenceSupported rawRow rawMember owner rawMove
        rawChosen
      rw [rows reference referenceSupported] at rawMember
      obtain ⟨position, bounded, rowEq⟩ := List.mem_map.mp rawMember
      have readAction := congrFun rowEq owner
      rw [← readAction] at rawChosen
      split at rawChosen
      · cases rawChosen
      · rename_i activeOwner
        refine ⟨rawMove.action, ?_, ?_⟩
        · simp only [completeWord, activeOwner, ↓reduceIte]
          exact List.mem_filterMap.mpr ⟨position, bounded, by
            have actionRead := congrArg (Option.map (fun move => move.action)) rawChosen
            simp only [CommitRecoveryMove.lift, Option.map_map, Function.comp_def,
              Option.map_some] at actionRead
            have identity : ∀ action : Option (OwnAction Player L),
                Option.map (fun x => x) action = action := by
              intro action
              cases action <;> rfl
            rw [identity] at actionRead
            simpa only [final] using actionRead⟩
        · rw [show rawMove = ⟨rawMove.action, false⟩ by
            cases rawMove; simp_all only]
    have targetCovered : ∀ row ∈
        ((setup.proposalRecoveryJointRecall retainedPrefix.trace).take before.length).reverse,
        ∀ owner move, row owner = some move →
          ∃ action ∈ imposed owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩ := by
      intro row member owner move chosen
      have semanticPrefix : ((setup.proposalRecoveryJointRecall retainedPrefix.trace).take
          before.length).reverse = ((semantic reference).take before.length).map
            (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) := by
        rw [prefixWord]
        exact prefixWords.2
      rw [semanticPrefix] at member
      obtain ⟨rawRow, rawMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨rawMove, rawChosen, rfl⟩ := Option.map_eq_some_iff.mp chosen
      have fullMember := List.mem_of_mem_take rawMember
      have proper := properRows reference referenceSupported rawRow fullMember owner rawMove
        rawChosen
      rw [rows reference referenceSupported, ← List.map_take] at rawMember
      obtain ⟨position, bounded, rowEq⟩ := List.mem_map.mp rawMember
      have rangeMember := List.mem_of_mem_take bounded
      have bound : position < before.length := by
        have bounded' : position < min before.length block.block.length := by
          simpa only [List.take_range, List.mem_range] using bounded
        omega
      have readAction := congrFun rowEq owner
      rw [← readAction] at rawChosen
      split at rawChosen
      · cases rawChosen
      · rename_i activeOwner
        refine ⟨rawMove.action, ?_, ?_⟩
        · simp only [imposed, activeOwner, ↓reduceIte]
          apply List.mem_filterMap.mpr
          refine ⟨position, List.mem_range.mpr (by split <;> omega), ?_⟩
          have actionRead := congrArg (Option.map (fun move => move.action)) rawChosen
          simp only [CommitRecoveryMove.lift, Option.map_map, Function.comp_def,
            Option.map_some] at actionRead
          have identity : ∀ action : Option (OwnAction Player L),
              Option.map (fun x => x) action = action := by
            intro action
            cases action <;> rfl
          rw [identity] at actionRead
          simpa only [final] using actionRead
        · rw [show rawMove = ⟨rawMove.action, false⟩ by
            cases rawMove; simp_all only]
    have pastImposed : ∀ action ∈ imposed who, ∃ owner name payload result,
        action = OwnAction.commit owner name payload result ∧ name ∈ middleContext.map Prod.fst
          := by
      intro action member
      have activeWho : who ∉ current.excluded := by rw [cursorExcluded]; exact alive
      simp only [imposed, activeWho, ↓reduceIte] at member
      obtain ⟨position, bounded, actionRead⟩ := List.mem_filterMap.mp member
      have positionBound : position < before.length := by
        simpa only [beforeLength] using List.mem_range.mp bounded
      rw [← split, before.wordAction_append_prefix after who position _ positionBound]
        at actionRead
      obtain ⟨owner, name, domain, result, actionEq⟩ :=
        word_action_commit before who position _ action actionRead
      refine ⟨owner, name, domain, result, actionEq, ?_⟩
      exact word_action_name_in_context before who position _ owner name domain result
        (actionEq ▸ actionRead)
    have forcedComplete := source_word_run_conditioned setup .concurrent implementation.runtime
      implementation.leaks implementation.plan values fullValues nativeInitial
        implementation.horizon implementation.scheduler control
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
          trace) entry.phase before after block.suffix splitCursor (by omega) imposed completeWord
        (fun owner => final.view owner) (by simpa only [split] using readout)
        (by simpa only [split] using completeReadout) imposedProper completeProper who sameForeign
        reference retainedPrefix (by
          simpa only [← splitStartTarget,
            ← setup.proposalRecoveryModel.runBehavioralFrom_add] using
            (PMF.mem_support_bind_iff ..).mpr ⟨retainedPrefix, prefixSupported, suffixSupported⟩)
        referenceCovered (by simpa only [← splitStartTarget] using prefixSupported)
          targetCovered pastImposed
    have foreignRows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        read history = word ↔ ∀ owner, owner ≠ who →
          (semantic history).map (fun row => row owner) =
            (semantic reference).map (fun row => row owner) := by
      rw [← referenceForeign]
      constructor
      · intro same owner different
        have historyEq : (reconstruct history).history owner = final.history owner := by
          simpa only [read, foreignRead, different, ↓reduceIte] using congrFun same owner
        have viewEq := block.block.prefixLaw_view_eq_of_history_eq block.suffix profile profile
          cursor.source cursor.source owner rfl _ _ (reconstructedSupport history member)
            finalSupported historyEq
        rw [rows history member, rows reference referenceSupported]
        simp only [List.map_map, Function.comp_def, viewEq, final]
      · intro same
        funext owner
        by_cases ownOwner : owner = who
        · simp only [read, foreignRead, ownOwner, ↓reduceIte]
        · obtain ⟨firstConfig, firstState, firstTrace, firstAttempt, firstEq, firstReplay,
            _firstPoint, firstExcluded, firstRecall, _firstLabels, _firstViews, _firstProper⟩ :=
            related history member
          obtain ⟨secondConfig, secondState, secondTrace, secondAttempt, secondEq, secondReplay,
            _secondPoint, secondExcluded, secondRecall, _secondLabels, _secondViews,
            _secondProper⟩ := related reference referenceSupported
          have firstRead : semantic history = firstAttempt.joints := by
            dsimp only [semantic]
            rw [firstEq, firstRecall, ← firstAttempt.joints_length,
              ← List.length_reverse, List.take_left, List.reverse_reverse]
          have secondRead : semantic reference = secondAttempt.joints := by
            dsimp only [semantic]
            rw [secondEq, secondRecall, ← secondAttempt.joints_length,
              ← List.length_reverse, List.take_left, List.reverse_reverse]
          have castJoints {config : SourceProgram.Config Player L block.context}
              {first last : Finset Player} (equal : first = last)
              (attempt : block.block.Attempt cursor.source cursor.current.excluded config first) :
              (equal ▸ attempt).joints = attempt.joints := by
            cases equal
            rfl
          have castWithout {config : SourceProgram.Config Player L block.context}
              {first last : Finset Player} (equal : first = last)
              (attempt : block.block.Attempt cursor.source cursor.current.excluded config first) :
              (equal ▸ attempt).withoutMisses ∅ cursor.source =
                attempt.withoutMisses ∅ cursor.source := by
            cases equal
            rfl
          let firstTyped := firstExcluded ▸ firstAttempt
          let secondTyped := secondExcluded ▸ secondAttempt
          have owned := structural_owned_history_of_joints block.block owner cursor.source
            cursor.source current.excluded firstConfig secondConfig firstTyped secondTyped rfl
              (by simpa only [firstTyped, secondTyped, castJoints firstExcluded firstAttempt,
                  castJoints secondExcluded secondAttempt, firstRead, secondRead]
                using same owner ownOwner)
          simpa only [read, foreignRead, ownOwner, ↓reduceIte, firstReplay, secondReplay,
            firstTyped, secondTyped, castWithout firstExcluded firstAttempt,
            castWithout secondExcluded secondAttempt]
            using owned
    have prefixFiber (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        own history = true ∧ read history = word ↔
          (∀ owner, owner ≠ who → (semantic history).map (fun row => row owner) =
            (semantic reference).map (fun row => row owner)) ∧
          (semantic history).take before.length = (semantic reference).take before.length := by
      have ledger := issuedLedger_iff_prefix_at_request setup implementation block.block
        block.suffix cursor.embedding low rank cursor.views.actionEq trace entry.phase
          entry.installed phaseLow phaseHigh who event payload cleanSiteProof.binding request
            (by have bounds := (entry.phase.mem_events event).mp entry.inside; omega)
            cleanSiteProof.unsent (final.view who) ((reconstruct history).view who) retained
      dsimp only [own]
      rw [ownGateEq _ (reconstructedSupport history member)]
      simp only [ownTest, high, decide_eq_true_eq, ledger, foreignRows history member]
      have rowBound (h : setup.proposalRecoveryProtocol.History)
          (supported : h ∈ ordinary.support) (position : Nat)
          (bound : position < block.block.length) : position < (semantic h).length := by
        rw [rows h supported]
        simpa only [List.length_map, List.length_range] using bound
      have rowEq (position : Nat) (bound : position < block.block.length) (owner : Player) :
          ((semantic history)[position]'(rowBound history member position bound)) owner =
            if owner ∈ current.excluded then none else CommitRecoveryMove.lift
              (block.block.wordAction owner position ((reconstruct history).view owner)) := by
        have indexed := congrArg
          (fun entries : List (Player → Option (CommitRecoveryMove Player L)) =>
          entries[position]?) (rows history member)
        have rangeBound : position < (List.range block.block.length).length := by
          simpa only [List.length_range] using bound
        have selected := Option.some.inj (by
          simpa only [List.getElem?_eq_getElem (rowBound history member position bound),
            List.getElem?_map, List.getElem?_eq_getElem rangeBound, Option.map_some,
            List.getElem_range, Option.some.injEq] using indexed)
        exact congrFun selected owner
      have referenceRow (position : Nat) (bound : position < block.block.length) (owner : Player) :
          ((semantic reference)[position]'
            (rowBound reference referenceSupported position bound)) owner =
            if owner ∈ current.excluded then none else CommitRecoveryMove.lift
              (block.block.wordAction owner position (final.view owner)) := by
        have indexed := congrArg
          (fun entries : List (Player → Option (CommitRecoveryMove Player L)) =>
          entries[position]?) (rows reference referenceSupported)
        have rangeBound : position < (List.range block.block.length).length := by
          simpa only [List.length_range] using bound
        have selected := Option.some.inj (by
          simpa only [List.getElem?_eq_getElem
            (rowBound reference referenceSupported position bound),
            List.getElem?_map, List.getElem?_eq_getElem rangeBound, Option.map_some,
            List.getElem_range, Option.some.injEq] using indexed)
        simpa only [final] using congrFun selected owner
      have activeWho : who ∉ current.excluded := by rw [cursorExcluded]; exact alive
      have liftInjective : Function.Injective
          (CommitRecoveryMove.lift : Option (OwnAction Player L) →
            Option (CommitRecoveryMove Player L)) := by
        intro first second same
        cases first with
        | none =>
          cases second with
          | none => rfl
          | some _ => simp only [CommitRecoveryMove.lift, Option.map_none,
              Option.map_some, reduceCtorEq] at same
        | some first =>
          cases second with
          | none => simp only [CommitRecoveryMove.lift, Option.map_none,
              Option.map_some, reduceCtorEq] at same
          | some second =>
            have equal : first = second := by
              simpa only [CommitRecoveryMove.lift, Option.map_some,
                Option.some.injEq, CommitRecoveryMove.mk.injEq, and_true] using same
            cases equal
            rfl
      constructor
      · rintro ⟨⟨earlier, chosen⟩, others⟩
        refine ⟨others, ?_⟩
        apply List.ext_getElem
        · rw [List.length_take, List.length_take, rows history member,
            rows reference referenceSupported]
          simp
        · intro position firstBound secondBound
          have bound : position < before.length := by
            exact lt_of_lt_of_le firstBound (List.length_take_le ..)
          have wholeBound : position < block.block.length := by omega
          funext owner
          rw [List.getElem_take, List.getElem_take, rowEq position wholeBound owner,
            referenceRow position wholeBound owner]
          by_cases ownOwner : owner = who
          · subst owner
            simp only [activeWho, ↓reduceIte]
            congr 1
            by_cases past : position < k
            · exact earlier position past
            · have currentPosition : position = k := by omega
              simpa only [currentPosition, selected] using chosen
          · have mapped := congrArg (fun items => items[position]?) (others owner ownOwner)
            simpa only [rows history member, rows reference referenceSupported,
              List.getElem?_map, List.getElem?_range, wholeBound, ↓reduceIte,
              Option.map_some, Option.some.injEq] using mapped
      · rintro ⟨others, prefixEq⟩
        have ownRows (position : Nat) (bound : position < before.length) :
            block.block.wordAction who position ((reconstruct history).view who) =
              block.block.wordAction who position (final.view who) := by
          have wholeBound : position < block.block.length := by omega
          have selectedRow := congrArg (fun items => (items[position]?).map
            (fun row => row who)) prefixEq
          apply liftInjective
          simpa only [rows history member, rows reference referenceSupported,
            List.getElem?_take, bound, ↓reduceIte, List.getElem?_map, List.getElem?_range,
            wholeBound, Option.map_some, Option.some.injEq, activeWho, ↓reduceIte]
            using selectedRow
        exact ⟨⟨fun position bound => ownRows position (by omega),
          (ownRows k (by omega)).trans selected⟩, others⟩
    let foreignObserved := fun history : setup.proposalRecoveryProtocol.History =>
      decide (∀ owner, owner ≠ who → (semantic history).map (fun row => row owner) =
        (semantic reference).map (fun row => row owner))
    let prefixObserved := fun history : setup.proposalRecoveryProtocol.History =>
      (semantic history).take before.length
    let jointObserved := fun history : setup.proposalRecoveryProtocol.History =>
      decide (own history = true ∧ read history = word)
    have foreignPresent : true ∈ (ordinary.map foreignObserved).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨reference, referenceSupported, by
        exact decide_eq_true (by intro owner _; rfl)⟩
    have referenceConditioned : reference ∈
        (fiberPosterior ordinary foreignObserved true).support := by
      rw [fiberPosterior_support _ _ _ foreignPresent]
      exact ⟨by exact decide_eq_true (by intro owner _; rfl),
        referenceSupported⟩
    have prefixPresent : prefixObserved reference ∈
        ((fiberPosterior ordinary foreignObserved true).map prefixObserved).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨reference, referenceConditioned, rfl⟩
    have total : before.length + after.length = block.block.length := by omega
    have completedConditional :
        setup.proposalRecoveryModel.runBehavioralFrom (sourceBlockWordStrategy setup values imposed)
          block.block.length ⟨some current, targetTrace⟩ =
          fiberPosterior ordinary (fun history => (own history, read history)) (true, word) := by
      have nested : setup.proposalRecoveryModel.runBehavioralFrom
          (sourceBlockWordStrategy setup values imposed) block.block.length
            ⟨some current, targetTrace⟩ =
          fiberPosterior (fiberPosterior ordinary foreignObserved true) prefixObserved
            (prefixObserved reference) := by
        rw [splitStartTarget] at forcedComplete
        simpa only [total, ordinary, q0, semantic, foreignObserved, prefixObserved,
          prefixWord] using forcedComplete
      have appended := posterior_append_observation ordinary foreignObserved jointObserved
        prefixObserved (prefixObserved reference) (fiberPosterior ordinary foreignObserved true)
          _ foreignPresent rfl prefixPresent nested (by
            intro history member
            simpa only [jointObserved, foreignObserved, prefixObserved, decide_eq_true_eq]
              using prefixFiber history member)
      rw [appended.2]
      exact fiberPosterior_eq_of_support_fiber ordinary jointObserved
        (fun history => (own history, read history)) true (true, word) (by
          intro history _
          simp only [jointObserved, decide_eq_true_eq, Prod.mk.injEq])
    have forcedWord : sourceForcedBlockJoint setup values implementation who
        ⟨some control, trace⟩ event payload ⟨some current, targetTrace⟩ word value =
        (setup.proposalRecoveryModel.runBehavioralFrom
          (sourceBlockWordStrategy setup values imposed) k ⟨some current, targetTrace⟩).bind
            (fun cut => (setup.proposalRecoveryModel.runBehavioralFrom
              (sourceBlockWordStrategy setup values imposed) (sourceCommitFuel setup cut) cut).map
                (Prod.mk cut)) := by
      let chosen := decodeEventAction setup.program event
        (cast (congrArg EventField.Action cleanSiteProof.binding.symm) (.success value))
      let prior := phaseCommitRecallWord setup.program .concurrent implementation.runtime
        implementation.leaks low event.val control.execution.application.generation
          (control.execution.recall who)
      let listed : SourceProgram.History Player L := fun owner => if owner = who then
        prior ++ chosen.toList else (word owner).drop
          ((ProtocolState.history setup.program current.point owner).length)
      have listMembership : ∀ owner action,
          action ∈ (if owner ∈ current.excluded then [] else listed owner) ↔
            action ∈ imposed owner := by
        intro owner action
        by_cases inactive : owner ∈ current.excluded
        · simp only [inactive, imposed, ↓reduceIte]
        · by_cases ownOwner : owner = who
          · subst owner
            have recalledActions := issued_ledger_recall_actions setup implementation block.block
              block.suffix cursor.embedding low rank cursor.views.actionEq control trace
                entry.phase entry.installed phaseLow phaseHigh who event payload
                  cleanSiteProof.binding
                  request (by have bounds := (entry.phase.mem_events event).mp entry.inside; omega)
                  (final.view who) retained action
            simp only [inactive, listed, prior, chosen, imposed, ↓reduceIte,
              List.mem_append, Option.mem_toList, recalledActions, ← selected]
            constructor
            · rintro (⟨position, bound, actionRead⟩ | actionRead)
              · exact List.mem_filterMap.mpr ⟨position, List.mem_range.mpr (by omega), actionRead⟩
              · exact List.mem_filterMap.mpr ⟨k, List.mem_range.mpr (by omega), actionRead⟩
            · rintro member
              obtain ⟨position, bounded, actionRead⟩ := List.mem_filterMap.mp member
              have bound := List.mem_range.mp bounded
              by_cases earlier : position < k
              · exact Or.inl ⟨position, earlier, actionRead⟩
              · have same : position = k := by omega
                exact Or.inr (same ▸ actionRead)
          · have fullWord : word owner = final.history owner := by
              have same := congrFun referenceForeign owner
              simpa only [read, foreignRead, ownOwner, ↓reduceIte] using same.symm
            have entryWord : ProtocolState.history setup.program current.point owner =
                cursor.source.history owner := rfl
            simp only [inactive, listed, imposed, ownOwner, ↓reduceIte, fullWord, entryWord]
            rw [ordinaryBlockWord_drop block.block block.suffix profile cursor.source owner
              final finalSupported]
      have strategies : sourceBlockWordStrategy setup values
          (fun owner => if owner ∈ current.excluded then [] else listed owner) =
          sourceBlockWordStrategy setup values imposed := by
        funext owner information
        unfold sourceBlockWordStrategy
        simp only [listMembership]
      have sourceRank : instructionCount setup.program -
          ProtocolState.remaining setup.program current.point = low := by
        rw [← cursorCurrent]
        rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
        have programCount := cursor.compiled.countEq
        simp only [eventCount_eq_instructionCount] at programCount
        have start : cursor.offset = low := offset
        omega
      simp only [sourceForcedBlockJoint, cleanSiteProof.binding, ↓reduceDIte]
      change ((setup.proposalRecoveryModel.runBehavioralFrom
          (sourceBlockWordStrategy setup values listed) (event.val -
            (instructionCount setup.program - ProtocolState.remaining setup.program current.point))
          ⟨some current, targetTrace⟩).bind fun cut =>
            (setup.proposalRecoveryModel.runBehavioralFrom (sourceBlockWordStrategy setup values
              listed) (sourceCommitFuel setup cut) cut).map (Prod.mk cut)) = _
      rw [sourceRank, source_word_cut_mask_excluded setup values listed current.excluded
        ⟨some current, targetTrace⟩ k (by exact Finset.Subset.refl _), strategies]
    obtain ⟨cutContext, cutNames, cutBefore, cutAfter, cutLength, restLength, cutSplit⟩ :=
      block.block.exists_split k inside.le
    let cutCursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control entry.phase (cutBefore.append cutAfter)
          block.suffix := cutSplit.symm ▸ cursor
    have cutStart : (⟨some cutCursor.current, cutCursor.trace⟩ :
        setup.proposalRecoveryProtocol.History) = ⟨some current, targetTrace⟩ := by
      exact (castStart startOf cutSplit.symm cursor).trans cursorStart
    have cutTraceLength : cutCursor.trace.length = targetTrace.length :=
      congrArg (fun history : setup.proposalRecoveryProtocol.History => history.trace.length)
        cutStart
    have forcedGeometry := source_word_pair_fuel setup values implementation control
      entry.phase cutBefore cutAfter block.suffix block.boundary cutCursor imposed
        (fun owner => final.view owner) (by simpa only [cutSplit] using readout) imposedProper
    have ordinaryGeometry := ordinary_source_pair_geometry setup values implementation
      control entry.phase cutBefore cutAfter block.suffix cutCursor
    rw [cutStart] at forcedGeometry ordinaryGeometry
    have cutRest : cutAfter.length = block.block.length - k := by omega
    rw [cutLength, cutRest] at forcedGeometry ordinaryGeometry
    have forcedCompletion : (sourceForcedBlockJoint setup values implementation who
        ⟨some control, trace⟩ event payload ⟨some current, targetTrace⟩ word value).map Prod.snd =
        fiberPosterior ordinary (fun history => (own history, read history)) (true, word) := by
      rw [forcedWord]
      have fuelEq := forcedGeometry.1
      rw [fuelEq]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      simp only [show (fun x : setup.proposalRecoveryProtocol.History => x) = id from rfl,
        PMF.map_id]
      rw [← setup.proposalRecoveryModel.runBehavioralFrom_add,
        Nat.add_sub_of_le inside.le]
      exact completedConditional
    have pairPresent : (true, word) ∈
        (pair.map (fun point => (own point.2, read point.2))).support := by
      rw [← pairComplete, PMF.map_comp, Function.comp_def] at jointPresent
      exact jointPresent
    have posteriorCompletion :
        (fiberPosterior pair (fun point => (own point.2, read point.2)) (true, word)).map Prod.snd =
          fiberPosterior ordinary (fun history => (own history, read history)) (true, word) := by
      have mapped := map_fiberPosterior_readout pair Prod.snd
        (fun history => (own history, read history)) (true, word) pairPresent
      simpa only [pairComplete, Function.comp_def] using mapped
    apply source_pair_eq_of_completed setup _ _ (targetTrace.length + k)
    · intro point member
      rw [forcedWord] at member
      simpa only [cutLength] using (forcedGeometry.2 point member).1
    · intro point member
      have original := (mem_support_fiberPosterior pairPresent member).2
      simpa only [cutLength, cutRest]
        using (ordinaryGeometry point original).1
    · intro point member
      rw [forcedWord] at member
      simpa only [cutLength, cutTraceLength] using (forcedGeometry.2 point member).2
    · intro point member
      have original := (mem_support_fiberPosterior pairPresent member).2
      simpa only [cutLength, cutRest, cutTraceLength]
        using (ordinaryGeometry point original).2
    · exact forcedCompletion.trans posteriorCompletion.symm
  have result := fiberPosteriors_of_independent_restriction pair words ownLaw
    (fun point => read point.2) (fun point => own point.2) foreignGate
      (fun word => sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
        event payload ⟨some current, targetTrace⟩ word value) ownPositive foreignPositive
          pairJoint conditional
  have observedMap : pair.map observed =
      pair.map (fun point => own point.2 && foreignGate (read point.2)) :=
    map_congr_on_support pair pairObserved
  have ownMap : pair.map ownObserved = pair.map (fun point => own point.2) :=
    map_congr_on_support pair pairOwn
  have observedPosterior := fiberPosterior_eq_of_support_fiber pair observed
    (fun point => own point.2 && foreignGate (read point.2)) true true
      (fun point member => by rw [pairObserved point member])
  have ownPosterior := fiberPosterior_eq_of_support_fiber pair ownObserved
    (fun point => own point.2) true true (fun point member => by rw [pairOwn point member])
  have wordsEq : foreign.map Prod.fst = words := by
    rw [foreignEq, PMF.map_comp]
    exact PMF.map_id _
  have ownMarginal : pair.map (fun point => own point.2) = ownLaw := by
    have mapped := congrArg (PMF.map Prod.fst) pairJoint
    simpa only [PMF.map_comp, Function.comp_def, bindPairLaw_map_fst] using mapped
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [observedMap]
    exact result.1
  · simpa only [foreignEq] using result.2.1
  · rw [observedPosterior, foreignEq]
    exact result.2.2.1
  · rw [ownMap]
    exact result.2.2.2.1
  · rw [ownPosterior, wordsEq]
    exact result.2.2.2.2.1
  · rw [observedMap, ownMap, ownMarginal, foreignEq]
    simpa only [PMF.map_comp, Function.comp_def] using result.2.2.2.2.2.1
  · refine ⟨read, ?_, ?_, ?_⟩
    · calc
        foreign.map Prod.fst = words := wordsEq
        _ = ordinary.map read := rfl
        _ = (pair.map Prod.snd).map read := by rw [pairComplete]
        _ = pair.map (fun point => read point.2) := by
          rw [PMF.map_comp]
          rfl
    · intro word point issued
      have admitted : foreignGate word = true := by
        rw [foreignEq] at issued
        obtain ⟨original, _, same⟩ := (PMF.mem_support_map_iff ..).mp issued
        have wordEq := congrArg Prod.fst same
        have bitEq := congrArg Prod.snd same
        simp only at wordEq bitEq
        subst original
        exact bitEq
      have posteriorWord : (fiberPosterior foreign Prod.snd true) (word, true) =
          fiberPosterior words foreignGate true word := by
        have mapped := map_fiberPosterior_readout words
          (fun selected => (selected, foreignGate selected)) Prod.snd true foreignPositive
        have mapped' : (fiberPosterior words foreignGate true).map
          (fun selected => (selected, foreignGate selected)) =
            fiberPosterior foreign Prod.snd true := by
          simpa only [Function.comp_def, foreignEq] using mapped
        rw [← mapped', PMF.map_apply, tsum_eq_single word]
        · simp [admitted]
        · intro other different
          simp [Ne.symm different]
      have observedMass : (pair.map observed) true =
          (pair.map ownObserved) true * (foreign.map Prod.snd) true := by
        rw [observedMap, ownMap, ownMarginal, foreignEq]
        simpa only [PMF.map_comp, Function.comp_def] using result.2.2.2.2.2.1
      rw [observedMass, posteriorWord, ownMap, ownMarginal]
      have foreignMass : (foreign.map Prod.snd) true =
          (words.map foreignGate) true := by
        rw [foreignEq, PMF.map_comp]
        rfl
      rw [foreignMass]
      have atom := result.2.2.2.2.2.2 word point admitted
      by_cases reached : point ∈ pair.support
      · by_cases same : read point.2 = word
        · have gate : foreignGate (read point.2) = true := by rw [same]; exact admitted
          by_cases ownBit : own point.2 = true
          · simpa [pairObserved point reached, ownBit, same, gate, admitted] using atom
          · simpa [pairObserved point reached, ownBit, same, gate, admitted] using atom
        · simp only [same, and_false, ite_false] at atom ⊢
          exact atom
      · have zero : pair point = 0 := (PMF.apply_eq_zero_iff _ _).mpr reached
        simpa only [zero, ite_self] using atom
    · refine ⟨entry.phase, cursor, cursorStart.symm, ?_, ?_⟩
      · intro point
        exact lift point
      · intro history member
        rw [pairComplete] at member
        obtain ⟨finished, last, lastTrace, attempt, historyEq, replay, point, excluded,
            word, labels, _views, _proper⟩ := related history member
        refine ⟨finished, last, lastTrace, attempt, historyEq, ?_, word, labels, point, excluded,
          offset⟩
        simp only [read, foreignRead, replay]

/-- The actual ordinary source continuation has both binding posterior laws. -/
theorem foreign_posterior_cut_pair :
    ForeignPosteriorCutPair setup values implementation := by
  intro operational fullValues sourceProfile nativeProfile who control trace tape target
    supportedWord canonicalSupported positive past view information event payload cleanSite
    admitted value checkpoint block low high k q0 pair completed observed foreign ownObserved
  have result := foreign_posterior_cut_pair_atoms setup values implementation operational
    fullValues sourceProfile nativeProfile who control trace tape target supportedWord
      canonicalSupported positive past view information event payload cleanSite admitted value
  exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1,
    result.2.2.2.2.1⟩

end ForeignPosterior

end Vegas.PhaseProposalQualifiedBinding

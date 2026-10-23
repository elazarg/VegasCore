/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.SourceImage
import Vegas.Game.AsyncDeviationForeign
import Vegas.Source.CommitRecoveryAttemptOrigin

/-! # Foreign callback queries on the literal replay chronology -/

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

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

omit [Fintype Player] in
private theorem sourceReplay_proposalWord_observer
    (left right : Player) {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.proposalRecoveryProposalWord left
        (setup.proposalRecoveryModel.infoOf left trace) =
      setup.proposalRecoveryProposalWord right
        (setup.proposalRecoveryModel.infoOf right trace) := by
  induction trace with
  | start => rfl
  | extend prior joint legal moved ih =>
      rw [setup.proposalRecoveryProposalWord_extend,
        setup.proposalRecoveryProposalWord_extend, ih]

omit [Fintype Player] in
private theorem sourceReplay_archive_observer
    (left right : Player) {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.proposalRecoveryArchive left (setup.proposalRecoveryModel.infoOf left trace) =
      setup.proposalRecoveryArchive right (setup.proposalRecoveryModel.infoOf right trace) := by
  unfold Setup.proposalRecoveryArchive
  rw [sourceReplay_proposalWord_observer setup left right trace]

omit [Fintype Player] in
private theorem sourceReplay_selected_entry
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (selected : RecoverySourceCheckpoint setup .concurrent state)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (live saved : SourceProgram.Config Player L selected.residual.context)
    (livePoint : current.point = selected.residual.lift
      (ProtocolState.entry selected.residual.tail live))
    (savedPoint : current.saved = selected.residual.lift
      (ProtocolState.entry selected.residual.tail saved))
    (committing : ProtocolState.atCommit setup.program current.point = true) :
    live = saved ∧ current.saved = current.point ∧ current.entryExcluded = current.excluded := by
  have rank : ProtocolState.remaining setup.program current.point =
      ProtocolState.remaining setup.program current.saved := by
    rw [livePoint, savedPoint, selected.remaining, selected.remaining,
      ProtocolState.remaining_entry, ProtocolState.remaining_entry]
  have actual := source_commit_entry_eq_atPoint setup current trace committing rank
  have savedEq : current.saved = current.point := congrArg CommitRecoveryState.saved actual
  have excludedEq : current.entryExcluded = current.excluded :=
    congrArg CommitRecoveryState.entryExcluded actual
  have points : selected.residual.lift (ProtocolState.entry selected.residual.tail live) =
      selected.residual.lift (ProtocolState.entry selected.residual.tail saved) := by
    rw [← livePoint, ← savedPoint, savedEq]
  exact ⟨ProtocolState.entry_injective selected.residual.tail
    (sourceReplaySuffixInjective setup selected.origin points), savedEq, excludedEq⟩

omit [Fintype Player] in
private theorem sourceReplay_visible_prefix_decode
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (views : ProtocolViewSuffix setup.program (block.prepend suffix) refs embedding lift)
    (config : (serviceGraph setup .concurrent).Config)
    (before : SourceProgram.Config Player L Δ) (owner : Player)
    (agreement : ∀ {name cell} (source : HasVar Δ name cell), cellVisibleTo owner cell →
      ((commitBlockRefs setup.program block suffix embedding refs).get source).get?
          config.store = some (cellValue (before.state.get source)))
    (selected : Fin (eventCount (block.prepend suffix)))
    (atEnd : selected.val = block.length) :
    decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref owner (embedding.event selected)
        ((serviceGraph setup .concurrent).playerStore owner config.store) [] =
      some (ProtocolView.eraseHistory owner setup.program
        (ProtocolState.observe owner setup.program
          (lift (block.liftPoint suffix (ProtocolState.entry suffix before))))) := by
  have decoded := decodeObservation?_eq_some_of_visible
    (commitBlockRefs setup.program block suffix embedding refs) owner before.state
      config.store agreement
  have masked : decodeObservation? owner
      (commitBlockRefs setup.program block suffix embedding refs)
      ((toEventGraph setup.program).playerStore owner config.store) =
        some (sourceObserve owner before.state) :=
    (decodeObservation?_playerStore (graph := toEventGraph setup.program) owner
      (commitBlockRefs setup.program block suffix embedding refs) config.store).trans decoded
  have localView := decodeEventView?_commitPrefix_entry setup.program block suffix embedding
    refs ((toEventGraph setup.program).playerStore owner config.store) before owner selected atEnd
      masked
  have wholeView := (views.decode owner selected
    ((toEventGraph setup.program).playerStore owner config.store) (before.history owner)).trans
      ((congrArg (Option.map (views.view owner)) localView).trans
        (congrArg some (views.observe owner
          (block.liftPoint suffix (ProtocolState.entry suffix before)))).symm)
  change decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref owner (embedding.event selected)
      ((toEventGraph setup.program).playerStore owner config.store) [] = _
  rw [decodeEventView?_eraseHistory (past := before.history owner), wholeView, Option.map_some]

private theorem sourceReplay_foreign_virtual_view
    (operational : implementation.Operational)
    (focal owner : Player) (foreign : owner ≠ focal)
    (execution : (nativeApplication).Execution)
    (event : (serviceGraph setup .concurrent).EventId)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (survives : owner ∉ current.excluded)
    (good : setup.proposalRecoveryForeignGood focal ⟨some current, trace⟩)
    (decoded : decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref owner event
      ((serviceGraph setup .concurrent).playerStore owner
        execution.application.current.native.config.store) [] =
        some (ProtocolView.eraseHistory owner setup.program
          (ProtocolState.observe owner setup.program current.point))) :
    phaseVirtualSourceView? setup .concurrent implementation.runtime implementation.leaks
        owner event (execution.observe nativeApplication owner) =
      some (ProtocolView.eraseHistory owner setup.program
        (ProtocolState.observe owner setup.program current.point)) := by
  have ordinary := setup.proposalRecovery_bindingsHoldValues_of_surviving_no_generated
    operational.wellFormed current trace owner survives (good owner foreign)
  unfold phaseVirtualSourceView?
  have ownerView : (execution.observe nativeApplication owner).application.1.who = owner := rfl
  rw [dite_eq_left ownerView]
  change (decodeEventView? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref owner event
    ((serviceGraph setup .concurrent).playerStore owner
      execution.application.current.native.config.store) []).map _ = _
  rw [decoded, Option.map_some, ProtocolView.virtualBindings_eraseHistory,
    ProtocolState.virtualBindings_observe_eq owner (setup.context.map Prod.fst).toFinset
      setup.program current.point ordinary]

private theorem sourceReplay_signed_binding_read
    (reference before : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix prior referenceTrace)
    (target : setup.proposalRecoveryProtocol.History)
    (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent)) (value : L.Val payload)
    (accepted : before.execution.application.current.native.accepted (.inr event) = some handle)
    (lower : before.execution.application.attempt.phase ≤ event.val)
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, value⟩ : Raw L)) :
    sourceBindingAt setup before.execution.application.attempt event owner payload binding
      target.trace = some value := by
  classical
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have counted : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before) := by
    rw [← initialEq]
    exact prior
  have stamp := phaseLiveBindingStamp_history implementation.runtime implementation.leaks
    implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      implementation.scheduler
        ((nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler counted)
  rcases stamp event handle accepted with earlier |
      ⟨message, output, _sender, call, attempt⟩
  · omega
  · obtain ⟨record, recorded, emitted⟩ := List.mem_filterMap.mp output
    have rawRetained : TracePrefix
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler prior)
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler referenceTrace) := by
      have convert : ∀ {leftState rightState}
          {left : (nativeProtocol).Trace leftState}
          {right : (nativeProtocol).Trace rightState}, TracePrefix left right →
          TracePrefix
            ((nativeMenu).toRawTrace nativeInitial implementation.horizon
              implementation.scheduler left)
            ((nativeMenu).toRawTrace nativeInitial implementation.horizon
              implementation.scheduler right) := by
        intro leftState rightState left right kept
        induction kept with
        | refl => exact .refl
        | extend earlier joint legal moved ih => exact .extend ih _ _ _
      exact convert retained
    have retainedRecall := (nativeApplication).reaches_recall_prefix nativeInitial
      implementation.horizon implementation.scheduler rawRetained.reachesWithin
        before reference rfl rfl handle.1
    have present : record ∈ reference.execution.recall handle.1 := retainedRecall.subset recorded
    have signed := sourceHandleMeaning_of_emission setup implementation target reference
      referenceTrace handle record present message emitted event call owner payload binding
        (sourceBindingAt setup message.payload.attempt event owner payload binding target.trace) rfl
    rw [meaning, attempt] at signed
    cases read : sourceBindingAt setup before.execution.application.attempt event owner
        payload binding target.trace with
    | none => simp only [read, Option.map_none] at signed; cases signed
    | some actual =>
        rw [read, Option.map_some] at signed
        have same : actual = value := eq_of_heq (Raw.mk.inj (Option.some.inj signed)).2.symm
        exact congrArg some same

private theorem sourceReplay_archive_before
    (before reference : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some reference))
    (retained : TracePrefix prior trace) :
    (PhaseProposal.sourceArchive reference.execution.network.inputs).filter
        (fun proposal => proposal.address.phase < before.execution.application.attempt.phase) =
      (PhaseProposal.sourceArchive before.execution.network.inputs).filter
        (fun proposal => proposal.address.phase < before.execution.application.attempt.phase) := by
  classical
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state supported
    have initialEq : nativeInitial =
        (setup.initialLaw.map encodeInputs).map
          (PhaseRuntimeState.initial implementation.plan) := by
      simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
    rw [initialEq] at supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered implementation.plan draw
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler prior)
  have restrict (first second : Finset (ProposalRecoveryProposal L)) (low high : Nat)
      (lower : low ≤ high)
      (same : first.filter (fun proposal => proposal.address.phase < high) =
        second.filter (fun proposal => proposal.address.phase < high)) :
      first.filter (fun proposal => proposal.address.phase < low) =
        second.filter (fun proposal => proposal.address.phase < low) := by
    apply Finset.ext
    intro proposal
    have highEq := Finset.ext_iff.mp same proposal
    simp only [Finset.mem_filter] at highEq ⊢
    constructor
    · rintro ⟨present, bounded⟩
      exact ⟨(highEq.mp ⟨present, by omega⟩).1, bounded⟩
    · rintro ⟨present, bounded⟩
      exact ⟨(highEq.mpr ⟨present, by omega⟩).1, bounded⟩
  have frame (current next : (nativeApplication).Control)
      (joint : Player → Option (nativeApplication).Action)
      (moved : some next ∈ ((nativeApplication).transition nativeInitial
        implementation.horizon implementation.scheduler (some current) joint).support) :
      (PhaseProposal.sourceArchive next.execution.network.inputs).filter
          (fun proposal => proposal.address.phase < current.execution.application.attempt.phase) =
        (PhaseProposal.sourceArchive current.execution.network.inputs).filter
          (fun proposal => proposal.address.phase < current.execution.application.attempt.phase)
            := by
    rcases current with ⟨remaining, actor, execution⟩
    cases actor with
    | some owner =>
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact PhaseProposal.sourceArchive_respond_before implementation.runtime
          implementation.leaks execution owner ((joint owner).getD ⟨none⟩)
    | none =>
        cases remaining with
        | zero =>
            cases (PMF.mem_support_pure_iff _ _).mp moved
            rfl
        | succ remaining =>
            obtain ⟨command, _selected, realized⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
            obtain ⟨native, stepped, equal⟩ := PMF.support_map .. ▸ realized
            cases Option.some.inj equal
            rw [PhaseProposal.sourceArchive_environmentStep implementation.runtime
              implementation.leaks execution native command stepped]
  have along : ∀ {state} {earlier : (nativeProtocol).Trace state},
      TracePrefix prior earlier → ∃ current : (nativeApplication).Control,
        state = some current ∧
        (PhaseProposal.sourceArchive current.execution.network.inputs).filter
            (fun proposal => proposal.address.phase < before.execution.application.attempt.phase) =
          (PhaseProposal.sourceArchive before.execution.network.inputs).filter
            (fun proposal => proposal.address.phase < before.execution.application.attempt.phase)
              := by
    intro state earlier kept
    induction kept with
    | refl => exact ⟨before, rfl, rfl⟩
    | @extend source target middle kept joint legal moved ih =>
        obtain ⟨current, rfl, previous⟩ := ih
        have realized : target ∈ ((nativeApplication).transition nativeInitial
            implementation.horizon implementation.scheduler (some current) joint).support := moved
        obtain ⟨next, rfl, _recall⟩ := (nativeApplication).transition_recall_prefix nativeInitial
          implementation.horizon implementation.scheduler current target joint realized
        have progress := phase_attempt_progress_of_prefix implementation.runtime
          implementation.leaks
          nativeMenu nativeInitial initialized implementation.horizon implementation.scheduler
            before current prior middle kept ordered
        exact ⟨next, rfl,
          (restrict _ _ _ _ progress.2.1 (frame current next joint realized)).trans previous⟩
  obtain ⟨current, same, result⟩ := along retained
  cases Option.some.inj same
  exact result

private theorem sourceReplay_selected_archive
    (operational : implementation.Operational)
    (before reference : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some reference))
    (retained : TracePrefix prior trace)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : before.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (owner : Player) (active : owner ∉ before.execution.application.current.excluded) :
    let selected := (checkpointSelection setup implementation operational prior).val.checkpoint
    setup.proposalRecoveryArchive owner (setup.proposalRecoveryModel.infoOf owner
        (setup.proposalRecoveryLiftTrace (nativeArchiveLabels setup
          (PhaseProposal.sourceArchive reference.execution.network.inputs)) selected.trace)) =
      PhaseProposal.sourceArchive before.execution.network.inputs := by
  classical
  let witness := (checkpointSelection setup implementation operational prior).val
  let selected := witness.checkpoint
  let current := CommitRecoveryState.atPoint
    (selected.residual.lift (ProtocolState.entry selected.residual.tail selected.source))
      before.execution.application.entry.excluded before.execution.application.generation
  have sourceActive : owner ∉ current.excluded := by
    intro member
    exact active (witness.order.coverage.inherited member)
  have phaseRank : instructionCount setup.program -
      ProtocolState.remaining setup.program current.point =
        before.execution.application.attempt.phase := selected.saved_position
  have filtered := sourceReplay_archive_before setup implementation before reference prior trace
    retained
  have lifted := setup.proposalRecoveryLiftTrace_eq_of_withheld_labels
    (nativeArchiveLabels setup (PhaseProposal.sourceArchive reference.execution.network.inputs))
    (nativeArchiveLabels setup (PhaseProposal.sourceArchive before.execution.network.inputs))
      selected.trace (by
        intro state after earlier joint legal moved kept author move chosen revealing
        cases state with
        | none =>
            have offered := legal.2 author
            rw [chosen] at offered
            exact False.elim offered.1
        | some state =>
            have offered := legal.2 author
            rw [chosen] at offered
            obtain ⟨revealOwner, name, action⟩ := revealing
            have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal author
              setup.program state.point move offered.2 ⟨revealOwner, name, false, action⟩
            have earlierRank := setup.proposalRecovery_noncommit_prefix_rank_lt owner state current
              earlier selected.trace joint legal moved kept notCommit sourceActive
            apply nativeArchiveLabels_eq_of_earlier setup _ _
              before.execution.application.attempt.phase filtered _ author state rfl
            exact earlierRank.2.trans_eq phaseRank)
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have counted : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before) := by
    rw [← initialEq]
    exact prior
  have full := RecoverySourceCheckpoint.ArchivedProposals.binding implementation.runtime
    implementation.leaks implementation.bounds implementation.plan (setup.initialLaw.map
      encodeInputs)
      implementation.horizon implementation.scheduler before counted selected
        (checkpointSelection setup implementation operational prior).property
          phase installed commitment owner active
  change setup.proposalRecoveryArchive owner
      (setup.proposalRecoveryModel.infoOf owner
        (setup.proposalRecoveryLiftTrace _ selected.trace)) = _
  rw [lifted]
  exact full

omit [Fintype Player] in
private theorem sourceReplay_unclosed_commit_head
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (entry : SourceProgram.Config Player L Γ)
    (start : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some start))
    (final : setup.proposalRecoveryProtocol.History)
    (point : start.point = lift (.inl entry))
    (saved : ProtocolState.atCommit setup.program start.saved = true)
    (unfinished : ProtocolState.commitEnd setup.program start.saved < instructionCount tail)
    (choice : PublicationResult (L.Val payload)) (missed : Bool)
    (missing : missed = true → choice = .failure)
    (retained : TracePrefix prior final.trace)
    (word : List (Player → Option (CommitRecoveryMove Player L)))
    (instructions : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      (start.commitJoint owner name payload choice missed :: word).reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior)) :
    let nextConfig := if owner ∈ start.excluded then automaticCommit name owner payload entry
      else commitSuccessor name guard entry choice
    let nextExcluded := if owner ∈ start.excluded then start.excluded
      else excludeCommit start.excluded owner missed
    ∃ (next : CommitRecoveryState setup.program)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some start) joint)
      (moved : some next ∈
        (setup.proposalRecoveryProtocol.step (some start) ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal moved) final.trace ∧
      next.point = lift (.inr (ProtocolState.entry tail nextConfig)) ∧
      next.excluded = nextExcluded ∧ next.saved = start.saved ∧
      next.generation = start.generation ∧
      Setup.proposalRecoveryJoint joint = start.commitJoint owner name payload choice missed := by
  classical
  intro nextConfig nextExcluded
  have committing : ProtocolState.atCommit setup.program start.point = true := by
    rw [point, origin.atCommit_lift]
    rfl
  have positionWithin : instructionCount setup.program -
      ProtocolState.remaining setup.program start.point < instructionCount setup.program -
        ProtocolState.commitEnd setup.program start.saved := by
    have bounded := ProtocolState.remaining_le_instructionCount setup.program start.point
    rw [point, origin.remaining_lift] at bounded ⊢
    change instructionCount tail + 1 ≤ instructionCount setup.program at bounded
    change instructionCount setup.program - (instructionCount tail + 1) < _
    omega
  obtain ⟨next, joint, legal, moved, kept, semantic, _rank⟩ := sourceReplayHeadRow setup
    start prior committing final retained (start.commitJoint owner name payload choice missed ::
      word)
      instructions (by simp only [List.length_cons]; omega) _ rfl positionWithin
  have semantic : Setup.proposalRecoveryJoint joint =
      start.commitJoint owner name payload choice missed := by
    simpa only [List.getElem_cons_zero] using semantic
  obtain ⟨monotone, _generatedLegal, generated⟩ := lifted_commit_successor setup.program
    (setup.initialConfig setup.initialLaw.support_nonempty.choose) guard tail lift
      origin.remaining_lift origin.actor_lift (fun point who => origin.recoveryAvailable who point)
        origin.recoveryStep_lift entry start point choice missed missing
  let installed := start.install (lift (.inr (ProtocolState.entry tail nextConfig)), nextExcluded)
    monotone
  have generated : installed.close ∈
      (start.step (start.commitJoint owner name payload choice missed)).support := generated
  have remains : ProtocolState.commitEnd setup.program installed.saved <
      ProtocolState.remaining setup.program installed.point := by
    change ProtocolState.commitEnd setup.program start.saved <
      ProtocolState.remaining setup.program (lift (.inr (ProtocolState.entry tail nextConfig)))
    rw [origin.remaining_lift]
    simpa only [ProtocolState.remaining, Sum.elim_inr, ProtocolState.remaining_entry]
      using unfinished
  have noClose := installed.close_eq_self_of_remaining_gt saved remains
  rw [noClose] at generated
  have actual : next ∈ (start.step (start.commitJoint owner name payload choice missed)).support
    := by
    change some next ∈ ((start.step (Setup.proposalRecoveryJoint joint)).map some).support at moved
    obtain ⟨result, support, same⟩ := (PMF.mem_support_map_iff ..).mp moved
    cases Option.some.inj same
    simpa only [semantic] using support
  have equal := start.step_unique_of_commit committing
    (start.commitJoint owner name payload choice missed) next installed actual generated
  refine ⟨next, joint, legal, moved, kept, ?_, ?_, ?_, ?_, semantic⟩ <;>
    rw [equal] <;> rfl

omit [Fintype Player] in
private theorem sourceReplay_attempt_survives_prefix
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {block : SourceProgram.CommitPrefix Γ O Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (native : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
      (start : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some start))
      (final : setup.proposalRecoveryProtocol.History)
      (_point : start.point = lift (ProtocolState.entry (block.prepend suffix) entry))
      (_mask : start.excluded = excluded)
      (_saved : ProtocolState.atCommit setup.program start.saved = true)
      (_endpoint : ProtocolState.commitEnd setup.program start.saved ≤ instructionCount suffix)
      (_retained : TracePrefix prior final.trace)
      (_word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
        attempt.joints.reverse ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace
          prior))
      (observer : Player) (_active : observer ∉ excluded) (count : Nat)
      (_inside : count < block.length)
      (_accepted : ∀ (index : Fin (eventCount (block.prepend suffix))), index.val < count →
        ∀ payload, (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
          .binding observer payload → native.accepted (.inr (embedding.event index)) ≠ none)
      (_reads : sourceAttemptTableReads setup attempt suffix embedding native),
      ∃ (current : CommitRecoveryState setup.program)
        (trace : setup.proposalRecoveryProtocol.Trace (some current)),
        TracePrefix trace final.trace ∧ trace.length = prior.length + count ∧
          observer ∉ current.excluded := by
  induction attempt with
  | nil =>
      intro suffix embedding native lift origin start prior final point mask saved endpoint
        retained word observer active count inside accepted reads
      simp only [SourceProgram.CommitPrefix.length] at inside
      omega
  | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      acting choice missed missing later ih =>
      intro suffix embedding native lift origin start prior final point mask saved endpoint
        retained word observer active count inside accepted reads
      cases count with
      | zero => exact ⟨start, prior, retained, by omega, by simpa only [mask] using active⟩
      | succ count =>
          obtain ⟨_choice, missedEq, _stored, tailReads⟩ := reads
          let zero : Fin (eventCount
              ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
            ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
          have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event zero) =
              .binding owner payload := by
            change outputLayout setup.program (embedding.event zero) = _
            simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
              Fin.cases_zero] using embedding.layout_eq zero
          have nextActive : observer ∉ excludeCommit excluded owner missed := by
            by_cases same : owner = observer
            · subst owner
              have present := accepted zero (by simp only [zero]; omega) payload shape
              have notMissing : missed = false := by
                cases selected : native.accepted (.inr (embedding.event zero)) with
                | none => exact False.elim (present selected)
                | some handle =>
                    simpa only [zero, selected, Option.isNone_some] using missedEq.symm
              simpa only [excludeCommit, notMissing, Bool.false_eq_true, ↓reduceIte] using active
            · cases missed with
              | false => simpa only [excludeCommit, Bool.false_eq_true, ↓reduceIte] using active
              | true =>
                  intro member
                  rcases Finset.mem_insert.mp member with equal | old
                  · exact same equal.symm
                  · exact active old
          have nonfinal : 0 < rest.length := by
            simp only [SourceProgram.CommitPrefix.length] at inside
            omega
          obtain ⟨next, joint, legal, moved, kept, nextPoint, nextMask, nextSaved,
            _nextGeneration, semantic⟩ := sourceReplayActiveHeadStep setup acting choice missed
              missing later suffix lift origin start prior final point mask saved endpoint
                retained word nonfinal
          have tailWord := sourceReplayTailWord setup final start prior next joint legal moved
            _ later.joints semantic word
          obtain ⟨current, trace, keptPrefix, length, survives⟩ := ih suffix
            (embedding.tail (rest.prepend suffix) (by
              simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
            native (fun point => lift (.inr point))
            (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin) next
            (prior.extend joint legal moved) final nextPoint nextMask
            (by rw [nextSaved]; exact saved) (by rw [nextSaved]; exact endpoint)
            kept tailWord observer nextActive count (by
              simp only [SourceProgram.CommitPrefix.length] at inside; omega)
            (by
              intro index earlier ty shape
              exact accepted index.succ (by simp only [Fin.val_succ]; omega) ty shape) tailReads
          exact ⟨current, trace, keptPrefix, by simp only [Trace.length] at length; omega,
            survives⟩
  | @excluded Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      inactive later ih =>
      intro suffix embedding native lift origin start prior final point mask saved endpoint
        retained word observer active count inside accepted reads
      cases count with
      | zero => exact ⟨start, prior, retained, by omega, by simpa only [mask] using active⟩
      | succ count =>
          have nonfinal : 0 < rest.length := by
            simp only [SourceProgram.CommitPrefix.length] at inside
            omega
          obtain ⟨next, joint, legal, moved, kept, nextPoint, nextMask, nextSaved,
            _nextGeneration, semantic⟩ := sourceReplayExcludedHeadStep setup inactive later
              suffix lift origin start prior final point mask saved endpoint retained word nonfinal
          have tailWord := sourceReplayTailWord setup final start prior next joint legal moved
            _ later.joints semantic word
          obtain ⟨current, trace, keptPrefix, length, survives⟩ := ih suffix
            (embedding.tail (rest.prepend suffix) (by
              simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
            native (fun point => lift (.inr point))
            (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin) next
            (prior.extend joint legal moved) final nextPoint nextMask
            (by rw [nextSaved]; exact saved) (by rw [nextSaved]; exact endpoint)
            kept tailWord observer active count (by
              simp only [SourceProgram.CommitPrefix.length] at inside; omega)
            (by
              intro index earlier ty shape
              exact accepted index.succ (by simp only [Fin.val_succ]; omega) ty shape) reads.2
          exact ⟨current, trace, keptPrefix, by simp only [Trace.length] at length; omega,
            survives⟩

omit [Fintype Player] in
private theorem sourceReplay_attempt_visible_agreement
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {block : SourceProgram.CommitPrefix Γ O Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
      (_views : ProtocolViewSuffix setup.program (block.prepend suffix) refs embedding lift)
      (store : Store (graphLayout setup.program))
      (start finalCurrent : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some start))
      (finalTrace : setup.proposalRecoveryProtocol.Trace (some finalCurrent))
      (target : setup.proposalRecoveryProtocol.History)
      (_toTarget : TracePrefix finalTrace target.trace)
      (_point : start.point = lift (ProtocolState.entry (block.prepend suffix) entry))
      (_mask : start.excluded = excluded)
      (_saved : ProtocolState.atCommit setup.program start.saved = true)
      (_endpoint : ProtocolState.commitEnd setup.program start.saved < instructionCount suffix)
      (_retained : TracePrefix prior finalTrace)
      (_word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace finalTrace) =
        attempt.joints.reverse ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace
          prior))
      (attemptId : CommitAttemptId) (_generation : start.generation = attemptId.generation)
      (_savedRank : instructionCount setup.program -
        ProtocolState.remaining setup.program start.saved = attemptId.phase)
      (low : Nat) (_ranking : ∀ index, (embedding.event index).val = low + index.val)
      (_clock : low + instructionCount (block.prepend suffix) = instructionCount setup.program)
      (focal observer : Player) (_foreign : observer ≠ focal)
      (_survives : observer ∉ finalCurrent.excluded)
      (_good : setup.proposalRecoveryForeignGood focal ⟨some finalCurrent, finalTrace⟩)
      (_agrees : ∀ {name cell} (source : HasVar Γ name cell), cellVisibleTo observer cell →
        (refs.get source).get? store = some (cellValue (entry.state.get source)))
      (_read : ∀ (index : Fin (eventCount (block.prepend suffix))), index.val < block.length →
        ∀ payload (binding : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
          .binding observer payload) (value : L.Val payload),
          sourceBindingAt setup attemptId (embedding.event index) observer payload binding
            target.trace =
            some value →
          (⟨.inr (embedding.event index), binding⟩ : FieldRef (graphLayout setup.program)
            (.binding observer payload)).get? store = some (.success value)),
      ∀ {name cell} (source : HasVar Δ name cell), cellVisibleTo observer cell →
        ((commitBlockRefs setup.program block suffix embedding refs).get source).get? store =
          some (cellValue (finished.state.get source)) := by
  induction attempt with
  | nil =>
      intro suffix embedding refs lift origin views store start finalCurrent prior finalTrace target
        toTarget point mask saved endpoint retained word attemptId generation savedRank low ranking
        clock focal observer foreign survives good agrees read
      exact agrees
  | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      active choice missed missing later ih =>
      intro suffix embedding refs lift origin views store start finalCurrent prior finalTrace target
        toTarget point mask saved endpoint retained word attemptId generation savedRank low ranking
        clock focal observer foreign survives good agrees read
      let zero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let named := embedding.event zero
      have shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload :=
        by
        change outputLayout setup.program named = _
        simpa only [named, zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.layout_eq zero
      let head : FieldRef (graphLayout setup.program) (.binding owner payload) := ⟨.inr named,
        shape⟩
      have unfinished : ProtocolState.commitEnd setup.program start.saved <
          instructionCount (rest.prepend suffix) := by
        rw [rest.instructionCount_prepend]
        omega
      have activeStart : owner ∉ start.excluded := by rwa [mask]
      have jointEq : start.commitJoint owner name payload choice missed = fun player =>
          if player = owner then some ⟨OwnAction.commit owner name payload choice, missed⟩
            else none := by
        funext player
        change (if player = owner ∧ owner ∉ start.excluded then _ else _) = _
        simp only [activeStart, not_false_eq_true, and_true]
      have headWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace finalTrace) =
          (start.commitJoint owner name payload choice missed :: later.joints).reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior) := by
        rw [jointEq]
        exact word
      obtain ⟨next, joint, legal, moved, kept, nextPoint, nextMask, nextSaved, nextGeneration,
        semantic⟩ := sourceReplay_unclosed_commit_head setup fresh guard (rest.prepend suffix)
          lift origin entry start prior ⟨some finalCurrent, finalTrace⟩ point saved unfinished
            choice missed missing retained later.joints headWord
      simp only [activeStart, ↓reduceIte] at nextPoint nextMask
      rw [mask] at nextMask
      have canonical : Setup.proposalRecoveryJoint joint = fun player =>
          if player = owner then some ⟨OwnAction.commit owner name payload choice, missed⟩ else
            none := by
        exact semantic.trans jointEq
      have headRead : owner = observer → head.get? store = some choice := by
        intro same
        subst owner
        have beforeActive : observer ∉ start.excluded := activeStart
        have nextActive : observer ∉ next.excluded := by
          have monotone := setup.commitRecovery_public_excluded_of_reaches
            (setup.proposalRecoveryEraseTrace_prefix kept).reachesWithin
          change next.excluded ⊆ finalCurrent.excluded at monotone
          exact fun member => survives (monotone member)
        have position : named.val = instructionCount setup.program -
            ProtocolState.remaining setup.program start.point := by
          rw [ranking, point, origin.remaining_lift, ProtocolState.remaining_entry]
          simp only [zero, Nat.add_zero]
          omega
        obtain ⟨value, proper⟩ := source_foreign_binding_success setup focal observer foreign
          named payload shape start prior joint legal next moved position beforeActive nextActive
            (source_good_prefix setup focal _ finalTrace kept good)
        have data := sourceReplayCompiledHeadData setup name observer payload fresh guard rest
          suffix embedding views.actionEq choice missed missing joint canonical shape
        have choiceEq : choice = .success value := congrArg Prod.fst (data.symm.trans proper)
        have originRead := sourceBindingAt_of_origin setup attemptId named observer payload shape
          start prior joint legal (some next) moved generation savedRank position.symm
            (.success value, false) proper target.trace (kept.trans toTarget)
        have stored := read zero (by simp only [zero, SourceProgram.CommitPrefix.length]; omega)
          payload shape value originRead
        rw [choiceEq]
        exact stored
      have nextAgrees : ∀ {readName cell} (source : HasVar
          ((name, .commitment owner payload) :: Γ) readName cell), cellVisibleTo observer cell →
          ((refs.cons (name := name) head).get source).get? store =
            some (cellValue ((commitSuccessor name guard entry choice).state.get source)) := by
        intro readName cell source visible
        cases source with
        | here => exact headRead visible
        | there source => exact agrees source visible
      have tailWord := sourceReplayTailWord setup ⟨some finalCurrent, finalTrace⟩ start prior
        next joint legal moved _ later.joints canonical word
      intro readName cell source visible
      refine ih suffix
        (embedding.tail (rest.prepend suffix) (by
          simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
        (refs.cons (name := name) head) (fun point => lift (.inr point))
        (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin)
        (ProtocolViewSuffix.commitTail setup.program fresh guard (rest.prepend suffix) refs
          embedding lift views) store next finalCurrent (prior.extend joint legal moved)
        finalTrace target toTarget nextPoint nextMask (by rw [nextSaved]; exact saved)
        (by rw [nextSaved]; exact endpoint) kept tailWord attemptId
        (nextGeneration.trans generation) (by rw [nextSaved]; exact savedRank)
        (low + 1) ?_ (by
          simp only [SourceProgram.CommitPrefix.prepend, instructionCount] at clock ⊢; omega)
        focal observer foreign survives good nextAgrees ?_ source visible
      · intro index
        have rank := ranking index.succ
        dsimp only [OutputEmbedding.tail] at rank ⊢
        simp only [Fin.cast_eq_self, Fin.val_succ] at rank ⊢
        omega
      · intro index inside ty binding value originRead
        exact read index.succ (by
          simp only [Fin.val_succ, SourceProgram.CommitPrefix.length]; omega) ty binding value
            originRead
  | @excluded Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      inactive later ih =>
      intro suffix embedding refs lift origin views store start finalCurrent prior finalTrace target
        toTarget point mask saved endpoint retained word attemptId generation savedRank low ranking
        clock focal observer foreign survives good agrees read
      have inactiveStart : owner ∈ start.excluded := by rwa [mask]
      have different : owner ≠ observer := by
        intro equal
        have monotone := setup.commitRecovery_public_excluded_of_reaches
          (setup.proposalRecoveryEraseTrace_prefix retained).reachesWithin
        change start.excluded ⊆ finalCurrent.excluded at monotone
        exact survives (equal ▸ monotone inactiveStart)
      let zero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event zero) =
          .binding owner payload := by
        change outputLayout setup.program (embedding.event zero) = _
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.layout_eq zero
      let head : FieldRef (graphLayout setup.program) (.binding owner payload) :=
        ⟨.inr (embedding.event zero), shape⟩
      have jointEq : start.commitJoint owner name payload .failure false = fun _ => none := by
        funext player
        change (if player = owner ∧ owner ∉ start.excluded then _ else _) = none
        simp only [inactiveStart, not_true_eq_false, and_false, ↓reduceIte]
      have headWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace finalTrace) =
          (start.commitJoint owner name payload .failure false :: later.joints).reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior) := by
        rw [jointEq]
        exact word
      obtain ⟨next, joint, legal, moved, kept, nextPoint, nextMask, nextSaved, nextGeneration,
        semantic⟩ := sourceReplay_unclosed_commit_head setup fresh guard (rest.prepend suffix)
          lift origin entry start prior ⟨some finalCurrent, finalTrace⟩ point saved (by
            rw [rest.instructionCount_prepend]; omega) .failure false
              (by intro impossible; cases impossible) retained later.joints headWord
      simp only [mask, inactive, ↓reduceIte] at nextPoint nextMask
      have canonical : Setup.proposalRecoveryJoint joint = fun _ => none := by
        exact semantic.trans jointEq
      have nextAgrees : ∀ {readName cell} (source : HasVar
          ((name, .commitment owner payload) :: Γ) readName cell), cellVisibleTo observer cell →
          ((refs.cons (name := name) head).get source).get? store =
            some (cellValue ((automaticCommit name owner payload entry).state.get source)) := by
        intro readName cell source visible
        cases source with
        | here => exact (different visible).elim
        | there source => exact agrees source visible
      have tailWord := sourceReplayTailWord setup ⟨some finalCurrent, finalTrace⟩ start prior
        next joint legal moved _ later.joints canonical word
      intro readName cell source visible
      refine ih suffix
        (embedding.tail (rest.prepend suffix) (by
          simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
        (refs.cons (name := name) head) (fun point => lift (.inr point))
        (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin)
        (ProtocolViewSuffix.commitTail setup.program fresh guard (rest.prepend suffix) refs
          embedding lift views) store next finalCurrent (prior.extend joint legal moved)
        finalTrace target toTarget nextPoint nextMask (by rw [nextSaved]; exact saved)
        (by rw [nextSaved]; exact endpoint) kept tailWord attemptId
        (nextGeneration.trans generation) (by rw [nextSaved]; exact savedRank)
        (low + 1) ?_ (by
          simp only [SourceProgram.CommitPrefix.prepend, instructionCount] at clock ⊢; omega)
        focal observer foreign survives good nextAgrees ?_ source visible
      · intro index
        have rank := ranking index.succ
        dsimp only [OutputEmbedding.tail] at rank ⊢
        simp only [Fin.cast_eq_self, Fin.val_succ] at rank ⊢
        omega
      · intro index inside ty binding value originRead
        exact read index.succ (by
          simp only [Fin.val_succ, SourceProgram.CommitPrefix.length]; omega) ty binding value
            originRead

omit [Fintype Player] in
private theorem sourceReplay_generated_semantic_word
    (owner : Player) {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.GeneratedPreparationHistory owner ⟨state, trace⟩ ↔
      ∃ joint ∈ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace trace),
        ProposalRecoveryMove.GeneratedPreparationFailure
          ((joint owner).map ProposalRecoveryMove.ordinary) := by
  rw [generated_preparation_iff_joint_word, ← setup.proposalRecoveryJointRecall_semantic]
  constructor
  · rintro ⟨joint, member, bad⟩
    refine ⟨Setup.proposalRecoveryJoint joint, List.mem_map.mpr ⟨joint, member, rfl⟩, ?_⟩
    cases selected : joint owner with
    | none => simp only [ProposalRecoveryMove.GeneratedPreparationFailure,
        selected, Option.elim_none] at bad
    | some move =>
        simpa only [Setup.proposalRecoveryJoint, selected, Option.map_some, Option.elim_some,
          ProposalRecoveryMove.GeneratedPreparationFailure, ProposalRecoveryMove.ordinary]
          using bad
  · rintro ⟨joint, member, bad⟩
    obtain ⟨original, member, same⟩ := List.mem_map.mp member
    refine ⟨original, member, ?_⟩
    rw [← same] at bad
    cases selected : original owner with
    | none => simp only [Setup.proposalRecoveryJoint, selected, Option.map_none,
        ProposalRecoveryMove.GeneratedPreparationFailure, Option.elim_none] at bad
    | some move =>
        simpa only [Setup.proposalRecoveryJoint, selected, Option.map_some, Option.elim_some,
          ProposalRecoveryMove.GeneratedPreparationFailure, ProposalRecoveryMove.ordinary]
          using bad

omit [Fintype Player] in
private theorem sourceReplay_good_of_proper_word
    (focal : Player) (earlier later : setup.proposalRecoveryProtocol.History)
    (good : setup.proposalRecoveryForeignGood focal earlier)
    (word : List (Player → Option (CommitRecoveryMove Player L)))
    (instructions : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace later.trace) =
      word.reverse ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace earlier.trace))
    (proper : ∀ joint ∈ word, ∀ owner move, joint owner = some move →
      move.missing = false ∧ ¬ move.action.IsFailure) :
    setup.proposalRecoveryForeignGood focal later := by
  intro owner foreign generated
  obtain ⟨joint, member, bad⟩ :=
    (sourceReplay_generated_semantic_word setup owner later.trace).mp generated
  rw [instructions] at member
  rcases List.mem_append.mp member with fresh | old
  · have selected : joint ∈ word := List.mem_reverse.mp fresh
    cases chosen : joint owner with
    | none =>
        simp only [chosen, Option.map_none, ProposalRecoveryMove.GeneratedPreparationFailure,
          Option.elim_none] at bad
    | some move =>
        have forbidden := (proper joint selected owner move chosen).2
        rw [chosen, Option.map_some] at bad
        exact forbidden (ProposalRecoveryMove.generatedPreparationFailure_flags move bad).2
  · exact good owner foreign
      ((sourceReplay_generated_semantic_word setup owner earlier.trace).mpr ⟨joint, old, bad⟩)

private theorem sourceReplay_first_attempt_exit
    (before reference : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some reference))
    (retained : TracePrefix prior trace)
    (changed : reference.execution.application.attempt ≠ before.execution.application.attempt) :
    ∃ (closing ending : (nativeApplication).Control)
      (closingTrace : (nativeProtocol).Trace (some closing))
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal (some closing) joint)
      (moved : some ending ∈ ((nativeProtocol).step (some closing) ⟨joint, legal⟩).support),
      TracePrefix prior closingTrace ∧
      TracePrefix (closingTrace.extend joint legal moved) trace ∧
      closing.execution.application.attempt = before.execution.application.attempt ∧
      ending.execution.application.attempt ≠ closing.execution.application.attempt := by
  have along : ∀ {state} {later : (nativeProtocol).Trace state}, TracePrefix prior later →
      ∃ current : (nativeApplication).Control, state = some current ∧
      (current.execution.application.attempt ≠ before.execution.application.attempt →
        ∃ (closing ending : (nativeApplication).Control)
          (closingTrace : (nativeProtocol).Trace (some closing))
          (joint : Player → Option (nativeApplication).Action)
          (legal : (nativeProtocol).Legal (some closing) joint)
          (moved : some ending ∈
            ((nativeProtocol).step (some closing) ⟨joint, legal⟩).support),
          TracePrefix prior closingTrace ∧
          TracePrefix (closingTrace.extend joint legal moved) later ∧
          closing.execution.application.attempt = before.execution.application.attempt ∧
          ending.execution.application.attempt ≠ closing.execution.application.attempt) := by
    intro state later kept
    induction kept with
    | refl => exact ⟨before, rfl, fun different => (different rfl).elim⟩
    | @extend source target middle kept joint legal moved ih =>
        obtain ⟨current, rfl, previous⟩ := ih
        have realized : target ∈ ((nativeApplication).transition nativeInitial
            implementation.horizon implementation.scheduler (some current) joint).support := moved
        obtain ⟨next, rfl, _recall⟩ := (nativeApplication).transition_recall_prefix nativeInitial
          implementation.horizon implementation.scheduler current target joint realized
        refine ⟨next, rfl, ?_⟩
        intro different
        by_cases same : current.execution.application.attempt = before.execution.application.attempt
        · exact ⟨current, next, middle, joint, legal, moved, kept, .refl, same,
            fun equal => different (equal.trans same)⟩
        · obtain ⟨closing, ending, closingTrace, choices, offered, reached, fromStart, toMiddle,
            attemptEq, changed⟩ := previous same
          exact ⟨closing, ending, closingTrace, choices, offered, reached, fromStart,
            toMiddle.extend joint legal moved, attemptEq, changed⟩
  obtain ⟨current, state, result⟩ := along retained
  cases Option.some.inj state
  exact result changed

-- BEGIN LITERAL COMMIT WINDOW

/-- The literal interior commitment occurrence reads the same normalized
information as its omission-free representative from the identical saved trace. -/
private theorem sourceReplay_query_of_literal_commit_window
    (operational : implementation.Operational)
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (actual : (nativeApplication).Control)
    (actualTrace : (nativeProtocol).Trace (some actual))
    (owner : Player) (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (actualActing : actual.actor = some owner)
    (publicFrame : actual.execution.application.publicView =
      before.execution.application.publicView)
    (network : actual.execution.network = before.execution.network)
    (nativeRequest : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, named⟩)
    (entryCurrent : CommitRecoveryState setup.program)
    (entryTrace : setup.proposalRecoveryProtocol.Trace (some entryCurrent))
    (entryPoint : entryCurrent = CommitRecoveryState.atPoint entryCurrent.point
      entryCurrent.excluded entryCurrent.generation)
    (committing : ProtocolState.atCommit setup.program entryCurrent.point = true)
    (entryRank : instructionCount setup.program -
      ProtocolState.remaining setup.program entryCurrent.point =
        before.execution.application.attempt.phase)
    (entryExcluded : entryCurrent.excluded = before.execution.application.entry.excluded)
    (entryGeneration : entryCurrent.generation = before.execution.application.generation)
    (addresses : setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace entryTrace) =
      before.execution.application.sourcePublicAddressWord implementation.plan
        before.execution.application.attempt.phase)
    (current : CommitRecoveryState setup.program)
    (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (retained : TracePrefix entryTrace sourceTrace)
    (inside : sourceTrace.length + ProtocolState.commitEnd setup.program entryCurrent.point <
      entryTrace.length + ProtocolState.remaining setup.program entryCurrent.point)
    (rank : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (_generation : current.generation = before.execution.application.generation)
    (saved : current.saved = entryCurrent.point)
    (active : owner ∉ current.excluded)
    (typed : phaseVirtualSourceView? setup .concurrent implementation.runtime
      implementation.leaks owner named (actual.execution.observe nativeApplication owner) =
        some (ProtocolView.eraseHistory owner setup.program
          (ProtocolState.observe owner setup.program current.point)))
    (proposals : setup.proposalRecoveryArchive owner
        (setup.proposalRecoveryModel.infoOf owner sourceTrace) =
      PhaseProposal.sourceArchive before.execution.network.inputs) :
    phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
        implementation.plan owner named (actual.execution.recall owner)
          (actual.execution.observe nativeApplication owner) =
      some (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner sourceTrace)) := by
  classical
  let rawSource := setup.proposalRecoveryEraseTrace sourceTrace
  let rawOriginal := setup.proposalRecoveryEraseTrace entryTrace
  let rawEntry : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint entryCurrent.point entryCurrent.excluded
        entryCurrent.generation)) := (congrArg some entryPoint) ▸ rawOriginal
  have castHistory {first second : setup.commitRecoveryProtocol.State}
      (equal : first = second) (trace : setup.commitRecoveryProtocol.Trace first) :
      (⟨second, equal ▸ trace⟩ : setup.commitRecoveryProtocol.History) = ⟨first, trace⟩ := by
    cases equal
    rfl
  have entryHistory : (⟨_, rawEntry⟩ : setup.commitRecoveryProtocol.History) =
      ⟨some entryCurrent, rawOriginal⟩ := castHistory (congrArg some entryPoint) rawOriginal
  have entryLength : rawEntry.length = entryTrace.length := by
    have equal := congrArg
      (fun history : setup.commitRecoveryProtocol.History => history.trace.length)
      entryHistory
    exact equal.trans (setup.proposalRecoveryEraseTrace_length entryTrace)
  have sourceLength : rawSource.length = sourceTrace.length :=
    setup.proposalRecoveryEraseTrace_length sourceTrace
  have rawKept : TracePrefix rawEntry rawSource := by
    have castPrefix {first second last : setup.commitRecoveryProtocol.State}
        (equal : first = second) (trace : setup.commitRecoveryProtocol.Trace first)
        (finish : setup.commitRecoveryProtocol.Trace last) (kept : TracePrefix trace finish) :
        TracePrefix (equal ▸ trace) finish := by
      cases equal
      exact kept
    exact castPrefix (congrArg some entryPoint) rawOriginal rawSource
      (setup.proposalRecoveryEraseTrace_prefix retained)
  have rawInside : rawSource.length + ProtocolState.commitEnd setup.program entryCurrent.point <
      rawEntry.length + ProtocolState.remaining setup.program entryCurrent.point := by
    rw [entryLength, sourceLength]
    exact inside
  obtain ⟨original, replay, originalState, originalSaved, originalEntry, originalGeneration,
    replayTrace, replayKept, replayLength, replaySaved, replayEntry, replayGeneration,
    replayExcluded, replayView, replayInformation⟩ :=
    setup.commitRecovery_noMiss_prefix_information owner entryCurrent.point entryCurrent.excluded
      entryCurrent.generation rawEntry committing rawSource rawKept rawInside active
  have originalEq : original = current := (Option.some.inj originalState).symm
  subst original
  have entryActive : owner ∉ entryCurrent.excluded := by
    intro member
    exact active (current.entered (originalEntry.symm ▸ member))
  have replayActive : owner ∉ replay.excluded := by rwa [replayExcluded]
  have replayInside :
      replayTrace.length + ProtocolState.commitEnd setup.program entryCurrent.point <
      rawEntry.length + ProtocolState.remaining setup.program entryCurrent.point := by
    rw [replayLength]
    exact rawInside
  obtain ⟨rankCurrent, rankState, _currentCommit, _endpoint, remaining⟩ :=
    setup.commitRecovery_prefix_inside_commit
      (CommitRecoveryState.atPoint entryCurrent.point entryCurrent.excluded
        entryCurrent.generation) rawEntry committing rawSource rawKept rawInside
  have rankEq : rankCurrent = current := (Option.some.inj rankState).symm
  subst rankCurrent
  have pointRank : rawSource.length + ProtocolState.remaining setup.program current.point =
      rawEntry.length + ProtocolState.remaining setup.program entryCurrent.point := remaining
  let sourceEntry : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation)) :=
    (show some (CommitRecoveryState.atPoint entryCurrent.point entryCurrent.excluded
        entryCurrent.generation) =
      some (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation) by
        rw [saved, originalEntry, originalGeneration]) ▸ rawEntry
  have sourceEntryHistory : (⟨_, sourceEntry⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, rawEntry⟩ := by
    dsimp only [sourceEntry]
    exact castHistory _ rawEntry
  have sourceEntryLength : sourceEntry.length = rawEntry.length :=
    congrArg (fun history : setup.commitRecoveryProtocol.History => history.trace.length)
      sourceEntryHistory
  have sourceEntryKept : TracePrefix sourceEntry rawSource := by
    have castPrefix {first second last : setup.commitRecoveryProtocol.State}
        (equal : first = second) (trace : setup.commitRecoveryProtocol.Trace first)
        (finish : setup.commitRecoveryProtocol.Trace last) (kept : TracePrefix trace finish) :
        TracePrefix (equal ▸ trace) finish := by
      cases equal
      exact kept
    exact castPrefix _ rawEntry rawSource rawKept
  have sourceBalance : rawSource.length + ProtocolState.remaining setup.program current.point =
      sourceEntry.length + ProtocolState.remaining setup.program current.saved := by
    rw [sourceEntryLength, saved]
    exact pointRank
  have cut := setup.commitRecoveryAttemptStart_of_entry owner current rawSource
    sourceEntry sourceEntryKept sourceBalance
  have savedExclusions := setup.commitRecoverySavedExclusions_of_entry owner current rawSource
    sourceEntry sourceEntryKept sourceBalance
  have currentCommit : ProtocolState.atCommit setup.program current.point = true :=
    (source_binding_at_rank setup.program current.point named owner ty shape rank).1
  have normalized : setup.commitRecoveryNoMissInformation owner
      (setup.commitRecoveryModel.infoOf owner rawSource) =
        setup.commitRecoveryModel.infoOf owner replayTrace := by
    unfold Setup.commitRecoveryNoMissInformation
    have currentSignal : (setup.commitRecoveryModel.infoOf owner rawSource).1.1 =
        (setup.commitRecoveryPrivate owner (some current),
          setup.commitRecoveryPublic (some current)) := by
      change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf owner rawSource).1.1 = _
      rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current owner rawSource]
    rw [currentSignal, savedExclusions]
    simp only [Setup.commitRecoveryPrivate, Setup.commitRecoveryPublic,
      Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe, currentCommit, active, originalEntry, entryActive,
      not_false_eq_true, and_self, ↓reduceIte]
    rw [cut, sourceEntryLength]
    exact replayInformation.symm
  have liveCount : replayTrace.length - rawEntry.length =
      named.val - before.execution.application.attempt.phase := by
    have bound := ProtocolState.remaining_le_instructionCount setup.program entryCurrent.point
    have currentBound := ProtocolState.remaining_le_instructionCount setup.program current.point
    have length := rawKept.length_le
    rw [replayLength]
    omega
  have replayAddresses := source_binding_prefix_addresses setup owner entryCurrent.point
    entryCurrent.excluded entryCurrent.generation rawEntry committing entryActive replayTrace
      replayKept replayInside replayExcluded
  have originalAddresses : setup.recoveryAddressWord rawEntry =
      before.execution.application.sourcePublicAddressWord implementation.plan
        before.execution.application.attempt.phase := by
    have equal := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      setup.recoveryAddressWord history.trace) entryHistory
    exact equal.trans addresses
  have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have counted := initialEq ▸ prior
  have rawPrior := (nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler counted
  obtain ⟨phase, remainingPhases, installed, _kind, _inside⟩ := phase_ready_binding_phase
    implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler rawPrior
          owner named ty shape nativeRequest.2.2.1
  have savedMask := PhaseRuntimeState.saved_excluded_eq_public_failures
    (phaseArchivedExclusions_history implementation.runtime implementation.leaks implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler rawPrior)
    (phasePublicFailureCheckpoint_history implementation.runtime implementation.leaks
      implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
        implementation.scheduler rawPrior)
    (phaseExclusionRecord_history implementation.runtime implementation.leaks implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon
        implementation.scheduler rawPrior).frontier
      phase remainingPhases installed
  have inherited :
      (before.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun a b => a ∪ b) ∅ =
      PhaseRuntimeState.archivedFailureOwners before.execution.application.retired := by
    have failures := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
      before.execution.application.retired
    simpa only [RuntimePhasePlan.sourceRecordFailures, PhaseRuntimeState.sourceControlRecords,
      PhaseRuntimeState.publicView, List.map_map, Function.comp_def,
      State.sourceFailureFootprint_read, State.sourceFailureFootprint] using failures
  have word : setup.recoveryAddressWord replayTrace =
      before.execution.application.sourcePublicAddressWord implementation.plan named.val := by
    rw [replayAddresses, originalAddresses, liveCount, entryRank, entryExcluded, entryGeneration]
    unfold PhaseRuntimeState.sourcePublicAddressWord
    simp only [Nat.sub_self, List.range_zero, List.map_nil, List.append_nil,
      State.sourceFailureFootprint]
    have masks :
        ((PhaseRuntimeState.sourceControlRecords before.execution.application.retired).map
            (fun record => record.2.2)).foldr (fun a b => a ∪ b) ∅ =
          PhaseRuntimeState.archivedFailureOwners before.execution.application.retired := by
      exact PhaseRuntimeState.sourceRecordFailures_sourceControlRecords _
    rw [masks, ← savedMask]
    rfl
  have observedPublic :
      (implementation.application.observePlayer actual.execution.application owner).2 =
        before.execution.application.publicView := by
    change actual.execution.application.publicView = _
    exact publicFrame
  have replayControls : setup.commitRecoveryPublic (some replay) =
      (before.execution.application.entry.excluded, before.execution.application.generation,
        before.execution.application.attempt.phase) := by
    change (replay.excluded, replay.generation, instructionCount setup.program -
      ProtocolState.remaining setup.program replay.saved) = _
    rw [replayExcluded, replayGeneration, replaySaved, entryRank, entryExcluded, entryGeneration]
  have read := setup.commitRecovery_erasedInformation_read owner replay replayTrace replayActive
  rw [replayControls, setup.commitRecovery_publicRecall_addresses, word] at read
  have nativeRead : setup.commitRecoveryErasedRead owner
      (ProtocolView.eraseHistory owner setup.program
        (ProtocolState.observe owner setup.program current.point))
      (before.execution.application.entry.excluded, before.execution.application.generation,
        before.execution.application.attempt.phase)
      ((before.execution.application.sourcePublicAddressWord
        implementation.plan named.val).reverse ++
        [(none, (∅, 0, 0))]) =
      setup.commitRecoveryErasedInformation owner
        (setup.commitRecoveryModel.infoOf owner replayTrace) := by
    rw [← replayView]
    simpa only [Setup.commitRecoveryErasedRead, ProtocolView.eraseHistory_idempotent,
      ProtocolView.publicPadding_eraseHistory] using read.symm
  have semantic : phaseVirtualSourceQuery? setup .concurrent implementation.runtime
      implementation.leaks implementation.plan owner named
        (actual.execution.observe nativeApplication owner) =
      some (setup.commitRecoveryErasedInformation owner
        (setup.commitRecoveryNoMissInformation owner
          (setup.commitRecoveryModel.infoOf owner rawSource))) := by
    unfold phaseVirtualSourceQuery?
    rw [typed, Option.map_some]
    dsimp only [ReactiveApplication.Execution.observe, phaseApplication,
      PhaseRuntimeState.playerView]
    rw [observedPublic, PhaseRuntimeState.sourcePublicAddressWord_read, inherited]
    dsimp only [PhaseRuntimeState.publicView]
    rw [State.sourceFailureFootprint_read]
    dsimp only [State.sourceFailureFootprint]
    rw [← savedMask]
    change some (setup.commitRecoveryErasedInformation owner
      (setup.commitRecoveryNoMissInformation owner
        (setup.commitRecoveryErasedRead owner _
          (before.execution.application.entry.excluded,
            before.execution.application.generation, before.execution.application.attempt.phase)
          _))) = _
    rw [nativeRead, ← normalized]
    exact congrArg some (setup.commitRecoveryNoMissInformation_erased_idempotent owner _)
  have countedActual := initialEq ▸ actualTrace
  have archive := PhaseProposal.observedSourceArchive_eq_submitted implementation.runtime
    implementation.leaks operational.completePending
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler actual
          ((nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler countedActual)
            owner actualActing
  unfold phaseProposalQuery? Setup.proposalRecoveryQuery
  rw [semantic, Option.map_some, setup.proposalRecoveryEraseInfo_observed, archive, network,
    proposals]

-- END LITERAL COMMIT WINDOW

/-- A foreign actual initialized callback reads the query at the same literal
target commitment occurrence. Only the focal native recall is fixed. -/
theorem sourceReplay_query_binding
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
      (reference.execution.recall who)
      (reference.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some reference, referenceTrace⟩)
    (entry : NativeBindingEntry setup implementation operational reference referenceTrace
      who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who
        (entry.canonicalCut setup values implementation operational fullValues reference
          referenceTrace who acting event payload clean foreign).trace)
    (good : setup.proposalRecoveryForeignGood who g)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g choice).support)
    (selectedAgreement : SourceReplaySelectedAgreement (setup := setup)
      (implementation := implementation) operational who reference referenceTrace g
        targetCurrent targetTrace)
    (completedVisit : SourceReplayCompletedVisit (setup := setup)
      (implementation := implementation) operational who reference referenceTrace g
        targetCurrent targetTrace)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (restricted : SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who lost)
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix prior referenceTrace)
    (actual : (nativeApplication).Control)
    (actualTrace : (nativeProtocol).Trace (some actual))
    (owner : Player) (ownerForeign : owner ≠ who)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (actualActing : actual.actor = some owner)
    (application : actual.execution.application = sourceSnapshotAssignment setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference lost before.execution.application)
    (network : actual.execution.network = before.execution.network)
    (_receipts : actual.execution.receipts = before.execution.receipts)
    (_environmentRecall : actual.execution.environmentRecall = before.execution.environmentRecall)
    (_focalRecall : actual.execution.recall who = before.execution.recall who)
    (request : actual.execution.application.SeedRequest owner
      ⟨actual.execution.application.attempt, named⟩) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current)),
      TracePrefix sourceTrace targetTrace ∧
      named.val = instructionCount setup.program -
        ProtocolState.remaining setup.program current.point ∧
      current.generation = before.execution.application.generation ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.saved =
        before.execution.application.attempt.phase ∧
      owner ∉ current.excluded ∧
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
          implementation.plan owner named (actual.execution.recall owner)
            (actual.execution.observe nativeApplication owner) =
        some (setup.proposalRecoveryQuery owner
          (setup.proposalRecoveryModel.infoOf owner sourceTrace)) := by
  classical
  let target : setup.proposalRecoveryProtocol.History := ⟨some targetCurrent, targetTrace⟩
  let cut := entry.canonicalCut setup values implementation operational fullValues reference
    referenceTrace who acting event payload clean foreign
  let witness := (checkpointSelection setup implementation operational prior).val
  let selected := witness.checkpoint
  obtain ⟨mapped, mappedCurrent, live, saved, mappedToG, mappedToTarget, mappedLength,
    mappedInfo, mappedState, mappedPoint, mappedSaved, mappedExcluded, mappedGeneration,
    mappedAgreement⟩ := selectedAgreement lost restricted before prior retained
  have nativeRequest : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, named⟩ := by
    rw [application] at request
    exact request
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have counted : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before) := by
    rw [← initialEq]
    exact prior
  obtain ⟨phase, remaining, installed, commitment, inside⟩ := phase_ready_binding_phase
    implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
          ((nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler counted)
            owner named ty shape nativeRequest.2.2.1
  have geometry := source_checkpoint_binding_interval setup implementation witness
    operational.maximalPhases phase remaining installed commitment
  have mappedCommitting : ProtocolState.atCommit setup.program mappedCurrent.point = true := by
    rw [mappedPoint, selected.atCommit]
    have original := geometry.1
    change ProtocolState.atCommit setup.program
      (selected.residual.lift (ProtocolState.entry selected.residual.tail selected.source)) = true
        at original
    rw [selected.atCommit] at original
    have entryCommit : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
        (program : SourceProgram Player L Γ O) (first second : SourceProgram.Config Player L Γ),
        ProtocolState.atCommit program (ProtocolState.entry program first) =
          ProtocolState.atCommit program (ProtocolState.entry program second) := by
      intro Γ O program first second
      cases program <;> rfl
    exact (entryCommit selected.residual.tail live selected.source).trans original
  rcases mapped with ⟨mappedState', mappedTrace⟩
  cases mappedState
  obtain ⟨liveSaved, savedEq, entryMask⟩ := sourceReplay_selected_entry setup
    before.execution.application selected mappedCurrent mappedTrace live saved mappedPoint
      mappedSaved
      mappedCommitting
  have mappedSavedRank : instructionCount setup.program -
      ProtocolState.remaining setup.program mappedCurrent.saved =
        before.execution.application.attempt.phase := by
    rw [mappedSaved, selected.remaining, ProtocolState.remaining_entry]
    have original := selected.saved_position
    rw [selected.remaining, ProtocolState.remaining_entry] at original
    exact original
  have mappedRank : instructionCount setup.program -
      ProtocolState.remaining setup.program mappedCurrent.point =
        before.execution.application.attempt.phase := by
    rw [← savedEq]
    exact mappedSavedRank
  have mappedEndpoint : instructionCount setup.program -
      ProtocolState.commitEnd setup.program mappedCurrent.saved = phase.high := by
    rw [mappedSaved, selected.commitEnd]
    have original := geometry.2.2
    change instructionCount setup.program - ProtocolState.commitEnd setup.program
      (selected.residual.lift (ProtocolState.entry selected.residual.tail selected.source)) =
        phase.high at original
    rw [selected.commitEnd] at original
    change instructionCount setup.program - ProtocolState.commitEnd selected.residual.tail
      (ProtocolState.entry selected.residual.tail saved) = phase.high
    simpa only [ProtocolState.commitEnd_entry] using original
  have phaseLow : before.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have namedBounds := (phase.mem_events named).mp inside
  have archive := sourceReplay_selected_archive setup implementation operational before reference
    prior referenceTrace retained phase (by rw [installed]; rfl) commitment owner
      nativeRequest.2.2.2.2
  have mappedArchive : setup.proposalRecoveryArchive owner
      (setup.proposalRecoveryModel.infoOf owner mappedTrace) =
      PhaseProposal.sourceArchive before.execution.network.inputs := by
    rw [sourceReplay_archive_observer setup owner who mappedTrace]
    rw [mappedInfo]
    rw [← sourceReplay_archive_observer setup owner who
      (setup.proposalRecoveryLiftTrace (nativeArchiveLabels setup
        (PhaseProposal.sourceArchive reference.execution.network.inputs)) selected.trace)]
    exact archive
  have entryAgreement : selected.refs.Agrees live.state
      (sourceSnapshotState setup implementation target reference lost
        before.execution.application.current.native).config.store := by
    rw [liveSaved]
    apply sourceReplayEntryAgreesOfPreserved setup implementation selected.refs saved target
      reference lost before.execution.application.entry.native
        before.execution.application.current.native mappedAgreement
    · intro name cell source
      let field := (selected.refs.get source).field
      have occupied := selected.agrees source
      cases present : before.execution.application.entry.native.config.store field with
      | none =>
          have empty : (selected.refs.get source).get?
              before.execution.application.entry.native.config.store = none := by
            unfold FieldRef.get?
            rw [present]
            have castNone {α β : Type} (equal : α = β) :
                cast (congrArg Option equal) (none : Option α) = (none : Option β) := by
              cases equal
              rfl
            exact castNone (congrArg EventField.Value (selected.refs.get source).layout_eq)
          rw [empty] at occupied
          cases occupied
      | some value => exact (witness.stored field value present).symm
    · intro name cell source author domain shape value successful
      let field := (selected.refs.get source).field
      have read : (⟨field, shape⟩ : FieldRef (serviceGraph setup .concurrent).layout
          (.binding author domain)).get? before.execution.application.entry.native.config.store =
            some (.success value) := by
        change cast (congrArg (fun kind : EventField Player L => Option kind.Value) shape)
          (before.execution.application.entry.native.config.store field) = some (.success value)
        rw [successful]
        have cancel {α β : Type} (equal : α = β) (item : β) :
            cast (congrArg Option equal) (some (cast equal.symm item)) = some item := by
          cases equal
          rfl
        exact cancel (congrArg EventField.Value shape) (.success value)
      obtain ⟨candidate, accepted, _owned, _prepared⟩ :=
        witness.binding.saved.success_provenance ⟨field, shape⟩ value read
      have kept := phaseAcceptedCheckpoint_history implementation.runtime implementation.leaks
        implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
          implementation.scheduler
            ((nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler counted)
      exact accepted.trans (kept field candidate accepted).symm
  have entryAddresses : setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace mappedTrace) =
      before.execution.application.sourcePublicAddressWord implementation.plan
        before.execution.application.attempt.phase := by
    have semantic := congrArg (setup.proposalRecoveryEraseInfo who) mappedInfo
    rw [setup.proposalRecoveryEraseInfo_observed,
      setup.proposalRecoveryEraseInfo_observed] at semantic
    have publicRecall := setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq who
      (setup.proposalRecoveryEraseTrace mappedTrace)
      (setup.proposalRecoveryEraseTrace (setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive reference.execution.network.inputs))
          selected.trace))
        (congrArg (setup.commitRecoveryErasedInformation who) semantic)
    have numeric := congrArg (List.map (setup.commitRecoveryPublicAddress who)) publicRecall
    rw [setup.commitRecovery_publicRecall_addresses,
      setup.commitRecovery_publicRecall_addresses] at numeric
    have word := List.reverse_injective (List.append_cancel_right numeric)
    rw [setup.proposalRecoveryEraseTrace_lift] at word
    exact word.trans witness.chronology.addresses
  have assignedEarlier : ∀ (earlier : (serviceGraph setup .concurrent).EventId)
      (domain : L.Ty)
      (binding : (serviceGraph setup .concurrent).outputLayout earlier = .binding owner domain),
      before.execution.application.attempt.phase ≤ earlier.val → earlier.val < named.val →
      ∀ value : L.Val domain,
      sourceBindingAt setup before.execution.application.attempt earlier owner domain binding
        targetTrace = some value →
      (⟨.inr earlier, binding⟩ : FieldRef (graphLayout setup.program) (.binding owner domain)).get?
        (sourceSnapshotState setup implementation target reference lost
          before.execution.application.current.native).config.store = some (.success value) := by
    intro earlier domain binding lower earlierRank value sourceRead
    have earlierInside : earlier ∈ phase.events := (phase.mem_events earlier).mpr ⟨by omega, by
      omega⟩
    obtain ⟨candidate, _owned, accepted, physicalRead⟩ := phase_ready_earlier_binding_read
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler counted
          (serviceGraph_revealRelaxedOrdered setup .concurrent) phase (by rw [installed]; rfl)
            owner named ty shape nativeRequest.2.2.1 nativeRequest.2.2.2.2 earlier domain
              binding earlierInside earlierRank
    have noGenerated := no_generated_of_tracePrefix setup implementation owner retained
      (foreign owner ownerForeign)
    obtain ⟨old, proper⟩ := accepted_snapshot_value_of_no_generated_unusable setup implementation
      before prior before.execution.application.current.native (Or.inl rfl) owner noGenerated
        earlier domain binding candidate accepted
    rw [proper] at physicalRead
    obtain ⟨next, meaning, assignedStore, _assignedResult, _focal⟩ := assigned_accepted_binding_read
      setup values implementation operational reference (sourceCutTrace setup implementation
        referenceTrace)
        who event cut g sameInfo good choice properChoice target supported lost before
          (sourceCutTrace setup implementation prior)
          (tracePrefix_initializer setup implementation initialEq retained)
          before.execution.application.current.native (Or.inl rfl) owner domain earlier binding
            candidate old accepted physicalRead
    have signed := sourceReplay_signed_binding_read setup implementation reference before
      referenceTrace prior retained target earlier owner domain binding candidate next accepted
        lower meaning
    have valueEq : next = value := Option.some.inj (signed.symm.trans sourceRead)
    rw [valueEq] at assignedStore
    change cast (congrArg (fun kind : EventField Player L => Option kind.Value) binding)
      ((sourceSnapshotState setup implementation target reference lost
        before.execution.application.current.native).config.store (.inr earlier)) =
          some (.success value)
    rw [assignedStore]
    have cancel {α β : Type} (equal : α = β) (item : β) :
        cast (congrArg Option equal) (some (cast equal.symm item)) = some item := by
      cases equal
      rfl
    exact cancel (congrArg EventField.Value binding) (.success value)
  have typedAt : ∀ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current)),
      TracePrefix sourceTrace targetTrace → TracePrefix mappedTrace sourceTrace →
      sourceTrace.length = mappedTrace.length +
        (named.val - before.execution.application.attempt.phase) →
      current.generation = before.execution.application.generation →
      current.saved = mappedCurrent.point → owner ∉ current.excluded →
      setup.proposalRecoveryForeignGood who ⟨some current, sourceTrace⟩ →
      phaseVirtualSourceView? setup .concurrent implementation.runtime implementation.leaks
        owner named (actual.execution.observe nativeApplication owner) =
        some (ProtocolView.eraseHistory owner setup.program
          (ProtocolState.observe owner setup.program current.point)) := by
    intro current sourceTrace toTarget fromMapped depth generation savedPoint survives sourceGood
    obtain ⟨selectedIndex, selectedEvent, Δ, P, bindingName, fresh, guard, nextProgram, earlier,
      atEnd, reconstruct⟩ := selected.ready_binding_prefix witness.order.frontier phase remaining
        installed commitment named inside nativeRequest.2.2.1 owner ty shape
    let suffix := SourceProgram.commit bindingName owner fresh guard nextProgram
    let embedding := cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
      (outputLayout setup.program) program) reconstruct.symm) selected.embedding
    let lift : ProtocolState (earlier.prepend suffix) → ProtocolState setup.program :=
      fun point => selected.residual.lift (cast (congrArg ProtocolState reconstruct) point)
    have transport {Γ : SourceCtx Player L} {O : Finset VarId}
        {left right : SourceProgram Player L Γ O} (equal : left = right)
        (refs : ContextRefs (graphLayout setup.program) Γ)
        (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) right)
        (lift : ProtocolState right → ProtocolState setup.program)
        (origin : ProtocolSuffix setup.program right lift)
        (views : ProtocolViewSuffix setup.program right refs embedding lift) :
        PSigma fun _ : ProtocolSuffix setup.program left
          (fun point => lift (cast (congrArg ProtocolState equal) point)) =>
        ProtocolViewSuffix setup.program left refs
          (cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) program) equal.symm) embedding)
          (fun point => lift (cast (congrArg ProtocolState equal) point)) := by
      cases equal
      exact ⟨origin, views⟩
    obtain ⟨origin, views⟩ := transport reconstruct selected.refs selected.embedding
      selected.residual.lift selected.origin selected.views
    have entryTransport {Γ : SourceCtx Player L} {O : Finset VarId}
        {left right : SourceProgram Player L Γ O} (equal : left = right)
        (config : SourceProgram.Config Player L Γ) :
        cast (congrArg ProtocolState equal) (ProtocolState.entry left config) =
          ProtocolState.entry right config := by
      cases equal
      rfl
    have point : mappedCurrent.point = lift (ProtocolState.entry (earlier.prepend suffix) live) :=
      by
      dsimp only [lift]
      rw [entryTransport reconstruct]
      exact mappedPoint
    have ranking : ∀ index, (embedding.event index).val =
        before.execution.application.attempt.phase + index.val := by
      have castRank {Γ : SourceCtx Player L} {O : Finset VarId}
          {left right : SourceProgram Player L Γ O} (equal : left = right)
          (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
            right)
          (low : Nat) (rank : ∀ index, (embedding.event index).val = low + index.val) :
          ∀ index, ((cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) program) equal.symm) embedding).event index).val =
              low + index.val := by
        cases equal
        exact rank
      exact castRank reconstruct selected.embedding _ selected.compiled.rankEq
    let index : Fin (eventCount (earlier.prepend suffix)) :=
      ⟨earlier.length, by rw [← earlier.eventCount_prepend]; simp only [suffix, eventCount]; omega⟩
    have queryEvent : embedding.event index = named := by
      have castEvent {Γ : SourceCtx Player L} {O : Finset VarId}
          {left right : SourceProgram Player L Γ O} (equal : left = right)
          (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
            right)
          (first : Fin (eventCount left)) (second : Fin (eventCount right))
          (same : first.val = second.val) :
          (cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) program) equal.symm) embedding).event first =
              embedding.event second := by
        cases equal
        exact congrArg embedding.event (Fin.ext same)
      exact (castEvent reconstruct selected.embedding index selectedIndex atEnd.symm).trans
        selectedEvent
    have queriedRank := ranking index
    rw [queryEvent] at queriedRank
    have partialDepth : sourceTrace.length = mappedTrace.length + earlier.length := by
      dsimp only [index] at queriedRank
      omega
    let filled := fillCommitPrefix setup.program earlier suffix embedding
      (sourceSnapshotState setup implementation target reference lost
        before.execution.application.current.native).config.store live
    have endpoint : ProtocolState.commitEnd setup.program mappedCurrent.saved < instructionCount
      suffix := by
      rw [savedEq, point, origin.commitEnd_lift, earlier.commitEnd_suffix suffix live filled]
      have below := ProtocolState.commitEnd_lt_remaining suffix (ProtocolState.entry suffix filled)
        (by rfl)
      simpa only [ProtocolState.remaining_entry] using below
    obtain ⟨finished, excluded, attempt, endPoint, instructions⟩ :
        ∃ (finished : SourceProgram.Config Player L Δ) (excluded : Finset Player)
          (attempt : earlier.Attempt live mappedCurrent.excluded finished excluded),
          current.point = lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceTrace) =
            attempt.joints.reverse ++ setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace mappedTrace) := by
      by_cases positive : 0 < earlier.length
      · obtain ⟨finished, excluded, attempt, _addresses, _path, word, _addressWord,
          monotone, closed⟩ := source_attempt_of_literal_window setup
            (setup.initialConfig setup.initialLaw.support_nonempty.choose) earlier suffix lift
              origin
              live mappedCurrent current mappedTrace sourceTrace fromMapped point
                (by rw [savedEq]; exact mappedCommitting) endpoint.le positive partialDepth
        have remains : ProtocolState.commitEnd setup.program mappedCurrent.saved <
            ProtocolState.remaining setup.program
              (lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished))) := by
          rw [origin.remaining_lift, earlier.liftPoint_remaining, ProtocolState.remaining_entry]
          exact endpoint
        have unchanged := (mappedCurrent.install
          (lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished)), excluded)
            monotone).close_eq_self_of_remaining_gt
              (by change ProtocolState.atCommit setup.program mappedCurrent.saved = true
                  rw [savedEq]; exact mappedCommitting) remains
        rw [unchanged] at closed
        exact ⟨finished, excluded, attempt, congrArg CommitRecoveryState.point closed, word⟩
      · have empty : earlier.length = 0 := by omega
        have histories := fromMapped.eq_of_length (by omega)
        have states : mappedCurrent = current := Option.some.inj (congrArg History.state histories)
        cases earlier with
        | nil =>
            refine ⟨live, mappedCurrent.excluded, .nil live mappedCurrent.excluded, ?_, ?_⟩
            · rw [← states]
              exact point
            · have words := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
                  setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace))
                    histories
              exact words.symm
        | commit => simp only [SourceProgram.CommitPrefix.length] at empty; omega
    have clock : before.execution.application.attempt.phase +
        instructionCount (earlier.prepend suffix) = instructionCount setup.program := by
      rw [reconstruct]
      simpa only [eventCount_eq_instructionCount] using selected.compiled.countEq
    have visible : ∀ {name cell} (source : HasVar Δ name cell), cellVisibleTo owner cell →
        ((commitBlockRefs setup.program earlier suffix embedding selected.refs).get source).get?
          (sourceSnapshotState setup implementation target reference lost
            before.execution.application.current.native).config.store =
              some (cellValue (finished.state.get source)) := by
      intro name cell source isVisible
      exact sourceReplay_attempt_visible_agreement setup attempt suffix embedding
        selected.refs
        lift origin views
          (sourceSnapshotState setup implementation target reference lost
            before.execution.application.current.native).config.store
          mappedCurrent current mappedTrace sourceTrace target toTarget point rfl
          (by rw [savedEq]; exact mappedCommitting) endpoint fromMapped instructions
          before.execution.application.attempt mappedGeneration mappedSavedRank
          before.execution.application.attempt.phase ranking clock who owner ownerForeign
          survives sourceGood (fun source _visible => entryAgreement source) (by
            intro earlierIndex earlierInside payload binding value read
            have earlierRank := ranking earlierIndex
            exact assignedEarlier (embedding.event earlierIndex) payload binding (by omega)
              (by dsimp only [index] at queriedRank; omega) value read) source isVisible
    have decoded := sourceReplay_visible_prefix_decode setup earlier suffix selected.refs embedding
      lift views
        (sourceSnapshotState setup implementation target reference lost
          before.execution.application.current.native).config finished owner visible index rfl
    rw [queryEvent, ← endPoint] at decoded
    apply sourceReplay_foreign_virtual_view setup implementation operational who owner ownerForeign
      actual.execution named current sourceTrace survives sourceGood
    rw [application]
    exact decoded
  have queryAt : ∀ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current)),
      TracePrefix sourceTrace targetTrace → TracePrefix mappedTrace sourceTrace →
      sourceTrace.length = mappedTrace.length +
        (named.val - before.execution.application.attempt.phase) →
      named.val = instructionCount setup.program - ProtocolState.remaining setup.program
        current.point →
      current.generation = before.execution.application.generation →
      current.saved = mappedCurrent.point → owner ∉ current.excluded →
      setup.proposalRecoveryForeignGood who ⟨some current, sourceTrace⟩ →
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
          implementation.plan owner named (actual.execution.recall owner)
            (actual.execution.observe nativeApplication owner) =
        some (setup.proposalRecoveryQuery owner
          (setup.proposalRecoveryModel.infoOf owner sourceTrace)) := by
    intro current sourceTrace toTarget fromMapped depth rank generation savedPoint active sourceGood
    have entryPoint := source_commit_entry_eq_atPoint setup mappedCurrent mappedTrace
      mappedCommitting
      (by rw [savedEq])
    have within : sourceTrace.length + ProtocolState.commitEnd setup.program mappedCurrent.point <
        mappedTrace.length + ProtocolState.remaining setup.program mappedCurrent.point := by
      have remainingBound := ProtocolState.remaining_le_instructionCount setup.program
        mappedCurrent.point
      have endBound := ProtocolState.commitEnd_le_remaining setup.program mappedCurrent.point
      have endpoint : instructionCount setup.program -
          ProtocolState.commitEnd setup.program mappedCurrent.point = phase.high := by
        rw [← savedEq]
        exact mappedEndpoint
      rw [depth]
      omega
    have proposals := (setup.proposalRecoveryArchive_eq_of_commit_window owner mappedCurrent
      mappedTrace mappedCommitting sourceTrace fromMapped within.le).trans mappedArchive
    have publicFrame : actual.execution.application.publicView =
        before.execution.application.publicView := by
      rw [application]
      exact sourceSnapshotAssignment_public setup implementation target reference lost
        before.execution.application
    exact sourceReplay_query_of_literal_commit_window setup implementation operational before prior
      actual actualTrace owner named ty shape actualActing publicFrame network nativeRequest
        mappedCurrent mappedTrace entryPoint mappedCommitting mappedRank
        mappedExcluded mappedGeneration entryAddresses current sourceTrace fromMapped within rank
          generation savedPoint active
          (typedAt current sourceTrace toTarget fromMapped depth generation savedPoint active
            sourceGood)
          proposals
  by_cases finalAttempt : before.execution.application.attempt =
    reference.execution.application.attempt
  · have selectedEq := checkpointSelection_eq_of_attempt setup implementation operational
      before reference prior referenceTrace retained finalAttempt
    have selectedDepth := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.trace.length) selectedEq
    have canonicalEq : (⟨some cut.cursor.current, cut.cursor.trace⟩ :
        setup.proposalRecoveryProtocol.History) = canonicalSource setup implementation operational
          ⟨some reference, referenceTrace⟩ := entry.canonicalHistory
    have cursorDepth := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      history.trace.length) canonicalEq
    simp only [canonicalSource, setup.proposalRecoveryLiftTrace_length] at cursorDepth
    have mappedCursorDepth : mappedTrace.length = cut.cursor.trace.length :=
      mappedLength.trans (selectedDepth.trans cursorDepth.symm)
    have sameControls := phaseProposal_same_attempt_archive_metadata setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        implementation.horizon implementation.scheduler before reference
    rw [← initialEq] at sameControls
    have sameControls := sameControls prior referenceTrace retained finalAttempt
    have referenceInstalled : reference.execution.application.phases.head? = some phase := by
      rw [sameControls.1, installed]
      rfl
    have phaseEq : cut.phase = phase := Option.some.inj (cut.installed.symm.trans
      referenceInstalled)
    obtain ⟨canonicalFinished, canonicalLast, canonicalLastTrace, canonicalAttempt,
      canonicalCompleted, _canonicalPoint, canonicalExcluded, _canonicalGeneration,
      _canonicalLive, _canonicalAgrees, _canonicalWord, _canonicalLabels⟩ := cut.blockResult
    have lower := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
    have upper := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix cut.future).reachesWithin
    change cut.cursor.current.excluded ⊆ cut.current.excluded at lower
    change cut.current.excluded ⊆ (setup.commitRecoveryPublic cut.completed.state).1 at upper
    have canonicalEndpoint : cut.completed.state = some canonicalLast :=
      congrArg (fun history : setup.proposalRecoveryProtocol.History => history.state)
        canonicalCompleted
    rw [canonicalEndpoint] at upper
    change cut.current.excluded ⊆ canonicalLast.excluded at upper
    have cutMask : cut.current.excluded = cut.cursor.current.excluded :=
      Finset.Subset.antisymm (by simpa only [canonicalExcluded] using upper) lower
    have cursorOrdinary : cut.cursor.current.entryExcluded = cut.cursor.current.excluded :=
      cut.cursor.entryExcluded.trans cut.cursor.excluded.symm
    have cutOrdinary := (setup.commitRecovery_clean_rank_of_reaches who
      (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin cut.cursor.current
        cut.current rfl rfl cursorOrdinary cutMask cut.survives).1
    have metadata := source_information_metadata setup who g ⟨some cut.current, cut.trace⟩ sameInfo
    rcases g with ⟨gState, gTrace⟩
    cases gState with
    | none => cases metadata
    | some gCurrent =>
      change gCurrent.MetadataEq cut.current at metadata
      have ordinary : gCurrent.excluded = gCurrent.entryExcluded :=
        metadata.2.2.1.trans (cutOrdinary.symm.trans metadata.2.2.2.1.symm)
      have gRank : event.val = instructionCount setup.program -
          ProtocolState.remaining setup.program gCurrent.point := by
        rw [(ProtocolState.MetadataEq.controls setup.program _ _ metadata.1).1]
        exact cut.rank.symm
      obtain ⟨gCommitting, gActing, _gDecode⟩ := source_binding_at_rank setup.program
        gCurrent.point event who cut.payload cut.binding gRank
      have gDepth : gTrace.length = cut.trace.length := by
        have length := congrArg (fun information => information.1.2.length) sameInfo
        change
          (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who gTrace).1.2.length =
            (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who
              cut.trace).1.2.length at length
        rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at length
        simpa only [setup.source_signal_depth] using length
      have targetPrefix : TracePrefix gTrace targetTrace := by
        have support := supported
        unfold sourceForcedBlock at support
        obtain ⟨middle, first, last⟩ := (PMF.mem_support_bind_iff ..).mp support
        exact (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
          ⟨some gCurrent, gTrace⟩ middle first).tracePrefix.trans
            (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _ middle target
              last).tracePrefix
      obtain ⟨Γ, O, name, actor, domain, fresh, guard, nextProgram, lift, gEntry,
        origin, atEntry, _unique⟩ := ProtocolState.exists_committing_entry setup.program
          gCurrent.point setup.namesNodup gCommitting
      have actorEq : actor = who := by
        have acting := origin.actor_lift
          (ProtocolState.entry (.commit name actor fresh guard nextProgram) gEntry)
        rw [← atEntry] at acting
        exact Option.some.inj (acting.symm.trans gActing)
      subst actor
      obtain ⟨Δ, P, suffix, rest, reconstruct, boundary⟩ := SourceProgram.commitPhase nextProgram
      cases reconstruct
      let block : SourceProgram.CommitPrefix Γ O Δ P := .commit name who fresh guard rest
      have sameEnd : ProtocolState.commitEnd setup.program gCurrent.point =
          ProtocolState.commitEnd setup.program gCurrent.saved := by
        rcases setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace gTrace) with
          ⟨_saved, _live, same⟩ | same
        · exact same
        · rw [same]
      have endpoint : ProtocolState.commitEnd setup.program gCurrent.saved = instructionCount
        suffix := by
        rw [← sameEnd, atEntry, origin.commitEnd_lift]
        exact block.commitEnd_entry_prepend suffix boundary gEntry
      have distance : block.length + ProtocolState.commitEnd setup.program gCurrent.saved =
          ProtocolState.remaining setup.program gCurrent.point := by
        rw [endpoint, atEntry, origin.remaining_lift, ProtocolState.remaining_entry]
        exact (block.instructionCount_prepend suffix).symm
      have fuel : sourceCommitFuel setup ⟨some gCurrent, gTrace⟩ = rest.length + 1 := by
        change ProtocolState.remaining setup.program gCurrent.point -
          ProtocolState.commitEnd setup.program gCurrent.point = rest.length + 1
        rw [sameEnd]
        change rest.length + 1 +
          ProtocolState.commitEnd setup.program gCurrent.saved = _ at distance
        omega
      obtain ⟨forcedFinished, forcedLast, forcedTrace, forcedAttempt, forcedState,
        forcedPoint, forcedExcluded, _forcedEntry, _forcedGeneration, forcedWord,
        forcedProper, _forcedHead⟩ := sourceForcedBlock_commit_support setup values fresh guard
          rest suffix lift origin gEntry gCurrent gTrace atEntry ordinary fuel choice properChoice
            target supported
      have cutBounds := (cut.phase.mem_events event).mp cut.inside
      rw [phaseEq] at cutBounds
      have offset : gTrace.length = mappedTrace.length + (event.val - phase.low) := by
        rw [gDepth, cut.clock, ← mappedCursorDepth, phaseEq]
      have mappedRemaining := ProtocolState.remaining_le_instructionCount setup.program
        mappedCurrent.point
      have mappedEndBound := ProtocolState.commitEnd_le_remaining setup.program mappedCurrent.point
      have mappedPointEndpoint : instructionCount setup.program -
          ProtocolState.commitEnd setup.program mappedCurrent.point = phase.high := by
        rw [← savedEq]
        exact mappedEndpoint
      have insideG : gTrace.length + ProtocolState.commitEnd setup.program mappedCurrent.point <
          mappedTrace.length + ProtocolState.remaining setup.program mappedCurrent.point := by
        rw [offset]
        rw [phaseLow] at mappedRank
        omega
      obtain ⟨insideCurrent, insideState, _insideCommit, insideEnd, _insideRank⟩ :=
        setup.commitRecovery_prefix_inside_commit mappedCurrent
          (setup.proposalRecoveryEraseTrace mappedTrace) mappedCommitting
            (setup.proposalRecoveryEraseTrace gTrace)
              (setup.proposalRecoveryEraseTrace_prefix mappedToG)
                (by simpa only [setup.proposalRecoveryEraseTrace_length] using insideG)
      have insideEq : gCurrent = insideCurrent := Option.some.inj insideState
      have gEndpoint : instructionCount setup.program -
          ProtocolState.commitEnd setup.program gCurrent.point = phase.high := by
        rw [insideEq, insideEnd]
        exact mappedPointEndpoint
      have gRemaining := ProtocolState.remaining_le_instructionCount setup.program gCurrent.point
      have gEndBound := ProtocolState.commitEnd_le_remaining setup.program gCurrent.point
      have suffixLength : rest.length + 1 = phase.high - event.val := by
        change rest.length + 1 +
          ProtocolState.commitEnd setup.program gCurrent.saved = _ at distance
        rw [← sameEnd] at distance
        omega
      have forcedLength := congrArg List.length forcedWord
      simp only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
        List.length_append, List.length_reverse, forcedAttempt.joints_length,
        SourceProgram.CommitPrefix.length] at forcedLength
      have targetLength := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
        history.trace.length) forcedState
      change targetTrace.length = forcedTrace.length at targetLength
      have wholeDepth : targetTrace.length = mappedTrace.length + (phase.high - phase.low) := by
        omega
      have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
        intro state member
        obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
        exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
      have beforeOrdered := (phaseApplication_seedOrder implementation.runtime
        implementation.leaks).history nativeInitial implementation.horizon implementation.scheduler
          initialized ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler prior)
      have physicalProgress := phase_attempt_progress_of_prefix implementation.runtime
        implementation.leaks nativeMenu nativeInitial initialized implementation.horizon
          implementation.scheduler before reference prior referenceTrace retained beforeOrdered
      have canonicalMask : cut.cursor.current.excluded =
        reference.execution.application.entry.excluded := by
        have equal := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
          (setup.commitRecoveryPublic history.state).1) canonicalEq
        exact equal
      have gMask : gCurrent.excluded = before.execution.application.entry.excluded :=
        metadata.2.2.1.trans (cutMask.trans
          (canonicalMask.trans (congrArg RecoveryState.excluded
            (physicalProgress.2.2 finalAttempt)).symm))
      have targetMask : targetCurrent.excluded = before.execution.application.entry.excluded := by
        have states : targetCurrent = forcedLast := Option.some.inj (congrArg History.state
          forcedState)
        rw [states, forcedExcluded]
        exact gMask
      let segment := SourceProgram.commitPhase selected.residual.tail
      let blockLift : ProtocolState (segment.block.prepend segment.suffix) →
          ProtocolState setup.program := fun point => selected.residual.lift
            (cast (congrArg ProtocolState segment.reconstruct) point)
      have blockOrigin : ProtocolSuffix setup.program
          (segment.block.prepend segment.suffix) blockLift := by
        have transport {Γ : SourceCtx Player L} {O : Finset VarId}
            {left right : SourceProgram Player L Γ O} (equal : left = right)
            (lift : ProtocolState right → ProtocolState setup.program)
            (origin : ProtocolSuffix setup.program right lift) :
            ProtocolSuffix setup.program left
              (fun point => lift (cast (congrArg ProtocolState equal) point)) := by
          cases equal
          exact origin
        exact transport segment.reconstruct selected.residual.lift selected.origin
      have entryPoint : mappedCurrent.point = blockLift
          (ProtocolState.entry (segment.block.prepend segment.suffix) live) := by
        have transport {Γ : SourceCtx Player L} {O : Finset VarId}
            {left right : SourceProgram Player L Γ O} (equal : left = right)
            (config : SourceProgram.Config Player L Γ) :
            cast (congrArg ProtocolState equal) (ProtocolState.entry left config) =
              ProtocolState.entry right config := by
          cases equal
          rfl
        dsimp only [blockLift]
        rw [transport segment.reconstruct]
        exact mappedPoint
      have segmentGeometry := selected.commit_phase_geometry phase remaining installed commitment
        witness.order.frontier (operational.maximalPhases.suffix witness.suffix)
      have blockPositive : 0 < segment.block.length := by
        rw [segmentGeometry.1]
        exact Nat.sub_pos_of_lt phase.nonempty
      have blockEndpoint : ProtocolState.commitEnd setup.program mappedCurrent.saved ≤
          instructionCount segment.suffix := by
        rw [savedEq, entryPoint, blockOrigin.commitEnd_lift]
        rw [segment.block.commitEnd_entry_prepend segment.suffix segment.boundary]
      obtain ⟨wholeFinished, wholeExcluded, wholeAttempt, wholeAddresses, wholePath,
        wholeWord, wholeAddressWord, _wholeMonotone, _wholeClosed⟩ :=
        source_attempt_of_literal_window setup
          (setup.initialConfig setup.initialLaw.support_nonempty.choose)
          segment.block segment.suffix blockLift blockOrigin live mappedCurrent targetCurrent
          mappedTrace targetTrace mappedToTarget entryPoint
          (by rw [savedEq]; exact mappedCommitting) blockEndpoint blockPositive
          (by rw [segmentGeometry.1]; exact wholeDepth)
      have wholeSlot : named.val - before.execution.application.attempt.phase <
        wholeAttempt.joints.length := by
        rw [wholeAttempt.joints_length, segmentGeometry.1]
        omega
      obtain ⟨current, next, sourceTrace, sourceJoint, sourceLegal, sourceMoved, sourceKept,
        sourceDepth, sourceSemantic, sourceSaved, sourceGeneration, sourceRank⟩ :=
        source_commit_chunk_at_rank setup mappedCurrent mappedTrace mappedCommitting target
          mappedToTarget wholeAttempt.joints wholeWord
            (named.val - before.execution.application.attempt.phase) wholeSlot named.val
              (by rw [mappedRank]; omega) (by rw [mappedEndpoint]; exact namedBounds.2)
      have keptPrefix : TracePrefix sourceTrace targetTrace :=
        (TracePrefix.extend .refl sourceJoint sourceLegal sourceMoved).trans sourceKept
      have active : owner ∉ current.excluded := by
        have inherited := setup.commitRecovery_public_excluded_of_reaches
          (setup.proposalRecoveryEraseTrace_prefix keptPrefix).reachesWithin
        change current.excluded ⊆ targetCurrent.excluded at inherited
        intro member
        have entryMember : owner ∈ before.execution.application.entry.excluded := by
          rw [← targetMask]
          exact inherited member
        exact nativeRequest.2.2.2.2 (witness.order.coverage.inherited entryMember)
      refine ⟨current, sourceTrace, keptPrefix, sourceRank.symm,
        sourceGeneration.trans mappedGeneration, ?_, active, ?_⟩
      · rw [sourceSaved]
        exact mappedSavedRank
      · have forcedInstructions : setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace targetTrace) = forcedAttempt.joints.reverse ++
              setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace gTrace) := by
          have word := forcedWord
          have traceEq := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)) forcedState
          exact traceEq.trans word
        have targetGood := sourceReplay_good_of_proper_word setup who ⟨some gCurrent, gTrace⟩
          target good forcedAttempt.joints forcedInstructions forcedProper
        have sourceGood := source_good_prefix setup who sourceTrace targetTrace keptPrefix
          targetGood
        have fromMapped : TracePrefix mappedTrace sourceTrace :=
          (mappedToTarget.reachesWithin.ancestor_comparable keptPrefix.reachesWithin (by
            change mappedTrace.length ≤ sourceTrace.length
            rw [sourceDepth]; omega)).tracePrefix
        exact queryAt current sourceTrace keptPrefix fromMapped sourceDepth sourceRank.symm
          (sourceGeneration.trans mappedGeneration) (sourceSaved.trans savedEq) active sourceGood
  · obtain ⟨closing, ending, closingTrace, joint, legal, moved, fromBefore, toReference,
      sameAttempt, changed⟩ := sourceReplay_first_attempt_exit setup implementation
        before reference prior referenceTrace retained (Ne.symm finalAttempt)
    let endingTrace := closingTrace.extend joint legal moved
    have closingRetained : TracePrefix closingTrace referenceTrace :=
      (TracePrefix.extend .refl joint legal moved).trans toReference
    have sameControls := phaseProposal_same_attempt_archive_metadata setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        implementation.horizon implementation.scheduler before closing
    rw [← initialEq] at sameControls
    have sameControls := sameControls prior closingTrace fromBefore sameAttempt.symm
    have closingInstalled : closing.execution.application.phases = phase :: remaining :=
      sameControls.1.trans installed
    have closingRaw : ((nativeApplication).protocol
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace (some closing) := by
      rw [← initialEq]
      exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler closingTrace
    have realized : some ending ∈ ((nativeApplication).transition
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler (some closing) joint).support := by
      rw [← initialEq]
      exact moved
    obtain ⟨physical, _idle, normalized, finished, valid, _coverage, _excluded, _receipts,
      effect, stamp⟩ := phase_closed_transition_receipt_snapshot implementation.runtime
        implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
          implementation.horizon implementation.scheduler closing ending closingRaw joint
            realized phase (by rw [closingInstalled]; exact Option.mem_some_iff.mpr rfl) changed
    obtain ⟨sourceLast, closed, labeled, fuel, targetFirst, targetLast, targetPrior, targetEnd,
      targetEntry, targetFinished, targetExcluded, targetAttempt, targetMonotone, sourcePath,
      sourceWord, closedSelected, labeledKept, closedErase, targetInterval, targetEndToG,
      targetEndToTarget, targetPriorDepth, targetEndDepth, targetPoint, targetAtCommit,
      targetEndpoint, targetWord, targetClosed, targetImage, referenceStamp⟩ :=
      completedVisit lost restricted closing ending closingTrace endingTrace
        (by
          change TracePrefix closingTrace (closingTrace.extend joint legal moved)
          exact TracePrefix.extend (E := nativeProtocol) (prefixTrace := closingTrace)
            .refl joint legal moved) toReference phase remaining closingInstalled
          physical normalized finished commitment effect changed valid stamp
    have selectedEq := checkpointSelection_eq_of_attempt setup implementation operational
      before closing prior closingTrace fromBefore sameAttempt.symm
    have selectedDepth := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.trace.length) selectedEq
    have targetEntryEq : (⟨some targetFirst, targetPrior⟩ :
        setup.proposalRecoveryProtocol.History) = ⟨some mappedCurrent, mappedTrace⟩ :=
      (targetInterval.trans targetEndToTarget).eq_of_same_length mappedToTarget (by
        rw [targetPriorDepth]
        exact selectedDepth.symm.trans mappedLength.symm)
    have targetFirstEq : targetFirst = mappedCurrent :=
      Option.some.inj (congrArg History.state targetEntryEq)
    let closingWitness := (checkpointSelection setup implementation operational closingTrace).val
    have blockGeometry := closingWitness.checkpoint.commit_phase_geometry phase remaining
      closingInstalled commitment closingWitness.order.frontier
        (operational.maximalPhases.suffix closingWitness.suffix)
    have slotBound : named.val - before.execution.application.attempt.phase <
        targetAttempt.joints.length := by
      rw [targetAttempt.joints_length, blockGeometry.1]
      omega
    have targetCommit : ProtocolState.atCommit setup.program targetFirst.point = true := by
      rw [targetFirstEq]
      exact mappedCommitting
    have targetPosition : named.val = instructionCount setup.program -
        ProtocolState.remaining setup.program targetFirst.point +
          (named.val - before.execution.application.attempt.phase) := by
      rw [targetFirstEq, mappedRank]
      omega
    have targetWithin : named.val < instructionCount setup.program -
        ProtocolState.commitEnd setup.program targetFirst.saved := by
      rw [targetFirstEq, mappedEndpoint]
      exact namedBounds.2
    obtain ⟨current, next, sourceTrace, sourceJoint, sourceLegal, sourceMoved,
      sourceKept, sourceDepth, sourceSemantic, sourceSaved, sourceGeneration, sourceRank⟩ :=
      source_commit_chunk_at_rank setup targetFirst targetPrior targetCommit
        ⟨some targetLast, targetEnd⟩ targetInterval targetAttempt.joints targetWord
          (named.val - before.execution.application.attempt.phase) slotBound named.val
            targetPosition targetWithin
    have keptPrefix : TracePrefix sourceTrace targetTrace :=
      (TracePrefix.extend .refl sourceJoint sourceLegal sourceMoved).trans
        (sourceKept.trans targetEndToTarget)
    have generation : current.generation = before.execution.application.generation := by
      rw [sourceGeneration, targetFirstEq, mappedGeneration]
    have savedRank : instructionCount setup.program -
        ProtocolState.remaining setup.program current.saved =
          before.execution.application.attempt.phase := by
      rw [sourceSaved, targetFirstEq]
      exact mappedSavedRank
    have active : owner ∉ current.excluded := by
      let first := closingWitness.checkpoint
      let segment := SourceProgram.commitPhase first.residual.tail
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          segment.reconstruct.symm) first.embedding
      let blockLift : ProtocolState (segment.block.prepend segment.suffix) →
          ProtocolState setup.program := fun point => first.residual.lift
            (cast (congrArg ProtocolState segment.reconstruct) point)
      have blockOrigin : ProtocolSuffix setup.program
          (segment.block.prepend segment.suffix) blockLift := by
        have transport {Γ : SourceCtx Player L} {O : Finset VarId}
            {left right : SourceProgram Player L Γ O} (equal : left = right)
            (lift : ProtocolState right → ProtocolState setup.program)
            (origin : ProtocolSuffix setup.program right lift) :
            ProtocolSuffix setup.program left
              (fun point => lift (cast (congrArg ProtocolState equal) point)) := by
          cases equal
          exact origin
        exact transport segment.reconstruct first.residual.lift first.origin
      have embeddingRank : ∀ index, (embedding.event index).val =
          closing.execution.application.attempt.phase + index.val := by
        have transport {Γ : SourceCtx Player L} {O : Finset VarId}
            {left right : SourceProgram Player L Γ O} (equal : left = right)
            (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
              left)
            (low : Nat) (rank : ∀ index, (embedding.event index).val = low + index.val) :
            ∀ index, ((cast (congrArg (fun program => OutputEmbedding
              (inputLayout setup.context) (outputLayout setup.program) program) equal)
                embedding).event index).val = low + index.val := by
          cases equal
          exact rank
        exact transport segment.reconstruct.symm first.embedding _ first.compiled.rankEq
      have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
        intro state member
        obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
        exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
      have beforeOrdered := (phaseApplication_seedOrder implementation.runtime
        implementation.leaks).history nativeInitial implementation.horizon implementation.scheduler
          initialized ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler prior)
      have ownAccepted : ∀ (index : Fin (eventCount (segment.block.prepend segment.suffix))),
          index.val < named.val - before.execution.application.attempt.phase →
          ∀ payload, (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
            .binding owner payload →
          (sourceSnapshotState setup implementation target reference lost
            (phase.drain physical).native).accepted (.inr (embedding.event index)) ≠ none := by
        intro index earlier payload binding
        have eventRank := embeddingRank index
        have samePhase := congrArg CommitAttemptId.phase sameAttempt
        rw [samePhase] at eventRank
        have earlierInside : embedding.event index ∈ phase.events :=
          (phase.mem_events _).mpr ⟨by omega, by omega⟩
        obtain ⟨candidate, _owned, acceptedBefore, _read⟩ := phase_ready_earlier_binding_read
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
            (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
              counted (serviceGraph_revealRelaxedOrdered setup .concurrent) phase
                (by rw [installed]; rfl) owner named ty shape nativeRequest.2.2.1
                  nativeRequest.2.2.2.2 (embedding.event index) payload binding earlierInside (by
                    omega)
        have acceptedClosing := phase_prefix_accepted implementation.runtime implementation.leaks
          nativeMenu nativeInitial implementation.horizon implementation.scheduler before closing
            prior closingTrace fromBefore beforeOrdered sameAttempt.symm _ candidate acceptedBefore
        have acceptedPhysical := effect.accepted_preserved implementation.runtime
          implementation.leaks
          _ candidate acceptedClosing
        have acceptedDrained : (phase.drain physical).native.accepted
            (.inr (embedding.event index)) = some candidate := by
          rw [(phase.drain_tables physical).1]
          exact acceptedPhysical
        have acceptedAssigned : (sourceSnapshotState setup implementation target reference lost
            (phase.drain physical).native).accepted (.inr (embedding.event index)) = some
              candidate := by
          simpa only [sourceSnapshotState, State.swap_accepted] using acceptedDrained
        rw [acceptedAssigned]
        exact Option.some_ne_none candidate
      have activeEntry : owner ∉ targetFirst.excluded := by
        rw [targetFirstEq, mappedExcluded]
        intro member
        exact nativeRequest.2.2.2.2 (witness.order.coverage.inherited member)
      obtain ⟨surviving, survivingTrace, survivingKept, survivingLength, survives⟩ :=
        sourceReplay_attempt_survives_prefix setup targetAttempt segment.suffix embedding
          (sourceSnapshotState setup implementation target reference lost (phase.drain
            physical).native)
          blockLift blockOrigin targetFirst targetPrior ⟨some targetLast, targetEnd⟩ targetPoint rfl
          targetAtCommit targetEndpoint targetInterval targetWord owner activeEntry
          (named.val - before.execution.application.attempt.phase)
          (by simpa only [targetAttempt.joints_length] using slotBound) ownAccepted
            targetImage.tableReads
      have same : (⟨some surviving, survivingTrace⟩ : setup.proposalRecoveryProtocol.History) =
          ⟨some current, sourceTrace⟩ :=
        survivingKept.eq_of_same_length
          ((TracePrefix.extend .refl sourceJoint sourceLegal sourceMoved).trans sourceKept)
            (survivingLength.trans sourceDepth.symm)
      have states : surviving = current := Option.some.inj (congrArg History.state same)
      rwa [states] at survives
    refine ⟨current, sourceTrace, keptPrefix, sourceRank.symm, generation, savedRank, active, ?_⟩
    have sourceToG : TracePrefix sourceTrace g.trace :=
      (TracePrefix.extend .refl sourceJoint sourceLegal sourceMoved).trans
        (sourceKept.trans targetEndToG)
    have sourceGood := source_good_prefix setup who sourceTrace g.trace sourceToG good
    have priorLength : targetPrior.length = mappedTrace.length :=
      congrArg (fun history : setup.proposalRecoveryProtocol.History => history.trace.length)
        targetEntryEq
    have depth : sourceTrace.length = mappedTrace.length +
        (named.val - before.execution.application.attempt.phase) := by
      rw [sourceDepth, priorLength]
    have fromMapped : TracePrefix mappedTrace sourceTrace :=
      (mappedToTarget.reachesWithin.ancestor_comparable keptPrefix.reachesWithin
        (by
          change mappedTrace.length ≤ sourceTrace.length
          rw [depth]; omega)).tracePrefix
    have savedPoint : current.saved = mappedCurrent.point :=
      sourceSaved.trans ((congrArg CommitRecoveryState.saved targetFirstEq).trans savedEq)
    exact queryAt current sourceTrace keptPrefix fromMapped depth sourceRank.symm generation
      savedPoint
      active sourceGood

/-- A historical foreign callback reads its literal canonical source row.
The original focal goodness condition controls only the callback owner. -/
theorem sourceReplay_historical_query_binding
    (operational : implementation.Operational)
    (who : Player) (reference before : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix prior referenceTrace)
    (foreignGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner ⟨some reference, referenceTrace⟩)
    (owner : Player) (ownerForeign : owner ≠ who)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (acting : before.actor = some owner)
    (nativeRequest : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, named⟩)
    (historical : before.execution.application.attempt ≠ reference.execution.application.attempt)
    (current : CommitRecoveryState setup.program)
    (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (toTarget : TracePrefix sourceTrace
      (canonicalSource setup implementation operational ⟨some reference, referenceTrace⟩).trace)
    (generation : current.generation = before.execution.application.generation)
    (savedRank : instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved =
        before.execution.application.attempt.phase)
    (rank : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (survives : owner ∉ current.excluded) :
    phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
        implementation.plan owner named (before.execution.recall owner)
          (before.execution.observe nativeApplication owner) =
      some (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner sourceTrace)) := by
  classical
  let target := canonicalSource setup implementation operational ⟨some reference, referenceTrace⟩
  have targetGood := canonicalSource_foreignGood setup implementation operational who
    ⟨some reference, referenceTrace⟩ foreignGood
  have sourceGood := source_good_prefix setup who sourceTrace target.trace toTarget targetGood
  have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have counted := initialEq ▸ prior
  let witness := (checkpointSelection setup implementation operational prior).val
  let selected := witness.checkpoint
  let live := selected.source
  let mappedCurrent := CommitRecoveryState.atPoint
    (selected.residual.lift (ProtocolState.entry selected.residual.tail live))
      before.execution.application.entry.excluded before.execution.application.generation
  let mappedTrace : setup.proposalRecoveryProtocol.Trace (some mappedCurrent) :=
    setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive reference.execution.network.inputs))
        selected.trace
  have mappedToTarget : TracePrefix mappedTrace target.trace :=
    setup.proposalRecoveryLiftTrace_prefix _
      (checkpointSelection_prefix setup implementation operational before reference prior
        referenceTrace retained)
  obtain ⟨phase, remaining, installed, commitment, inside⟩ := phase_ready_binding_phase
    implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
          ((nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler counted)
            owner named ty shape nativeRequest.2.2.1
  have geometry := source_checkpoint_binding_interval setup implementation witness
    operational.maximalPhases phase remaining installed commitment
  have mappedCommitting : ProtocolState.atCommit setup.program mappedCurrent.point = true :=
    geometry.1
  have mappedRank : instructionCount setup.program -
      ProtocolState.remaining setup.program mappedCurrent.point =
        before.execution.application.attempt.phase := selected.saved_position
  have mappedSavedRank : instructionCount setup.program -
      ProtocolState.remaining setup.program mappedCurrent.saved =
        before.execution.application.attempt.phase := mappedRank
  have mappedEndpoint : instructionCount setup.program -
      ProtocolState.commitEnd setup.program mappedCurrent.saved = phase.high := geometry.2.2
  have phaseLow : before.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have namedBounds := (phase.mem_events named).mp inside
  obtain ⟨closing, ending, closingTrace, closingJoint, closingLegal, closingMoved, fromBefore,
    toReference, sameAttempt, changed⟩ := sourceReplay_first_attempt_exit setup implementation
      before reference prior referenceTrace retained (Ne.symm historical)
  let endingTrace := closingTrace.extend closingJoint closingLegal closingMoved
  have sameControls := phaseProposal_same_attempt_archive_metadata setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      implementation.horizon implementation.scheduler before closing
  rw [← initialEq] at sameControls
  have sameControls := sameControls prior closingTrace fromBefore sameAttempt.symm
  have closingInstalled : closing.execution.application.phases = phase :: remaining :=
    sameControls.1.trans installed
  have closingRaw := initialEq ▸ (nativeMenu).toRawTrace nativeInitial
    implementation.horizon implementation.scheduler closingTrace
  have realized : some ending ∈ ((nativeApplication).transition
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler (some closing) closingJoint).support := by
    rw [← initialEq]
    exact closingMoved
  have exitPrefix : TracePrefix closingTrace endingTrace := by
    change TracePrefix closingTrace (closingTrace.extend closingJoint closingLegal closingMoved)
    exact TracePrefix.extend (TracePrefix.refl : TracePrefix closingTrace closingTrace)
      closingJoint closingLegal closingMoved
  obtain ⟨physical, _idle, normalized, finished, _valid, _coverage, _excluded, _receipts,
    effect, _stamp⟩ := phase_closed_transition_receipt_snapshot implementation.runtime
      implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler closing ending closingRaw closingJoint
          realized phase (by rw [closingInstalled]; exact Option.mem_some_iff.mpr rfl) changed
  obtain ⟨last, closed, starting, labeled, _fuel, path, instructions, intervalLength,
    startKept, startErase, closedErase, labeledKept, _closedSelected, _labeledSelected,
    _closedMass⟩ := sourceReplayFactualCommitInterval setup implementation operational
      closing ending reference closingTrace endingTrace referenceTrace
        exitPrefix toReference
          phase remaining closingInstalled physical normalized finished commitment effect changed
  let first := (checkpointSelection setup implementation operational closingTrace).val.checkpoint
  have selectedEq := checkpointSelection_eq_of_attempt setup implementation operational
    before closing prior closingTrace fromBefore sameAttempt.symm
  have selectedDepth := congrArg
    (fun history : setup.commitRecoveryProtocol.History => history.trace.length) selectedEq
  have startSame : (⟨_, starting⟩ : setup.proposalRecoveryProtocol.History) =
      ⟨some mappedCurrent, mappedTrace⟩ :=
    (startKept.trans labeledKept).eq_of_same_length mappedToTarget (by
      have lengths := congrArg (fun path => path.length) startErase
      simpa only [setup.proposalRecoveryEraseTrace_length,
        setup.proposalRecoveryLiftTrace_length, mappedTrace] using lengths.trans selectedDepth.symm)
  have startLength : starting.length = mappedTrace.length :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History => history.trace.length)
      startSame
  have mappedLength : mappedTrace.length = first.trace.length := by
    simpa only [mappedTrace, setup.proposalRecoveryLiftTrace_length] using selectedDepth
  have wordLength : (first.commitInstructionWord (phase.drain physical).native).length =
      phase.high - phase.low := by
    rw [source_commit_instruction_word_length]
    have firstGeometry := source_checkpoint_binding_interval setup implementation
      (checkpointSelection setup implementation operational closingTrace).val
        operational.maximalPhases phase remaining closingInstalled commitment
    have bound := ProtocolState.remaining_le_instructionCount setup.program
      (first.residual.lift (ProtocolState.entry first.residual.tail first.source))
    have low := firstGeometry.2.1
    have high := firstGeometry.2.2
    change instructionCount setup.program - ProtocolState.remaining setup.program
      (first.residual.lift (ProtocolState.entry first.residual.tail first.source)) =
        phase.low at low
    change instructionCount setup.program - ProtocolState.commitEnd setup.program
      (first.residual.lift (ProtocolState.entry first.residual.tail first.source)) =
        phase.high at high
    omega
  have locate (state : CommitRecoveryState setup.program)
      (trace : setup.proposalRecoveryProtocol.Trace (some state))
      (kept : TracePrefix trace target.trace)
      (generation : state.generation = before.execution.application.generation)
      (position : Nat) (rank : position = instructionCount setup.program -
        ProtocolState.remaining setup.program state.point)
      (lower : phase.low ≤ position) (upper : position < phase.high) :
      TracePrefix mappedTrace trace ∧
        trace.length = mappedTrace.length + (position - phase.low) ∧
          first.trace.length ≤ trace.length ∧ trace.length < closed.length := by
    have firstRaw := setup.proposalRecoveryEraseTrace_prefix mappedToTarget
    have secondRaw := setup.proposalRecoveryEraseTrace_prefix kept
    have ordered : setup.commitRecoveryControl (some mappedCurrent) ≤
        setup.commitRecoveryControl (some state) := by
      change mappedCurrent.generation * (instructionCount setup.program + 1) +
          (instructionCount setup.program -
            ProtocolState.remaining setup.program mappedCurrent.point) + 1 ≤
        state.generation * (instructionCount setup.program + 1) +
          (instructionCount setup.program - ProtocolState.remaining setup.program state.point) + 1
      rw [generation, ← rank, mappedRank, phaseLow]
      exact Nat.add_le_add_right (Nat.add_le_add_left lower _) 1
    have path := setup.commitRecovery_ancestor_of_control_le firstRaw.reachesWithin
      secondRaw.reachesWithin ordered
    have lengthLe := path.tracePrefix.length_le
    simp only [setup.proposalRecoveryEraseTrace_length] at lengthLe
    have fromMapped : TracePrefix mappedTrace trace :=
      (mappedToTarget.reachesWithin.ancestor_comparable kept.reachesWithin lengthLe).tracePrefix
    have balance := setup.commitRecovery_same_generation_length path mappedCurrent state rfl rfl
      generation.symm
    simp only [setup.proposalRecoveryEraseTrace_length] at balance
    have firstBound := ProtocolState.remaining_le_instructionCount setup.program mappedCurrent.point
    have lastBound := ProtocolState.remaining_le_instructionCount setup.program state.point
    have duration : trace.length = mappedTrace.length + (position - phase.low) := by
      rw [phaseLow] at mappedRank
      omega
    have endLength := congrArg (fun path => path.length) closedErase
    simp only [setup.proposalRecoveryEraseTrace_length] at endLength
    refine ⟨fromMapped, duration, ?_, ?_⟩
    · rw [← mappedLength]
      exact fromMapped.length_le
    · rw [duration]
      rw [startLength, wordLength] at intervalLength
      omega
  obtain ⟨fromMapped, depth, _firstLower, _lastUpper⟩ := locate current sourceTrace toTarget
    generation named.val rank namedBounds.1 namedBounds.2
  rw [← phaseLow] at depth
  have mappedPoint : mappedCurrent.point = selected.residual.lift
      (ProtocolState.entry selected.residual.tail live) := rfl
  have savedEq : mappedCurrent.saved = mappedCurrent.point := rfl
  have mappedGeneration : mappedCurrent.generation = before.execution.application.generation := rfl
  have mappedExcluded : mappedCurrent.excluded = before.execution.application.entry.excluded := rfl
  have currentCommit := (source_binding_at_rank setup.program current.point named owner ty shape
    rank).1
  obtain ⟨savedTrace, savedKept, _savedBalance⟩ := setup.commitRecovery_attempt_entry current
    (setup.proposalRecoveryEraseTrace sourceTrace) currentCommit
  have savedToTarget := savedKept.trans (setup.proposalRecoveryEraseTrace_prefix toTarget)
  have sameEntry := setup.commitRecovery_ancestor_eq_of_control_eq
    (setup.proposalRecoveryEraseTrace_prefix mappedToTarget).reachesWithin
    savedToTarget.reachesWithin (by
      change mappedCurrent.generation * (instructionCount setup.program + 1) +
          (instructionCount setup.program - ProtocolState.remaining setup.program
            mappedCurrent.point) + 1 =
        current.generation * (instructionCount setup.program + 1) +
          (instructionCount setup.program - ProtocolState.remaining setup.program current.saved) + 1
      rw [mappedGeneration, generation, mappedRank, savedRank])
  have savedPoint : current.saved = mappedCurrent.point := by
    exact (congrArg CommitRecoveryState.point
      (Option.some.inj (congrArg History.state sameEntry))).symm
  have entryAgreement : selected.refs.Agrees live.state
      before.execution.application.current.native.config.store := by
    intro name cell source
    exact (selected.refs.get source).get?_preserved _ _ witness.stored _ (selected.agrees source)
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
  have beforeOrdered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history nativeInitial implementation.horizon implementation.scheduler
      initialized ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler prior)
  have closedKept : TracePrefix closed (setup.proposalRecoveryEraseTrace target.trace) := by
    have kept := setup.proposalRecoveryEraseTrace_prefix labeledKept
    rw [closedErase] at kept
    exact kept
  have assignedEarlier : ∀ (earlier : (serviceGraph setup .concurrent).EventId)
      (domain : L.Ty)
      (binding : (serviceGraph setup .concurrent).outputLayout earlier = .binding owner domain),
      before.execution.application.attempt.phase ≤ earlier.val → earlier.val < named.val →
      ∀ value : L.Val domain,
      sourceBindingAt setup before.execution.application.attempt earlier owner domain binding
        target.trace = some value →
      (⟨.inr earlier, binding⟩ : FieldRef (graphLayout setup.program) (.binding owner domain)).get?
        before.execution.application.current.native.config.store = some (.success value) := by
    intro earlier domain binding lower earlierRank value sourceRead
    have earlierInside : earlier ∈ phase.events :=
      (phase.mem_events earlier).mpr ⟨by omega, by omega⟩
    obtain ⟨candidate, _owned, accepted, physicalRead⟩ := phase_ready_earlier_binding_read
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler counted
          (serviceGraph_revealRelaxedOrdered setup .concurrent) phase (by rw [installed]; rfl)
            owner named ty shape nativeRequest.2.2.1 nativeRequest.2.2.2.2 earlier domain
              binding earlierInside earlierRank
    have noGenerated := no_generated_of_tracePrefix setup implementation owner retained
      (foreignGood owner ownerForeign)
    obtain ⟨old, proper⟩ := accepted_snapshot_value_of_no_generated_unusable setup implementation
      before prior before.execution.application.current.native (Or.inl rfl) owner noGenerated
        earlier domain binding candidate accepted
    rw [proper] at physicalRead
    have acceptedClosing := phase_prefix_accepted implementation.runtime implementation.leaks
      nativeMenu nativeInitial implementation.horizon implementation.scheduler before closing
        prior closingTrace fromBefore beforeOrdered sameAttempt.symm _ candidate accepted
    have acceptedPhysical := effect.accepted_preserved implementation.runtime implementation.leaks
      _ candidate acceptedClosing
    have acceptedDrained : (phase.drain physical).native.accepted (.inr earlier) =
        some candidate := by
      rw [(phase.drain_tables physical).1]
      exact acceptedPhysical
    obtain ⟨validBefore, catalogue⟩ := accepted_snapshot_catalogue setup implementation closing
      closingTrace before prior fromBefore before.execution.application.current.native (Or.inl rfl)
        owner domain ⟨.inr earlier, binding⟩ candidate accepted
    have fixed := validBefore.accepted_fixed (.inr earlier) candidate accepted
    have physicalCatalogue : physical.native.candidates.lookup candidate =
        closing.execution.application.current.native.candidates.lookup candidate := by
      rcases effect with ⟨_id, message, native, _found, _reached, handled, rfl⟩ |
        ⟨command, native, _reached, supported, rfl⟩
      · exact handle_lookup_of_not_fresh implementation.runtime _ native
          ⟨message.id, message.payload.packet.call⟩ candidate
            (by rw [catalogue]; exact fixed) handled
      · exact congrArg (fun candidates => candidates.lookup candidate)
          (environmentStep_tables implementation.runtime _ native command supported).2
    have drainedProper : (phase.drain physical).native.bindingResult candidate domain =
        .success old := by
      unfold State.bindingResult
      rw [(phase.drain_tables physical).2.1, physicalCatalogue, catalogue]
      exact proper
    obtain ⟨rowBefore, row, rowJoint, rowLegal, rowAfter, rowMoved, rowKept,
      rowGeneration, _rowSaved, rowPosition, rowData⟩ := sourceBindingAt_origin setup
        before.execution.application.attempt earlier owner domain binding target.trace value
          sourceRead
    obtain ⟨rowNext, _rawMoved, rfl⟩ := (PMF.mem_support_map_iff ..).mp rowMoved
    have rowActive : owner ∉ rowBefore.excluded := by
      cases chosen : rowJoint owner with
      | none => simp [chosen, phaseRecoveryBindingData] at rowData
      | some move => exact ((chosen ▸ rowLegal.2 owner).1).2
    have rowGeneration' : rowBefore.generation = before.execution.application.generation :=
      rowGeneration
    have rowPriorKept : TracePrefix row target.trace :=
      (TracePrefix.extend .refl rowJoint rowLegal rowMoved).trans rowKept
    obtain ⟨_fromMapped, _duration, lowerBound, upperBound⟩ := locate rowBefore row rowPriorKept
      rowGeneration' earlier.val rowPosition.symm (by omega) (by omega)
    obtain ⟨decodedBefore, decodedAfter, decodedTrace, decodedJoint, decodedLegal, decodedMoved,
      decodedKept, _depth, beforeInfo, _afterInfo, _own, decodedSaved, decodedGeneration,
      rawPhysical, _transported, _successful, _failed⟩ := sourceReplayPhysicalPairedRow setup first
        (phase.drain physical).native ⟨some last, closed⟩ path instructions who target target
          closedKept rfl targetGood targetGood rowBefore rowNext row rowJoint rowLegal rowMoved
            rowKept
            earlier owner domain binding rowPosition.symm lowerBound upperBound
    have metadata := source_information_metadata setup who ⟨some decodedBefore, decodedTrace⟩
      ⟨some rowBefore, row⟩ beforeInfo
    have decodedActive : owner ∉ decodedBefore.excluded := by
      rw [metadata.2.2.1]
      exact rowActive
    have data := rawPhysical decodedActive
    rw [acceptedDrained, Option.elim_some, Option.isNone_some, drainedProper] at data
    have decodedPosition : instructionCount setup.program -
        ProtocolState.remaining setup.program decodedBefore.point = earlier.val := by
      rw [(ProtocolState.MetadataEq.controls setup.program decodedBefore.point rowBefore.point
        metadata.1).1]
      exact rowPosition
    have decodedRead := sourceBindingAt_of_origin setup before.execution.application.attempt
      earlier owner domain binding decodedBefore decodedTrace decodedJoint decodedLegal
        (some decodedAfter) decodedMoved
          (decodedGeneration.trans (congrArg CommitAttemptId.generation sameAttempt))
          (by rw [decodedSaved, first.saved_position];
              exact congrArg CommitAttemptId.phase sameAttempt)
          decodedPosition (.success old, false) data target.trace decodedKept
    have same : old = value := Option.some.inj (decodedRead.symm.trans sourceRead)
    simpa only [same] using physicalRead
  have typed : phaseVirtualSourceView? setup .concurrent implementation.runtime
      implementation.leaks owner named (before.execution.observe nativeApplication owner) =
      some (ProtocolView.eraseHistory owner setup.program
        (ProtocolState.observe owner setup.program current.point)) := by
    obtain ⟨selectedIndex, selectedEvent, Δ, P, bindingName, fresh, guard, nextProgram, earlier,
      atEnd, reconstruct⟩ := selected.ready_binding_prefix witness.order.frontier phase remaining
        installed commitment named inside nativeRequest.2.2.1 owner ty shape
    let suffix := SourceProgram.commit bindingName owner fresh guard nextProgram
    let embedding := cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
      (outputLayout setup.program) program) reconstruct.symm) selected.embedding
    let lift : ProtocolState (earlier.prepend suffix) → ProtocolState setup.program :=
      fun point => selected.residual.lift (cast (congrArg ProtocolState reconstruct) point)
    have transport {Γ : SourceCtx Player L} {O : Finset VarId}
        {left right : SourceProgram Player L Γ O} (equal : left = right)
        (refs : ContextRefs (graphLayout setup.program) Γ)
        (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) right)
        (lift : ProtocolState right → ProtocolState setup.program)
        (origin : ProtocolSuffix setup.program right lift)
        (views : ProtocolViewSuffix setup.program right refs embedding lift) :
        PSigma fun _ : ProtocolSuffix setup.program left
          (fun point => lift (cast (congrArg ProtocolState equal) point)) =>
        ProtocolViewSuffix setup.program left refs
          (cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) program) equal.symm) embedding)
          (fun point => lift (cast (congrArg ProtocolState equal) point)) := by
      cases equal
      exact ⟨origin, views⟩
    obtain ⟨origin, views⟩ := transport reconstruct selected.refs selected.embedding
      selected.residual.lift selected.origin selected.views
    have entryTransport {Γ : SourceCtx Player L} {O : Finset VarId}
        {left right : SourceProgram Player L Γ O} (equal : left = right)
        (config : SourceProgram.Config Player L Γ) :
        cast (congrArg ProtocolState equal) (ProtocolState.entry left config) =
          ProtocolState.entry right config := by
      cases equal
      rfl
    have point : mappedCurrent.point = lift (ProtocolState.entry (earlier.prepend suffix) live) :=
      by
      dsimp only [lift]
      rw [entryTransport reconstruct]
      exact mappedPoint
    have ranking : ∀ index, (embedding.event index).val =
        before.execution.application.attempt.phase + index.val := by
      have castRank {Γ : SourceCtx Player L} {O : Finset VarId}
          {left right : SourceProgram Player L Γ O} (equal : left = right)
          (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
            right)
          (low : Nat) (rank : ∀ index, (embedding.event index).val = low + index.val) :
          ∀ index, ((cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) program) equal.symm) embedding).event index).val =
              low + index.val := by
        cases equal
        exact rank
      exact castRank reconstruct selected.embedding _ selected.compiled.rankEq
    let index : Fin (eventCount (earlier.prepend suffix)) :=
      ⟨earlier.length, by rw [← earlier.eventCount_prepend]; simp only [suffix, eventCount]; omega⟩
    have queryEvent : embedding.event index = named := by
      have castEvent {Γ : SourceCtx Player L} {O : Finset VarId}
          {left right : SourceProgram Player L Γ O} (equal : left = right)
          (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
            right)
          (first : Fin (eventCount left)) (second : Fin (eventCount right))
          (same : first.val = second.val) :
          (cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) program) equal.symm) embedding).event first =
              embedding.event second := by
        cases equal
        exact congrArg embedding.event (Fin.ext same)
      exact (castEvent reconstruct selected.embedding index selectedIndex atEnd.symm).trans
        selectedEvent
    have queriedRank := ranking index
    rw [queryEvent] at queriedRank
    have partialDepth : sourceTrace.length = mappedTrace.length + earlier.length := by
      dsimp only [index] at queriedRank
      omega
    let filled := fillCommitPrefix setup.program earlier suffix embedding
      before.execution.application.current.native.config.store live
    have endpoint : ProtocolState.commitEnd setup.program mappedCurrent.saved < instructionCount
      suffix := by
      rw [savedEq, point, origin.commitEnd_lift, earlier.commitEnd_suffix suffix live filled]
      have below := ProtocolState.commitEnd_lt_remaining suffix (ProtocolState.entry suffix filled)
        (by rfl)
      simpa only [ProtocolState.remaining_entry] using below
    obtain ⟨finished, excluded, attempt, endPoint, instructions⟩ :
        ∃ (finished : SourceProgram.Config Player L Δ) (excluded : Finset Player)
          (attempt : earlier.Attempt live mappedCurrent.excluded finished excluded),
          current.point = lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceTrace) =
            attempt.joints.reverse ++ setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace mappedTrace) := by
      by_cases positive : 0 < earlier.length
      · obtain ⟨finished, excluded, attempt, _addresses, _path, word, _addressWord,
          monotone, closed⟩ := source_attempt_of_literal_window setup
            (setup.initialConfig setup.initialLaw.support_nonempty.choose) earlier suffix lift
              origin
              live mappedCurrent current mappedTrace sourceTrace fromMapped point
                (by rw [savedEq]; exact mappedCommitting) endpoint.le positive partialDepth
        have remains : ProtocolState.commitEnd setup.program mappedCurrent.saved <
            ProtocolState.remaining setup.program
              (lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished))) := by
          rw [origin.remaining_lift, earlier.liftPoint_remaining, ProtocolState.remaining_entry]
          exact endpoint
        have unchanged := (mappedCurrent.install
          (lift (earlier.liftPoint suffix (ProtocolState.entry suffix finished)), excluded)
            monotone).close_eq_self_of_remaining_gt
              (by change ProtocolState.atCommit setup.program mappedCurrent.saved = true
                  rw [savedEq]; exact mappedCommitting) remains
        rw [unchanged] at closed
        exact ⟨finished, excluded, attempt, congrArg CommitRecoveryState.point closed, word⟩
      · have empty : earlier.length = 0 := by omega
        have histories := fromMapped.eq_of_length (by omega)
        have states : mappedCurrent = current := Option.some.inj (congrArg History.state histories)
        cases earlier with
        | nil =>
            refine ⟨live, mappedCurrent.excluded, .nil live mappedCurrent.excluded, ?_, ?_⟩
            · rw [← states]
              exact point
            · have words := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
                  setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace))
                    histories
              exact words.symm
        | commit => simp only [SourceProgram.CommitPrefix.length] at empty; omega
    have clock : before.execution.application.attempt.phase +
        instructionCount (earlier.prepend suffix) = instructionCount setup.program := by
      rw [reconstruct]
      simpa only [eventCount_eq_instructionCount] using selected.compiled.countEq
    have visible : ∀ {name cell} (source : HasVar Δ name cell), cellVisibleTo owner cell →
        ((commitBlockRefs setup.program earlier suffix embedding selected.refs).get source).get?
          before.execution.application.current.native.config.store =
              some (cellValue (finished.state.get source)) := by
      intro name cell source isVisible
      exact sourceReplay_attempt_visible_agreement setup attempt suffix embedding
        selected.refs
        lift origin views
          before.execution.application.current.native.config.store
          mappedCurrent current mappedTrace sourceTrace target toTarget point rfl
          (by rw [savedEq]; exact mappedCommitting) endpoint fromMapped instructions
          before.execution.application.attempt mappedGeneration mappedSavedRank
          before.execution.application.attempt.phase ranking clock who owner ownerForeign
          survives sourceGood (fun source _visible => entryAgreement source) (by
            intro earlierIndex earlierInside payload binding value read
            have earlierRank := ranking earlierIndex
            exact assignedEarlier (embedding.event earlierIndex) payload binding (by omega)
              (by dsimp only [index] at queriedRank; omega) value read) source isVisible
    have decoded := sourceReplay_visible_prefix_decode setup earlier suffix selected.refs embedding
      lift views
        before.execution.application.current.native.config finished owner visible index rfl
    rw [queryEvent, ← endPoint] at decoded
    apply sourceReplay_foreign_virtual_view setup implementation operational who owner ownerForeign
      before.execution named current sourceTrace survives sourceGood
    exact decoded
  have within : sourceTrace.length + ProtocolState.commitEnd setup.program mappedCurrent.point <
      mappedTrace.length + ProtocolState.remaining setup.program mappedCurrent.point := by
    have remainingBound := ProtocolState.remaining_le_instructionCount setup.program
      mappedCurrent.point
    have endBound := ProtocolState.commitEnd_le_remaining setup.program mappedCurrent.point
    have endpoint : instructionCount setup.program -
        ProtocolState.commitEnd setup.program mappedCurrent.point = phase.high := by
      rw [← savedEq]
      exact mappedEndpoint
    rw [depth]
    omega
  have archive := sourceReplay_selected_archive setup implementation operational before reference
    prior referenceTrace retained phase (by rw [installed]; rfl) commitment owner
      nativeRequest.2.2.2.2
  have mappedArchive : setup.proposalRecoveryArchive owner
      (setup.proposalRecoveryModel.infoOf owner mappedTrace) =
        PhaseProposal.sourceArchive before.execution.network.inputs := archive
  have proposals := (setup.proposalRecoveryArchive_eq_of_commit_window owner mappedCurrent
    mappedTrace mappedCommitting sourceTrace fromMapped within.le).trans mappedArchive
  have addresses : setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace mappedTrace) =
      before.execution.application.sourcePublicAddressWord implementation.plan
        before.execution.application.attempt.phase := by
    rw [setup.proposalRecoveryEraseTrace_lift]
    exact witness.chronology.addresses
  exact sourceReplay_query_of_literal_commit_window setup implementation operational before prior
    before prior owner named ty shape acting rfl rfl nativeRequest mappedCurrent mappedTrace rfl
      mappedCommitting mappedRank mappedExcluded mappedGeneration addresses current sourceTrace
        fromMapped within rank generation savedPoint survives typed proposals

end Vegas.PhaseProposalQualifiedBinding

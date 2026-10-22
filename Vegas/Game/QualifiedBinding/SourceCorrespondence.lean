/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.SourceImage
import Vegas.Game.RecoveryRetryChronology

/-! # Correspondence of selected source entries and factual commitment visits -/

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
theorem source_automatic_completed_owner
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (start : RecoveryState (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (completed : event ∈ (phase.drain start).native.config.cut.completed)
    (newly : event ∉ start.native.config.cut.completed) :
    ∃ owner, (serviceGraph setup .concurrent).actor? event = some owner ∧
      owner ∈ start.excluded ∧ event ∈ phase.events := by
  have along (last : RecoveryState (serviceGraph setup .concurrent))
      (path : Relation.ReflTransGen (phase.AutomaticStep) start last) :
      last.excluded = start.excluded ∧
        ∀ event, event ∈ last.native.config.cut.completed →
          event ∉ start.native.config.cut.completed →
            ∃ owner, (serviceGraph setup .concurrent).actor? event = some owner ∧
              owner ∈ start.excluded ∧ event ∈ phase.events := by
    induction path with
    | refl =>
        exact ⟨rfl, by intro event present absent; exact (absent present).elim⟩
    | @tail middle _ _ step ih =>
        obtain ⟨changed, eligible, rfl⟩ := step
        refine ⟨ih.1, ?_⟩
        intro event present absent
        by_cases old : event ∈ middle.native.config.cut.completed
        · exact ih.2 event old absent
        · obtain ⟨action, supported⟩ :=
            middle.completeAutomatic_step changed eligible.2
          have same := SuffixExclusionRecord.new_event_eq supported old present
          subst event
          obtain ⟨owner, actor, excluded⟩ := eligible.2.owned
          exact ⟨owner, actor, ih.1 ▸ excluded, eligible.1⟩
  exact (along _ (phase.drain_trace start)).2 event completed newly
omit [Fintype Player] in
theorem source_automatic_finished_event_owner
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (start : RecoveryState (serviceGraph setup .concurrent))
    (atStart : start.native.config.cut.IsPrefix phase.low)
    (finished : phase.Finished (phase.drain start)) :
    ∀ event ∈ phase.events, ∃ owner,
      (serviceGraph setup .concurrent).actor? event = some owner ∧
        owner ∈ start.excluded := by
  intro event member
  have absent : event ∉ start.native.config.cut.completed := by
    rw [atStart.2 event]
    exact Nat.not_lt.mpr ((phase.mem_events event).mp member).1
  obtain ⟨owner, acting, excluded, _⟩ :=
    source_automatic_completed_owner setup phase start event (finished member) absent
  exact ⟨owner, acting, excluded⟩
omit [Fintype Player] in
theorem source_automatic_finished_owners_subset
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (start : RecoveryState (serviceGraph setup .concurrent))
    (atStart : start.native.config.cut.IsPrefix phase.low)
    (finished : phase.Finished (phase.drain start)) :
    phase.owners ⊆ start.excluded := by
  intro owner member
  obtain ⟨event, inside, owned⟩ := Finset.mem_biUnion.mp member
  obtain ⟨actor, acting, excluded⟩ :=
    source_automatic_finished_event_owner setup phase start atStart finished event inside
  have same : owner = actor := by
    simpa only [acting, Option.toFinset_some, Finset.mem_singleton] using owned
  exact same.symm ▸ excluded

/- The factual native chronology is paired once with the target entry cut.
Each selected checkpoint carries the same target prefix and typed saved
agreement through callbacks; a changed attempt consumes its actual drained
source interval and the corresponding target Attempt. -/
theorem sourceReplayCorrespondence
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
        (sourceForcedBlock setup values who g choice).support) :
    SourceReplaySelectedAgreement (setup := setup) (implementation := implementation)
      operational who reference referenceTrace g targetCurrent targetTrace ∧
    SourceReplayCompletedVisit (setup := setup) (implementation := implementation)
      operational who reference referenceTrace g targetCurrent targetTrace := by
  classical
  let cut := entry.canonicalCut setup values implementation operational fullValues reference
    referenceTrace who acting event payload clean foreign
  let G : setup.proposalRecoveryProtocol.History := ⟨some targetCurrent, targetTrace⟩
  have canonicalEq : (⟨some cut.cursor.current, cut.cursor.trace⟩ :
      setup.proposalRecoveryProtocol.History) =
      canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩ := by
    exact entry.canonicalHistory
  have cutGood : setup.proposalRecoveryForeignGood who
      ⟨some cut.current, cut.trace⟩ :=
    PhaseProposalCanonicalBindingCut.foreignGood setup values implementation operational
      reference referenceTrace who event entry cut canonicalEq foreign
  obtain ⟨targetEntry, entryKept, _entryLength, entryInfo⟩ :=
    source_information_prefix setup who ⟨some cut.current, cut.trace⟩ g
      ⟨some cut.cursor.current, cut.cursor.trace⟩ sameInfo.symm cut.past
  have entryToG : TracePrefix targetEntry.trace G.trace := by
    have support := supported
    unfold sourceForcedBlock at support
    obtain ⟨middle, first, last⟩ := (PMF.mem_support_bind_iff ..).mp support
    have forward := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
      g middle first).tracePrefix
    have onward := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
      middle G last).tracePrefix
    exact entryKept.trans (forward.trans onward)
  have canonicalInfo : setup.proposalRecoveryModel.infoOf who
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace =
      setup.proposalRecoveryModel.infoOf who targetEntry.trace := by
    have aligned := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      setup.proposalRecoveryModel.infoOf who history.trace) canonicalEq
    exact aligned.symm.trans entryInfo
  let sourceCut : setup.proposalRecoveryProtocol.History := ⟨some cut.current, cut.trace⟩
  have canonicalToCut : TracePrefix
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace sourceCut.trace := by
    rw [← canonicalEq]
    exact cut.past
  have cutInfo : setup.proposalRecoveryModel.infoOf who sourceCut.trace =
      setup.proposalRecoveryModel.infoOf who g.trace := sameInfo.symm
  let SelectedImage := fun
      (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
      (before : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before)) =>
    let selected := (checkpointSelection setup implementation operational prior).val.checkpoint
    ∃ (mapped : setup.proposalRecoveryProtocol.History)
      (current : CommitRecoveryState setup.program)
      (live saved : SourceProgram.Config Player L selected.residual.context),
      TracePrefix mapped.trace targetEntry.trace ∧
      TracePrefix mapped.trace G.trace ∧
      mapped.trace.length = selected.trace.length ∧
      setup.proposalRecoveryModel.infoOf who mapped.trace =
        setup.proposalRecoveryModel.infoOf who
          (setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive reference.execution.network.inputs))
            selected.trace) ∧
      mapped.state = some current ∧
      current.point = selected.residual.lift
        (ProtocolState.entry selected.residual.tail live) ∧
      current.saved = selected.residual.lift
        (ProtocolState.entry selected.residual.tail saved) ∧
      current.excluded = before.execution.application.entry.excluded ∧
      current.generation = before.execution.application.generation ∧
      selected.refs.Agrees saved.state
        (sourceSnapshotState setup implementation G reference
          lost before.execution.application.entry.native).config.store
  have automaticSampleUnfinished
      (phase : RuntimePhase (serviceGraph setup .concurrent))
      (start : RecoveryState (serviceGraph setup .concurrent))
      (atStart : start.native.config.cut.IsPrefix phase.low)
      (sample : phase.kind = .sample) :
      ¬ phase.Finished (phase.drain start) := by
    intro finished
    let event : (serviceGraph setup .concurrent).EventId :=
      ⟨phase.low, lt_of_lt_of_le phase.nonempty phase.bounded⟩
    have member : event ∈ phase.events :=
      (phase.mem_events event).mpr ⟨le_refl _, phase.nonempty⟩
    obtain ⟨owner, acting, _⟩ :=
      source_automatic_finished_event_owner setup phase start atStart finished event member
    obtain ⟨payload, output⟩ :=
      sample ▸ phase.fields event (le_refl _) phase.nonempty
    have publicActorNone {Field : Type} [DecidableEq Field]
        {layout : Field → EventField Player L}
        {output : EventField Player L} {ty : L.Ty}
        (code : EventCode layout output) (shape : output = .publicData ty) :
        code.actor = none := by
      cases code <;> simp_all [EventCode.actor]
    have ownerless : (serviceGraph setup .concurrent).actor? event = none :=
      publicActorNone ((serviceGraph setup .concurrent).nodes event) output
    cases ownerless.symm.trans acting
  have automaticFinishedPublicFailures
      (phase : RuntimePhase (serviceGraph setup .concurrent))
      (start : RecoveryState (serviceGraph setup .concurrent))
      (atStart : start.native.config.cut.IsPrefix phase.low)
      (coverage : start.FailureCoverage)
      (ordered : (serviceGraph setup .concurrent).RevealRelaxedOrdered)
      (finished : phase.Finished (phase.drain start)) :
      ∀ event ∈ phase.events,
        ((serviceGraph setup .concurrent).outputLayout event).IsPublication →
        (phase.drain start).native.PublicFailure event := by
    have valid := RecoveryState.orderedPublicFailures_of_prefix phase.low
      start.excluded start atStart
    have drained := phase.orderedPublicFailures_drain phase.low start.excluded
      start valid coverage (Finset.Subset.rfl) ordered
    intro event member publication
    obtain ⟨owner, acting, excluded⟩ :=
      source_automatic_finished_event_owner setup phase start atStart finished event member
    exact drained event owner ((phase.mem_events event).mp member).1
      publication acting (finished member) (Or.inl excluded)
  have automaticFinishedBindingRows
      (phase : RuntimePhase (serviceGraph setup .concurrent))
      (start : RecoveryState (serviceGraph setup .concurrent))
      (atStart : start.native.config.cut.IsPrefix phase.low)
      (coverage : start.FailureCoverage)
      (valid : start.native.BindingInvariant)
      (finished : phase.Finished (phase.drain start))
      (event : (serviceGraph setup .concurrent).EventId)
      (member : event ∈ phase.events)
      (owner : Player) (payload : L.Ty)
      (binding : (serviceGraph setup .concurrent).outputLayout event =
        .binding owner payload)
      (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L)) :
      (⟨.inr event, binding⟩ : FieldRef
        (serviceGraph setup .concurrent).layout (.binding owner payload)).get?
          (sourceSnapshotState setup implementation G reference lost
            (phase.drain start).native).config.store = some .failure := by
    have actor := (serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding
    obtain ⟨actualOwner, actualActor, inherited⟩ :=
      source_automatic_finished_event_owner setup phase start atStart finished event member
    have ownerEq : actualOwner = owner := Option.some.inj (actualActor.symm.trans actor)
    have ownerInherited : owner ∈ start.excluded := ownerEq ▸ inherited
    have receipts := BindingReceiptOrder.of_prefix
      (inherited := start.excluded) coverage.receipts atStart
    have drainedReceipts := BindingReceiptOrder.congr receipts
      (phase.drain_tables start).1
    exact sourceReplayInheritedRow setup implementation G reference lost
      (phase.drain start).native event owner payload binding
        (phase.drain_bindingInvariant start valid) (finished member)
          phase.low start.excluded drainedReceipts
            ((phase.mem_events event).mp member).1 ownerInherited
  have automaticBindingReads
      {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      (block : SourceProgram.CommitPrefix Γ O Δ P)
      (entry : SourceProgram.Config Player L Γ)
      (excluded : Finset Player)
      (all : block.owners ⊆ excluded)
      (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (native : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (failed : ∀ index : Fin (eventCount (block.prepend suffix)),
        index.val < block.length → ∀ (owner : Player) (payload : L.Ty)
        (binding : outputLayout (block.prepend suffix) index =
          .binding owner payload),
        (⟨.inr (embedding.event index), (embedding.layout_eq index).trans binding⟩ :
          FieldRef (serviceGraph setup .concurrent).layout
            (.binding owner payload)).get? native.config.store = some .failure) :
      ∀ {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
        (attempt : block.Attempt entry excluded finished after),
        sourceAttemptTableReads setup attempt suffix embedding native := by
    induction block generalizing excluded with
    | nil => intro finished after attempt; cases attempt; trivial
    | @commit Γ O Δ P name owner payload fresh guard rest ih =>
        intro finished after attempt
        cases attempt with
        | active active choice missed missingFailure later =>
            exact (active (all (Finset.mem_insert_self _ _))).elim
        | excluded inactive later =>
            have head : (⟨.inr (embedding.event ⟨0, by
                simp only [SourceProgram.CommitPrefix.prepend, eventCount]
                omega⟩), (embedding.layout_eq ⟨0, by
                simp only [SourceProgram.CommitPrefix.prepend, eventCount]
                omega⟩).trans (by
                  simp only [SourceProgram.CommitPrefix.prepend, outputLayout,
                    Fin.mk_zero, Fin.cases_zero])⟩ :
                FieldRef (serviceGraph setup .concurrent).layout
                  (.binding owner payload)).get? native.config.store = some .failure := by
              exact failed ⟨0, by
                  simp only [SourceProgram.CommitPrefix.prepend, eventCount]
                  omega⟩ (by simp only [SourceProgram.CommitPrefix.length]; omega)
                    owner payload (by
                      simp only [SourceProgram.CommitPrefix.prepend, outputLayout,
                        Fin.mk_zero, Fin.cases_zero])
            have tailFailed : ∀ index : Fin (eventCount (rest.prepend suffix)),
                index.val < rest.length → ∀ (owner : Player) (payload : L.Ty)
                (binding : outputLayout (rest.prepend suffix) index =
                  .binding owner payload),
                (⟨.inr ((embedding.tail (rest.prepend suffix) (by
                    simp only [SourceProgram.CommitPrefix.prepend, eventCount])
                      (fun _ => rfl)).event index),
                    ((embedding.tail (rest.prepend suffix) (by
                      simp only [SourceProgram.CommitPrefix.prepend, eventCount])
                        (fun _ => rfl)).layout_eq index).trans binding⟩ :
                  FieldRef (serviceGraph setup .concurrent).layout
                    (.binding owner payload)).get? native.config.store = some .failure := by
              intro index inside owner payload binding
              simpa only [OutputEmbedding.tail, SourceProgram.CommitPrefix.prepend,
                outputLayout, Fin.cases_succ, Fin.cast_eq_self] using failed (Fin.succ index) (by
                  change index.val + 1 < rest.length + 1
                  omega) owner payload (by
                    simpa only [SourceProgram.CommitPrefix.prepend, outputLayout,
                      Fin.cases_succ]
                      using binding)
            change _ ∧ _
            exact ⟨head, ih (automaticCommit name owner _ entry) excluded
              (fun who member => all (Finset.mem_insert_of_mem member))
                suffix (embedding.tail (rest.prepend suffix) (by
                  simp only [SourceProgram.CommitPrefix.prepend, eventCount])
                    (fun _ => rfl)) tailFailed later⟩
  have mappedPrefixAtDepth
      (prior : setup.proposalRecoveryProtocol.History)
      (retained : TracePrefix prior.trace g.trace)
      (depth : Nat) (lower : prior.trace.length ≤ depth)
      (upper : depth ≤ g.trace.length) :
      ∃ (state : setup.proposalRecoveryProtocol.State)
        (trace : setup.proposalRecoveryProtocol.Trace state),
        TracePrefix prior.trace trace ∧ TracePrefix trace g.trace ∧
          trace.length = depth := by
    obtain ⟨state, trace, toG, length⟩ :=
      setup.proposalRecovery_prefix_at_depth g.trace depth upper
    have priorToTrace : TracePrefix prior.trace trace := by
      obtain ⟨earlier, atPrior, kept, sameLength⟩ :=
        setup.proposalRecovery_prefix_at_depth trace prior.trace.length (by
          rw [length]
          exact lower)
      have same := retained.eq_of_same_length (kept.trans toG) sameLength.symm
      cases same
      exact kept
    exact ⟨state, trace, priorToTrace, toG, length⟩
  have commonPrefixOrder
      (first second final : setup.proposalRecoveryProtocol.History)
      (firstKept : TracePrefix first.trace final.trace)
      (secondKept : TracePrefix second.trace final.trace)
      (depth : first.trace.length ≤ second.trace.length) :
      TracePrefix first.trace second.trace := by
    obtain ⟨state, prefixTrace, kept, length⟩ :=
      setup.proposalRecovery_prefix_at_depth second.trace
        first.trace.length depth
    have same := firstKept.eq_of_same_length
      (kept.trans secondKept) length.symm
    cases same
    exact kept
  have chronology : ∀ lost, SourceReplayLostRestricted setup implementation G reference
      who lost → ∀ {state : (nativeProtocol).State}
      (prior : (nativeProtocol).Trace state),
      match state with
      | none => True
      | some before => TracePrefix prior referenceTrace → SelectedImage lost before prior := by
    intro lost restricted state prior
    induction prior with
    | start => trivial
    | @extend before after earlier joint legal moved ih =>
        cases before with
        | none =>
            cases after with
            | none => trivial
            | some initialControl =>
                intro retained
                obtain ⟨_earlierSource, original, mapped, mappedEntryKept,
                  mappedToG, depth, information, mappedCurrent, mappedLive,
                  mappedSaved, mappedState, livePoint, savedPoint, mask, generation⟩ :=
                  sourceReplayTargetPrefix setup implementation operational who reference
                    referenceTrace targetEntry canonicalInfo G entryToG initialControl
                      (earlier.extend joint legal moved) retained
                rw [original] at information
                refine ⟨mapped, mappedCurrent, mappedLive, mappedSaved,
                  mappedEntryKept, mappedToG, ?_, information.symm, mappedState,
                  livePoint, savedPoint, mask, generation, ?_⟩
                · rw [original] at depth
                  simpa only [setup.proposalRecoveryLiftTrace_length] using depth
                · obtain ⟨theta, drawn, physical, historyEq⟩ :=
                    (checkpointSelectionStep setup implementation operational earlier
                      joint legal moved
                        (checkpointSelection setup implementation operational earlier)).property
                  have initialSelected : (⟨_, (checkpointSelection setup implementation
                      operational (earlier.extend joint legal moved)).val.checkpoint.trace⟩ :
                        setup.commitRecoveryProtocol.History) =
                      ⟨_, (RecoverySourceCheckpoint.initialized setup .concurrent
                        implementation.plan theta drawn).trace⟩ := by
                    exact historyEq
                  have targetBase :=
                    (source_initial_base_supported setup targetCurrent targetTrace).1
                  have initializedDepth :
                      (RecoverySourceCheckpoint.initialized setup .concurrent
                        implementation.plan theta drawn).trace.length = 1 := by
                    have raw := initialized_checkpoint_history setup .concurrent
                      implementation.plan theta drawn
                    have length := congrArg (fun history : setup.commitRecoveryProtocol.History =>
                      history.trace.length) raw
                    simpa only [RecoverySourceCheckpoint.initial, Trace.length] using length
                  have selectedDepth := congrArg
                    (fun history : setup.commitRecoveryProtocol.History =>
                      history.trace.length) initialSelected
                  have mappedDepth : mapped.trace.length = 1 := by
                    rw [original] at depth
                    simpa only [setup.proposalRecoveryLiftTrace_length,
                      selectedDepth, initializedDepth] using depth
                  have mappedInitial : ∃ initialValue : State L setup.context,
                      initialValue ∈ setup.initialLaw.support ∧
                        mappedCurrent = CommitRecoveryState.atPoint
                          (ProtocolState.entry setup.program
                            (setup.initialConfig initialValue)) ∅ 0 := by
                    rcases mapped with ⟨mappedEndpoint, mappedTrace⟩
                    cases mappedTrace with
                    | start => simp only [Trace.length] at mappedDepth; omega
                    | @extend before after prior joint legal reached =>
                        cases prior with
                        | start =>
                             change mappedEndpoint = some mappedCurrent at mappedState
                             change mappedEndpoint ∈ (setup.initialLaw.map fun initialValue =>
                              some (CommitRecoveryState.atPoint
                                (ProtocolState.entry setup.program
                                  (setup.initialConfig initialValue)) ∅ 0)).support at reached
                             obtain ⟨initialValue, supported, equation⟩ :=
                               (PMF.mem_support_map_iff ..).mp reached
                             exact ⟨initialValue, supported,
                               (Option.some.inj (equation.trans mappedState)).symm⟩
                        | extend earlier joint legal reached =>
                            simp only [Trace.length] at mappedDepth
                            omega
                  have mappedBase : mappedCurrent = CommitRecoveryState.atPoint
                      (ProtocolState.entry setup.program (setup.initialConfig
                        (ProtocolState.base setup.program targetCurrent.point))) ∅ 0 := by
                    obtain ⟨initialValue, _supported, mappedEq⟩ := mappedInitial
                    let typedMapped : setup.proposalRecoveryProtocol.Trace
                        (some mappedCurrent) :=
                      cast (congrArg setup.proposalRecoveryProtocol.Trace mappedState)
                        mapped.trace
                    have typedPrefix : TracePrefix typedMapped G.trace := by
                      rcases mapped with ⟨mappedStateValue, mappedTraceValue⟩
                      cases mappedState
                      exact mappedToG
                    have retainedRaw := setup.proposalRecoveryEraseTrace_prefix typedPrefix
                    have base := setup.commitRecovery_base_of_prefix mappedCurrent
                      (setup.proposalRecoveryEraseTrace typedMapped)
                      (by rw [mappedEq]; rfl)
                      (setup.proposalRecoveryEraseTrace targetTrace) retainedRaw
                    obtain ⟨endState, endEq, baseEq, _savedBase⟩ := base
                    have endpoint : endState = targetCurrent :=
                      (Option.some.inj endEq).symm
                    rw [endpoint, mappedEq] at baseEq
                    simp only [CommitRecoveryState.atPoint,
                      ProtocolState.base_entry, Setup.initialConfig] at baseEq
                    rw [baseEq]
                    exact mappedEq
                  have mappedSavedPoint :
                      (checkpointSelection setup implementation operational
                        (earlier.extend joint legal moved)).val.checkpoint.residual.lift
                          (ProtocolState.entry
                            (checkpointSelection setup implementation operational
                              (earlier.extend joint legal moved)).val.checkpoint.residual.tail
                              mappedSaved) =
                        ProtocolState.entry setup.program (setup.initialConfig
                          (ProtocolState.base setup.program targetCurrent.point)) := by
                    rw [mappedBase] at savedPoint
                    simpa only [CommitRecoveryState.atPoint] using savedPoint.symm
                  have initialDraw : theta = cut.theta := by
                    let labels := nativeArchiveLabels setup
                      (PhaseProposal.sourceArchive reference.execution.network.inputs)
                    let firstHistory : setup.proposalRecoveryProtocol.History :=
                      ⟨_, setup.proposalRecoveryLiftTrace labels
                        (checkpointSelection setup implementation operational
                          (earlier.extend joint legal moved)).val.checkpoint.trace⟩
                    have selectedKept := checkpointSelection_prefix setup implementation
                      operational initialControl reference (earlier.extend joint legal moved)
                        referenceTrace retained
                    have liftedKept := setup.proposalRecoveryLiftTrace_prefix labels
                      selectedKept
                    have firstKept : TracePrefix firstHistory.trace cut.cursor.trace := by
                      change TracePrefix firstHistory.trace
                        (canonicalSource setup implementation operational
                          ⟨some reference, referenceTrace⟩).trace at liftedKept
                      rw [← canonicalEq] at liftedKept
                      exact liftedKept
                    have firstLength : firstHistory.trace.length =
                        cut.initializerTrace.length := by
                       simp only [firstHistory, setup.proposalRecoveryLiftTrace_length,
                        selectedDepth, initializedDepth, cut.initializer_facts.2]
                    have firstEq := firstKept.eq_of_same_length cut.sourceRetained firstLength
                    have rawFirst := congrArg
                      (fun history : setup.commitRecoveryProtocol.History =>
                        (⟨history.state, setup.proposalRecoveryLiftTrace labels history.trace⟩ :
                          setup.proposalRecoveryProtocol.History))
                      (initialSelected.trans (initialized_checkpoint_history setup
                        .concurrent implementation.plan theta drawn))
                    have firstPoint : firstHistory.state = some
                        (CommitRecoveryState.atPoint
                          (ProtocolState.entry setup.program (setup.initialConfig theta))
                          ∅ 0) := by
                      exact congrArg (fun history : setup.proposalRecoveryProtocol.History =>
                        history.state) rawFirst
                    have cutPoint : cut.initializer = CommitRecoveryState.atPoint
                        (ProtocolState.entry setup.program (setup.initialConfig theta))
                          ∅ 0 := by
                      have sameState := congrArg
                        (fun history : setup.proposalRecoveryProtocol.History => history.state)
                          firstEq
                      exact Option.some.inj (sameState.symm.trans firstPoint)
                    have samePoint := congrArg CommitRecoveryState.point
                      (cutPoint.symm.trans cut.initializer_facts.1)
                    have sameBase := congrArg (ProtocolState.base setup.program) samePoint
                    simp only [CommitRecoveryState.atPoint,
                      ProtocolState.base_entry, Setup.initialConfig] at sameBase
                    exact sameBase
                  have assignedInitial := sourceReplayInitialFromCut setup values implementation
                    operational who reference referenceTrace event cut g sameInfo choice
                      targetCurrent targetTrace supported lost
                  have initialPhysical : initialControl.execution.application =
                      PhaseRuntimeState.initial implementation.plan
                        (encodeInputs cut.theta) := by
                    rw [← initialDraw]
                    exact physical
                  let targetBaseValue := ProtocolState.base setup.program targetCurrent.point
                  let rawTarget := RecoverySourceCheckpoint.initial setup .concurrent
                    implementation.plan targetBaseValue
                      (source_initial_base_supported setup targetCurrent targetTrace).1
                  let selected := (checkpointSelection setup implementation operational
                    (earlier.extend joint legal moved)).val.checkpoint
                  have initialPhaseZero
                      (inputs : (serviceGraph setup .concurrent).Inputs) :
                      (PhaseRuntimeState.initial implementation.plan inputs).attempt.phase =
                        0 := by
                    rw [phaseInitial_eq_raw]
                    change PhaseRuntimeState.phaseLow implementation.plan.phases = 0
                    cases phases : implementation.plan.phases with
                    | nil =>
                        simpa only [PhaseRuntimeState.phaseLow, List.head?_nil,
                          Option.map_none, Option.getD_none] using
                            implementation.plan.empty phases
                    | cons first rest =>
                        simpa only [PhaseRuntimeState.phaseLow, phases,
                          List.head?_cons, Option.map_some, Option.getD_some] using
                            implementation.plan.first first (by simp only [phases,
                              List.head?_cons, Option.mem_some_iff])
                  have phaseZero : initialControl.execution.application.attempt.phase = 0 := by
                    rw [initialPhysical]
                    exact initialPhaseZero (encodeInputs cut.theta)
                  have rawPhaseZero := initialPhaseZero (encodeInputs targetBaseValue)
                  rw [phaseInitial_eq_raw] at rawPhaseZero
                  have samePhase := phaseZero.trans rawPhaseZero.symm
                  have residualEq := selected.residual_eq_of_phase_eq rawTarget samePhase
                  have refsEq := sourceReplayCheckpointRefsEq setup selected rawTarget samePhase
                  have transportConfig {left right : ResidualProgram setup.program}
                      (equal : left = right)
                      (origin : ProtocolSuffix setup.program left.tail left.lift)
                      (source : SourceProgram.Config Player L left.context)
                      (result : SourceProgram.Config Player L right.context)
                      (point : left.lift (ProtocolState.entry left.tail source) =
                        right.lift (ProtocolState.entry right.tail result)) :
                      cast (congrArg (fun residual : ResidualProgram setup.program =>
                        SourceProgram.Config Player L residual.context) equal) source =
                          result := by
                    cases equal
                    exact ProtocolState.entry_injective left.tail
                      (sourceReplaySuffixInjective setup origin point)
                  have savedConfig :
                      cast (congrArg (fun residual : ResidualProgram setup.program =>
                        SourceProgram.Config Player L residual.context) residualEq) mappedSaved =
                          rawTarget.source := by
                    apply transportConfig residualEq selected.origin mappedSaved rawTarget.source
                    exact mappedSavedPoint
                  have initialAssignedAtControl :
                      sourceSnapshotAssignment setup implementation G reference lost
                        initialControl.execution.application =
                          PhaseRuntimeState.initial implementation.plan
                            (encodeInputs targetBaseValue) := by
                    rw [initialPhysical]
                    exact assignedInitial
                  have assignedStore := congrArg
                    (fun state : PhaseRuntimeState (serviceGraph setup .concurrent) =>
                      state.entry.native.config.store) initialAssignedAtControl
                  change (sourceSnapshotState setup implementation G reference lost
                    initialControl.execution.application.entry.native).config.store =
                      (PhaseRuntimeState.initial implementation.plan
                        (encodeInputs targetBaseValue)).entry.native.config.store
                    at assignedStore
                  have targetStore :
                      (PhaseRuntimeState.initial implementation.plan
                        (encodeInputs targetBaseValue)).entry.native.config.store =
                          (EventGraphRuntime.State.initial
                            (encodeInputs targetBaseValue)).config.store := by
                    rw [phaseInitial_eq_raw]
                  have transportAgrees {left right : ResidualProgram setup.program}
                      (equal : left = right)
                      (leftRefs : ContextRefs (graphLayout setup.program) left.context)
                      (rightRefs : ContextRefs (graphLayout setup.program) right.context)
                      (sameRefs : cast (congrArg
                        (fun residual : ResidualProgram setup.program =>
                          ContextRefs (graphLayout setup.program) residual.context)
                            equal) leftRefs = rightRefs)
                      (leftSource : SourceProgram.Config Player L left.context)
                      (rightSource : SourceProgram.Config Player L right.context)
                      (sameSource : cast (congrArg
                        (fun residual : ResidualProgram setup.program =>
                          SourceProgram.Config Player L residual.context)
                            equal) leftSource = rightSource)
                      (store : Store (graphLayout setup.program)) :
                      rightRefs.Agrees rightSource.state store →
                        leftRefs.Agrees leftSource.state store := by
                    cases equal
                    cases sameRefs
                    cases sameSource
                    exact id
                  have rawInitialAgreement : rawTarget.refs.Agrees rawTarget.source.state
                      (EventGraphRuntime.State.initial (graph := serviceGraph setup .concurrent)
                        (encodeInputs targetBaseValue)).config.store := by
                    intro name cell source
                    exact rawTarget.agrees source
                  have mappedAgreement : selected.refs.Agrees mappedSaved.state
                      (EventGraphRuntime.State.initial (graph := serviceGraph setup .concurrent)
                        (encodeInputs targetBaseValue)).config.store := by
                    intro name cell source
                    exact transportAgrees residualEq selected.refs rawTarget.refs refsEq
                       mappedSaved rawTarget.source savedConfig _ rawInitialAgreement source
                  intro name cell source
                  have literal := mappedAgreement source
                  rw [← targetStore, ← assignedStore] at literal
                  exact literal
        | some previous =>
            cases after with
            | none => trivial
            | some next =>
                intro retained
                have earlierKept : TracePrefix earlier referenceTrace :=
                  (TracePrefix.extend (TracePrefix.refl (prefixTrace := earlier))
                    joint legal moved).trans retained
                obtain ⟨priorMapped, priorCurrent, priorLive, priorSaved,
                  priorEntryKept, priorKept, priorDepth, _priorInfo, priorState, priorPoint,
                  priorSavedPoint, priorMask, priorGeneration, priorAgrees⟩ := ih earlierKept
                obtain ⟨_earlierSource, nextOriginal, nextMapped, nextEntryKept,
                  nextKept, nextDepth, nextInfo, nextCurrent, nextLive,
                  nextSaved, nextState, nextPoint, nextSavedPoint, nextMask,
                  nextGeneration⟩ := sourceReplayTargetPrefix setup implementation operational
                    who reference referenceTrace targetEntry canonicalInfo G entryToG next
                      (earlier.extend joint legal moved) retained
                rw [nextOriginal] at nextInfo
                by_cases same : previous.execution.application.attempt =
                    next.execution.application.attempt
                · have selected := sourceReplaySameAttemptSelectedEntry setup implementation
                    operational previous next earlier (earlier.extend joint legal moved)
                      (TracePrefix.extend (TracePrefix.refl (prefixTrace := earlier))
                        joint legal moved) same G priorMapped nextMapped priorKept nextKept
                          priorDepth (by
                            rw [nextOriginal] at nextDepth
                            simpa only [setup.proposalRecoveryLiftTrace_length]
                              using nextDepth) priorCurrent nextCurrent priorState nextState
                              priorLive nextLive priorSaved nextSaved priorPoint nextPoint
                              priorSavedPoint nextSavedPoint reference lost
                                  priorAgrees
                  refine ⟨nextMapped, nextCurrent, nextLive, nextSaved,
                    nextEntryKept, nextKept, ?_, nextInfo.symm, nextState,
                    nextPoint, nextSavedPoint, nextMask,
                    nextGeneration, selected.2.2.2⟩
                  rw [nextOriginal] at nextDepth
                  simpa only [setup.proposalRecoveryLiftTrace_length] using nextDepth
                · refine ⟨nextMapped, nextCurrent, nextLive, nextSaved,
                    nextEntryKept, nextKept,
                    by
                      rw [nextOriginal] at nextDepth
                      simpa only [setup.proposalRecoveryLiftTrace_length] using nextDepth,
                    nextInfo.symm, nextState, nextPoint, nextSavedPoint, nextMask,
                    nextGeneration, ?_⟩
                  let inputs := setup.initialLaw.map encodeInputs
                  have initialEq : nativeInitial =
                      inputs.map (PhaseRuntimeState.initial implementation.plan) := by
                    simp only [ReservedConcurrentImplementation.initial, inputs,
                      PMF.map_comp, Function.comp_def]
                  have rawTrace := (nativeMenu).toRawTrace nativeInitial
                    implementation.horizon implementation.scheduler earlier
                  rw [initialEq] at rawTrace
                  have rawMoved : some next ∈ ((nativeApplication).transition
                      (inputs.map (PhaseRuntimeState.initial implementation.plan))
                        implementation.horizon implementation.scheduler
                          (some previous) joint).support := by
                    rw [← initialEq]
                    exact moved
                  obtain ⟨phase, installed⟩ : ∃ phase : RuntimePhase
                      (serviceGraph setup .concurrent),
                      phase ∈ previous.execution.application.phases.head? := by
                    have along : ∀ {state : (nativeProtocol).State}
                        {trace : (nativeProtocol).Trace state},
                        TracePrefix (earlier.extend joint legal moved) trace →
                        ∃ current : (nativeApplication).Control, state = some current ∧
                          current.execution.application.phases <:+
                            next.execution.application.phases := by
                      intro state trace kept
                      induction kept with
                      | refl => exact ⟨next, rfl, List.suffix_refl _⟩
                      | @extend source target prior _kept actions available reached ih =>
                          obtain ⟨middle, rfl, suffix⟩ := ih
                          have actual : target ∈ ((nativeApplication).transition
                              nativeInitial implementation.horizon implementation.scheduler
                                (some middle) actions).support := reached
                          obtain ⟨future, rfl, _recalled⟩ :=
                            (nativeApplication).transition_recall_prefix nativeInitial
                              implementation.horizon implementation.scheduler middle target
                                actions actual
                          have step := (phaseApplication_phaseSuffix implementation.runtime
                            implementation.leaks).transition nativeInitial
                              implementation.horizon implementation.scheduler middle future
                                actions actual
                          exact ⟨future, rfl, step.trans suffix⟩
                    obtain ⟨sameReference, referenceEq, suffix⟩ := along retained
                    have exactReference := Option.some.inj referenceEq
                    subst sameReference
                    have activeReference : reference.execution.application.phases ≠ [] := by
                      intro empty
                      have installed := entry.installed
                      simp only [empty, List.head?_nil] at installed
                      cases installed
                    have afterActive : next.execution.application.phases ≠ [] := by
                      intro empty
                      have referenceEmpty := List.suffix_nil.mp (empty ▸ suffix)
                      exact activeReference referenceEmpty
                    have step := (phaseApplication_phaseSuffix implementation.runtime
                      implementation.leaks).transition
                        (inputs.map (PhaseRuntimeState.initial implementation.plan))
                          implementation.horizon implementation.scheduler previous next joint
                            rawMoved
                    have beforeActive : previous.execution.application.phases ≠ [] := by
                      intro empty
                      exact afterActive (List.suffix_nil.mp (empty ▸ step))
                    cases phases : previous.execution.application.phases with
                    | nil => exact (beforeActive phases).elim
                    | cons actual remaining =>
                         exact ⟨actual, by simp only [List.head?_cons,
                          Option.mem_some_iff]⟩
                  obtain ⟨physical, idle, normalized, finished, binding, coverage,
                      excluded, receipts, effect, stamp⟩ :=
                    phase_closed_transition_receipt_snapshot implementation.runtime
                      implementation.leaks implementation.plan inputs implementation.horizon
                        implementation.scheduler previous next rawTrace joint rawMoved phase
                          installed (Ne.symm same)
                  let first := (checkpointSelection setup implementation
                    operational earlier).val
                  let labels := nativeArchiveLabels setup
                    (PhaseProposal.sourceArchive reference.execution.network.inputs)
                  let originalStart : CommitRecoveryState setup.program :=
                    CommitRecoveryState.atPoint
                      (first.checkpoint.residual.lift
                        (ProtocolState.entry first.checkpoint.residual.tail
                          first.checkpoint.source))
                      previous.execution.application.entry.excluded
                      previous.execution.application.generation
                  let sourceStart : setup.proposalRecoveryProtocol.History :=
                    ⟨some originalStart,
                      setup.proposalRecoveryLiftTrace labels first.checkpoint.trace⟩
                  have sourceStartKept : TracePrefix sourceStart.trace
                      (canonicalSource setup implementation operational
                        ⟨some reference, referenceTrace⟩).trace := by
                    have selectedKept := checkpointSelection_prefix setup implementation
                      operational previous reference earlier referenceTrace earlierKept
                    exact setup.proposalRecoveryLiftTrace_prefix labels selectedKept
                  obtain ⟨remaining, installedEq⟩ :=
                    List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
                  change (checkpointSelection setup implementation operational
                    (earlier.extend joint legal moved)).val.checkpoint.refs.Agrees
                      nextSaved.state
                        (sourceSnapshotState setup implementation G reference lost
                          next.execution.application.entry.native).config.store
                  have transportOrigin {Γ : SourceCtx Player L} {O : Finset VarId}
                      {left right : SourceProgram Player L Γ O}
                      (equal : left = right)
                      (lift : ProtocolState right → ProtocolState setup.program)
                      (origin : ProtocolSuffix setup.program right lift) :
                      ProtocolSuffix setup.program left
                        (fun point =>
                          lift (cast (congrArg ProtocolState equal) point)) := by
                    cases equal
                    exact origin
                  have transportCompiled
                      {Γ : SourceCtx Player L} {O : Finset VarId}
                      {left right : SourceProgram Player L Γ O}
                      (equal : left = right)
                      (source : SourceProgram.Config Player L Γ)
                      (refs : ContextRefs (graphLayout setup.program) Γ)
                      (registry : Registry Γ)
                      (embedding : OutputEmbedding (inputLayout setup.context)
                        (outputLayout setup.program) right)
                      (before : ContextRefsBefore refs embedding)
                      (offset : Nat)
                      (compiled : CompiledSuffix setup.program right refs
                        source.revelations registry embedding before offset)
                      (aligned : CompiledReadoutSuffix setup.program right refs
                        embedding)
                      (lift : ProtocolState right → ProtocolState setup.program)
                      (views : ProtocolViewSuffix setup.program right refs
                        embedding lift) :
                      ∃ (translated : OutputEmbedding (inputLayout setup.context)
                          (outputLayout setup.program) left)
                        (translatedBefore : ContextRefsBefore refs translated),
                        translated = cast (congrArg (fun program =>
                          OutputEmbedding (inputLayout setup.context)
                            (outputLayout setup.program) program) equal.symm)
                              embedding ∧
                        CompiledSuffix setup.program left refs
                          source.revelations registry translated translatedBefore
                            offset ∧
                        CompiledReadoutSuffix setup.program left refs translated ∧
                        Nonempty (ProtocolViewSuffix setup.program left refs
                          translated (fun point =>
                            lift (cast (congrArg ProtocolState equal) point))) := by
                    cases equal
                    exact ⟨embedding, before, rfl, compiled, aligned, ⟨views⟩⟩
                  have transportEntry {Γ : SourceCtx Player L} {O : Finset VarId}
                      {left right : SourceProgram Player L Γ O}
                      (equal : left = right)
                      (entry : SourceProgram.Config Player L Γ) :
                      cast (congrArg ProtocolState equal)
                          (ProtocolState.entry left entry) =
                        ProtocolState.entry right entry := by
                    cases equal
                    rfl
                  have installCongr
                      {left right : CommitRecoveryState setup.program}
                      (equal : left = right)
                      (point : ProtocolState setup.program)
                      (excluded : Finset Player)
                      (grows : left.excluded ⊆ excluded) :
                      (left.install (point, excluded) grows).close =
                        (right.install (point, excluded)
                          (by rw [← equal]; exact grows)).close := by
                    cases equal
                    rfl
                  have castOwners
                      {Γ : SourceCtx Player L} {O : Finset VarId}
                      {left right : SourceProgram Player L Γ O}
                      (equal : left = right)
                      (point : ProtocolState left) :
                      ProtocolState.commitOwners right
                          (cast (congrArg ProtocolState equal) point) =
                        ProtocolState.commitOwners left point := by
                    cases equal
                    rfl
                  have castHistory
                      {Γ : SourceCtx Player L} {O : Finset VarId}
                      {left right : SourceProgram Player L Γ O}
                      (equal : left = right)
                      (point : ProtocolState left) :
                      ProtocolState.history right
                        (cast (congrArg ProtocolState equal) point) =
                        ProtocolState.history left point := by
                    cases equal
                    rfl
                  have castAutomatic
                      {Γ : SourceCtx Player L} {O : Finset VarId}
                      {left right : SourceProgram Player L Γ O}
                      (equal : left = right) (point : ProtocolState left) :
                      cast (congrArg ProtocolState equal)
                          (ProtocolState.automaticCommitBlock left point) =
                        ProtocolState.automaticCommitBlock right
                          (cast (congrArg ProtocolState equal) point) := by
                    cases equal
                    rfl
                  have bindingRecord :=
                    phaseBindingRecord_history implementation.runtime
                      implementation.leaks implementation.plan inputs
                        implementation.horizon implementation.scheduler rawTrace
                  have savedBinding := bindingRecord.saved
                  have savedAccepted :=
                    phaseAcceptedCheckpoint_history implementation.runtime
                      implementation.leaks implementation.plan inputs
                        implementation.horizon implementation.scheduler rawTrace
                  have savedStore :=
                    phaseStoredCheckpoint_history implementation.runtime
                      implementation.leaks implementation.plan inputs
                        implementation.horizon implementation.scheduler rawTrace
                  have rawStore : KeepsStore
                      previous.execution.application.current.native physical.native := by
                    rcases effect with ⟨_id, message, native, _found, _reached,
                      handled, rfl⟩ | ⟨command, native, _reached, supported, rfl⟩
                    · intro field value stored
                      change native.config.store field = some value
                      exact handle_store_of_some implementation.runtime _ native
                        ⟨message.id, message.payload.packet.call⟩ handled
                          field value stored
                    · intro field value stored
                      change native.config.store field = some value
                      exact environmentStep_store_of_some implementation.runtime _ native
                        command supported field value stored
                  have oldStore : KeepsStore previous.execution.application.entry.native
                      (phase.drain physical).native := by
                    intro field value stored
                    exact phase.drain_keepsStore physical field value
                      (rawStore field value (savedStore field value stored))
                  have castOptionNone {first second : EventField Player L}
                      (equal : first = second) :
                      cast (congrArg (fun kind : EventField Player L => Option kind.Value) equal)
                        (none : Option first.Value) = (none : Option second.Value) := by
                    cases equal
                    rfl
                  have oldEntryAgrees : first.checkpoint.refs.Agrees priorSaved.state
                      (sourceSnapshotState setup implementation G reference lost
                        (phase.drain physical).native).config.store := by
                    apply sourceReplayEntryAgreesOfPreserved setup implementation
                      first.checkpoint.refs priorSaved G reference lost
                        previous.execution.application.entry.native
                          (phase.drain physical).native priorAgrees
                    · intro name cell source
                      let field := (first.checkpoint.refs.get source).field
                      have occupied := first.checkpoint.agrees source
                      cases stored :
                          previous.execution.application.entry.native.config.store
                            field with
                      | none =>
                          have absent : (first.checkpoint.refs.get source).get?
                              previous.execution.application.entry.native.config.store =
                                none := by
                            unfold FieldRef.get?
                            rw [stored]
                            have castNone {α β : Type} (equal : α = β) :
                                cast (congrArg Option equal) (none : Option α) =
                                  (none : Option β) := by
                              cases equal
                              rfl
                            exact castNone (congrArg EventField.Value
                              (first.checkpoint.refs.get source).layout_eq)
                          rw [absent] at occupied
                          cases occupied
                      | some value =>
                          exact (oldStore field value stored).symm
                    · intro name cell source owner payload shape value successful
                      let field := (first.checkpoint.refs.get source).field
                      have read : (⟨field, shape⟩ : EventGraph.FieldRef
                          (serviceGraph setup .concurrent).layout
                            (.binding owner payload)).get?
                            previous.execution.application.entry.native.config.store =
                              some (.success value) := by
                        change cast (congrArg
                            (fun kind : EventField Player L => Option kind.Value) shape)
                          (previous.execution.application.entry.native.config.store
                            field) = some (.success value)
                        rw [successful]
                        have cancel {α β : Type} (equal : α = β) (item : β) :
                            cast (congrArg Option equal)
                              (some (cast equal.symm item)) = some item := by
                          cases equal
                          rfl
                        exact cancel (congrArg EventField.Value shape) (.success value)
                      obtain ⟨candidate, present, _owned, _openable⟩ :=
                        savedBinding.success_provenance ⟨field, shape⟩ value read
                      have active := savedAccepted field candidate present
                      have retained := effect.accepted_preserved
                        implementation.runtime implementation.leaks field candidate
                          active
                      have drainedAccepted : (phase.drain physical).native.accepted
                          field = some candidate := by
                        rw [(phase.drain_tables physical).1]
                        exact retained
                      exact present.trans drainedAccepted.symm
                  have revealMasksEqual :
                      ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
                        (program : SourceProgram Player L Γ O)
                        (prefixed : RevealPrefix program count)
                        (lift : ProtocolState program → ProtocolState setup.program)
                        (origin : ProtocolSuffix setup.program program lift)
                        (unique : (Γ.map Prod.fst).Nodup)
                        (left right : SourceProgram.Config Player L Γ)
                        (mask : Finset Player) (leftGeneration rightGeneration : Nat)
                        (rightFirst : CommitRecoveryState setup.program)
                        (rightPoint : rightFirst = CommitRecoveryState.atPoint
                          (lift (ProtocolState.entry program right)) mask rightGeneration)
                        (leftPrior : setup.commitRecoveryProtocol.Trace
                          (some (CommitRecoveryState.atPoint
                            (lift (ProtocolState.entry program left)) mask leftGeneration)))
                        (rightPrior : setup.commitRecoveryProtocol.Trace
                          (some rightFirst))
                        (leftLast rightLast : CommitRecoveryState setup.program)
                        (leftTrace : setup.commitRecoveryProtocol.Trace (some leftLast))
                        (rightTrace : setup.commitRecoveryProtocol.Trace (some rightLast)),
                        TracePrefix leftPrior leftTrace → TracePrefix rightPrior rightTrace →
                        leftTrace.length = leftPrior.length + count →
                        rightTrace.length = rightPrior.length + count →
                        (∀ name kind, (cellField kind).IsPublic →
                          ProtocolState.cell? setup.program leftLast.point name kind =
                            ProtocolState.cell? setup.program rightLast.point name kind) →
                        leftLast.excluded = rightLast.excluded := by
                    intro count
                    induction count with
                    | zero =>
                        intro Γ O program prefixed lift origin unique left right mask
                          leftGeneration rightGeneration rightFirst rightPoint
                            leftPrior rightPrior leftLast rightLast
                            leftTrace rightTrace leftKept rightKept leftLength rightLength _public
                        subst rightFirst
                        have leftHistory := leftKept.eq_of_same_length TracePrefix.refl (by omega)
                        have rightHistory := rightKept.eq_of_same_length TracePrefix.refl (by omega)
                        have leftState := Option.some.inj (congrArg History.state leftHistory)
                        have rightState := Option.some.inj (congrArg History.state rightHistory)
                        calc
                          leftLast.excluded = mask := by
                            simpa only [CommitRecoveryState.atPoint] using
                              (congrArg CommitRecoveryState.excluded leftState).symm
                          _ = rightLast.excluded := by
                            simpa only [CommitRecoveryState.atPoint] using
                              congrArg CommitRecoveryState.excluded rightState
                    | succ count ih =>
                        intro Γ O program prefixed lift origin unique left right mask
                          leftGeneration rightGeneration rightFirst rightPoint
                            leftPrior rightPrior leftLast rightLast
                            leftTrace rightTrace leftKept rightKept leftLength rightLength
                              publicCells
                        subst rightFirst
                        cases program with
                        | ret payoffs => exact prefixed.elim
                        | sample name fresh law suffix => exact prefixed.elim
                        | commit name owner fresh guard suffix => exact prefixed.elim
                        | @reveal Γ O published owner name payload fresh selected unresolved
                            suffix =>
                            have peel (entry : SourceProgram.Config Player L Γ)
                                (generation : Nat)
                                (joint : Player → Option (CommitRecoveryMove Player L))
                                (after : CommitRecoveryState setup.program)
                                (supported : after ∈ ((CommitRecoveryState.atPoint
                                  (lift (ProtocolState.entry _ entry)) mask generation).step
                                    joint).support) :
                                ∃ final : SourceProgram.Config Player L
                                    ((published, .publication payload) :: Γ),
                                  after = CommitRecoveryState.atPoint
                                    (lift (.inr (ProtocolState.entry suffix final)))
                                    (match final.state.get .here with
                                      | .failure => insert owner mask
                                      | .success _ => mask) generation := by
                              let result := revealSuccessor published selected entry
                                (if owner ∈ mask then false else
                                  OwnAction.disclosure ((joint owner).map (·.action)))
                              let kept := if owner ∈ mask then
                                { result with history := entry.history } else result
                              have notCommit : ProtocolState.atCommit setup.program
                                  (lift (ProtocolState.entry _ entry)) = false := by
                                rw [origin.atCommit_lift]
                                rfl
                              obtain ⟨raw, member, installed⟩ :=
                                CommitRecoveryState.step_noncommit_atPoint
                                  (CommitRecoveryState.atPoint
                                    (lift (ProtocolState.entry _ entry)) mask generation)
                                      (CommitRecoveryState.atPoint_blockFrontier _ _ _)
                                        notCommit joint after supported
                              have kernel : ProtocolState.recoveryStep
                                  (.reveal published owner name fresh selected unresolved suffix)
                                  (ProtocolState.entry _ entry) mask joint = PMF.pure
                                    ((Sum.inr (ProtocolState.entry suffix kept) : ProtocolState _),
                                      match result.state.get .here with
                                        | .failure => insert owner mask
                                        | .success _ => mask) := rfl
                              change raw ∈ (ProtocolState.recoveryStep setup.program
                                (lift (ProtocolState.entry _ entry)) mask joint).support at member
                              rw [origin.recoveryStep_lift, kernel, PMF.pure_map,
                                PMF.mem_support_pure_iff] at member
                              refine ⟨kept, ?_⟩
                              rw [installed, member]
                              have same : kept.state = result.state := by
                                dsimp only [kept]
                                split_ifs <;> rfl
                              rw [same]
                              rfl
                            rcases leftKept.reachesWithin.eq_or_step with leftSame | leftStep
                            · have lengths := congrArg
                                (fun history : setup.commitRecoveryProtocol.History =>
                                  history.trace.length) leftSame
                              change leftPrior.length = leftTrace.length at lengths
                              omega
                            · rcases rightKept.reachesWithin.eq_or_step with rightSame | rightStep
                              · have lengths := congrArg
                                  (fun history : setup.commitRecoveryProtocol.History =>
                                    history.trace.length) rightSame
                                change rightPrior.length = rightTrace.length at lengths
                                omega
                              · obtain ⟨leftJoint, leftLegal, leftState, leftMoved,
                                  _leftFuel, leftOnward⟩ := leftStep
                                obtain ⟨leftAfter, leftSupport, rfl⟩ :=
                                  (PMF.mem_support_map_iff ..).mp leftMoved
                                obtain ⟨rightJoint, rightLegal, rightState, rightMoved,
                                  _rightFuel, rightOnward⟩ := rightStep
                                obtain ⟨rightAfter, rightSupport, rfl⟩ :=
                                  (PMF.mem_support_map_iff ..).mp rightMoved
                                obtain ⟨leftNext, leftInstalled⟩ :=
                                  peel left leftGeneration leftJoint leftAfter leftSupport
                                obtain ⟨rightNext, rightInstalled⟩ :=
                                  peel right rightGeneration rightJoint rightAfter rightSupport
                                let suffixLift := fun point => lift (Sum.inr point)
                                have suffixOrigin : ProtocolSuffix setup.program suffix
                                    suffixLift := origin.revealTail fresh selected unresolved suffix
                                have nextUnique :
                                    (((published, .publication payload) :: Γ).map Prod.fst).Nodup :=
                                  by simpa only [List.map_cons] using
                                    List.nodup_cons.mpr ⟨fresh, unique⟩
                                have headRead
                                    (entry : SourceProgram.Config Player L
                                      ((published, .publication payload) :: Γ))
                                    (excluded : Finset Player) (generation : Nat)
                                    (prior : setup.commitRecoveryProtocol.Trace
                                      (some (CommitRecoveryState.atPoint
                                        (suffixLift (ProtocolState.entry suffix entry))
                                          excluded generation)))
                                    (ending : CommitRecoveryState setup.program)
                                    (trace : setup.commitRecoveryProtocol.Trace (some ending))
                                    (kept : TracePrefix prior trace) :
                                    ProtocolState.cell? setup.program ending.point published
                                      (.publication payload) = some (entry.state.get .here) := by
                                  obtain ⟨current, live, saved, endingState, point, _saved,
                                    cells, _savedCells⟩ := source_suffix_cells_of_prefix setup
                                      suffix suffixLift suffixOrigin _ prior
                                        (ProtocolState.entry suffix entry)
                                        (ProtocolState.entry suffix entry) rfl rfl rfl trace kept
                                  have same : current = ending :=
                                    (Option.some.inj endingState).symm
                                  subst current
                                  rw [point, suffixOrigin.cell?_lift,
                                    ProtocolState.cell?_eq_of_base published
                                      (.publication payload) suffix live nextUnique .here, cells]
                                  rw [ProtocolState.base_entry]
                                cases leftInstalled
                                cases rightInstalled
                                have leftHead := headRead leftNext _ leftGeneration
                                  (leftPrior.extend leftJoint leftLegal leftMoved)
                                    leftLast leftTrace leftOnward.tracePrefix
                                have rightHead := headRead rightNext _ rightGeneration
                                  (rightPrior.extend rightJoint rightLegal rightMoved)
                                    rightLast rightTrace rightOnward.tracePrefix
                                have headEqual : leftNext.state.get .here =
                                    rightNext.state.get .here := Option.some.inj
                                      (leftHead.symm.trans
                                        ((publicCells published (.publication payload)
                                          (by trivial)).trans rightHead))
                                have maskEqual :
                                    (match leftNext.state.get .here with
                                      | .failure => insert owner mask
                                      | .success _ => mask) =
                                    (match rightNext.state.get .here with
                                      | .failure => insert owner mask
                                      | .success _ => mask) := by rw [headEqual]
                                exact ih suffix prefixed suffixLift suffixOrigin nextUnique
                                  leftNext rightNext _ leftGeneration rightGeneration
                                    _ (by rw [maskEqual])
                                    (leftPrior.extend leftJoint leftLegal leftMoved)
                                    (rightPrior.extend rightJoint rightLegal rightMoved)
                                    leftLast rightLast leftTrace rightTrace
                                    leftOnward.tracePrefix rightOnward.tracePrefix
                                    (by
                                      change leftTrace.length = (leftPrior.length + 1) + count
                                      omega)
                                    (by
                                      change rightTrace.length = (rightPrior.length + 1) + count
                                      omega) publicCells
                  have transportPublicEndpoint
                      {left right : ResidualProgram setup.program} (equal : left = right)
                      (leftRefs : ContextRefs (graphLayout setup.program) left.context)
                      (rightRefs : ContextRefs (graphLayout setup.program) right.context)
                      (leftEmbedding : OutputEmbedding (inputLayout setup.context)
                        (outputLayout setup.program) left.tail)
                      (rightEmbedding : OutputEmbedding (inputLayout setup.context)
                        (outputLayout setup.program) right.tail)
                      (leftReadout : CompiledReadoutSuffix setup.program left.tail
                        leftRefs leftEmbedding)
                      (rightReadout : CompiledReadoutSuffix setup.program right.tail
                        rightRefs rightEmbedding)
                      (source : SourceProgram.Config Player L right.context)
                      (state : CommitRecoveryState setup.program)
                      (mask : Finset Player) (generation : Nat)
                      (point : state = CommitRecoveryState.atPoint
                        (right.lift (ProtocolState.entry right.tail source)) mask generation)
                      (store : Store (graphLayout setup.program))
                      (agreement : rightRefs.Agrees source.state store) :
                      ∃ mapped : SourceProgram.Config Player L left.context,
                        state = CommitRecoveryState.atPoint
                          (left.lift (ProtocolState.entry left.tail mapped)) mask generation ∧
                        leftRefs.Agrees mapped.state store := by
                    cases equal
                    have references := CompiledReadoutSuffix.refs_eq setup.program
                      leftReadout rightReadout
                    cases references
                    exact ⟨source, point, agreement⟩
                  let chosen := (checkpointSelection setup implementation operational
                    (earlier.extend joint legal moved)).val.checkpoint
                  have originalPrefix := checkpointSelection_prefix setup implementation
                    operational previous next earlier (earlier.extend joint legal moved)
                      (TracePrefix.extend TracePrefix.refl joint legal moved)
                  have priorToNext : TracePrefix priorMapped.trace nextMapped.trace := by
                    apply commonPrefixOrder priorMapped nextMapped targetEntry
                      priorEntryKept nextEntryKept
                    have bound := originalPrefix.length_le
                    rw [nextOriginal] at nextDepth
                    simp only [setup.proposalRecoveryLiftTrace_length] at nextDepth
                    omega
                  have priorRank : instructionCount setup.program -
                      ProtocolState.remaining setup.program priorCurrent.saved =
                        previous.execution.application.attempt.phase := by
                    rw [priorSavedPoint, first.checkpoint.remaining,
                      ProtocolState.remaining_entry]
                    simpa only [first.checkpoint.remaining,
                      ProtocolState.remaining_entry] using first.checkpoint.saved_position
                  have nextRank : instructionCount setup.program -
                      ProtocolState.remaining setup.program nextCurrent.saved =
                        next.execution.application.attempt.phase := by
                    rw [nextSavedPoint, chosen.remaining,
                      ProtocolState.remaining_entry]
                    simpa only [chosen.remaining,
                      ProtocolState.remaining_entry] using chosen.saved_position
                  have positiveLength : priorMapped.trace.length <
                      nextMapped.trace.length := by
                    by_contra notLonger
                    have lengths : priorMapped.trace.length = nextMapped.trace.length :=
                      Nat.le_antisymm priorToNext.length_le (Nat.le_of_not_gt notLonger)
                    have histories := priorToNext.eq_of_same_length TracePrefix.refl lengths
                    have states : priorCurrent = nextCurrent := by
                       have states := congrArg History.state histories
                       rw [priorState, nextState] at states
                       exact Option.some.inj states
                    apply same
                    have extensional (first second : CommitAttemptId)
                        (phase : first.phase = second.phase)
                        (generation : first.generation = second.generation) : first = second := by
                      cases first
                      cases second
                      cases phase
                      cases generation
                      rfl
                    apply extensional
                    · have savedEq := congrArg
                        (fun state : CommitRecoveryState setup.program =>
                          instructionCount setup.program -
                            ProtocolState.remaining setup.program state.saved) states
                      exact priorRank.symm.trans (savedEq.trans nextRank)
                    · exact priorGeneration.symm.trans
                        ((congrArg CommitRecoveryState.generation states).trans nextGeneration)
                  let priorActual : setup.proposalRecoveryProtocol.Trace
                      (some priorCurrent) := priorState ▸ priorMapped.trace
                  have priorActualEq :
                      (⟨some priorCurrent, priorActual⟩ :
                        setup.proposalRecoveryProtocol.History) = priorMapped := by
                    rcases priorMapped with ⟨state, trace⟩
                    cases priorState
                    rfl
                  have priorActualLength : priorActual.length =
                      priorMapped.trace.length := congrArg
                        (fun history : setup.proposalRecoveryProtocol.History =>
                          history.trace.length) priorActualEq
                  let nextActual : setup.proposalRecoveryProtocol.Trace
                      (some nextCurrent) := nextState ▸ nextMapped.trace
                  have nextActualEq :
                      (⟨some nextCurrent, nextActual⟩ :
                        setup.proposalRecoveryProtocol.History) = nextMapped := by
                    rcases nextMapped with ⟨state, trace⟩
                    cases nextState
                    rfl
                  have nextActualInfo : setup.proposalRecoveryModel.infoOf who
                      (setup.proposalRecoveryLiftTrace labels chosen.trace) =
                        setup.proposalRecoveryModel.infoOf who nextActual :=
                    nextInfo.trans (congrArg
                      (fun history : setup.proposalRecoveryProtocol.History =>
                        setup.proposalRecoveryModel.infoOf who history.trace)
                          nextActualEq).symm
                  have actualPriorToNext : TracePrefix priorActual nextMapped.trace := by
                    have kept := priorToNext
                    rw [← priorActualEq] at kept
                    exact kept
                  have finishCursor
                      {cursorState : PhaseRuntimeState
                        (serviceGraph setup .concurrent)}
                      (cursor : RecoverySourceCheckpoint setup .concurrent cursorState)
                      (targetSource : SourceProgram.Config Player L
                        cursor.residual.context)
                      (targetState : CommitRecoveryState setup.program)
                      (targetHistory : setup.proposalRecoveryProtocol.Trace
                        (some targetState))
                      (targetSaved : targetState.saved =
                        cursor.residual.lift
                          (ProtocolState.entry cursor.residual.tail targetSource))
                      (targetAgrees : cursor.refs.Agrees targetSource.state
                        (sourceSnapshotState setup implementation G reference lost
                          next.execution.application.entry.native).config.store)
                      (sameHistory :
                        (⟨some targetState, targetHistory⟩ :
                          setup.proposalRecoveryProtocol.History) =
                            nextMapped)
                      (sameResidual : cursor.residual = chosen.residual)
                      (sameRefs : cast (congrArg (fun residual :
                        ResidualProgram setup.program =>
                          ContextRefs (graphLayout setup.program)
                            residual.context) sameResidual)
                              cursor.refs = chosen.refs) :
                      chosen.refs.Agrees nextSaved.state
                        (sourceSnapshotState setup implementation G reference lost
                          next.execution.application.entry.native).config.store := by
                    have atEndState : targetState = nextCurrent := by
                      have states := congrArg
                        (fun history : setup.proposalRecoveryProtocol.History =>
                          history.state) sameHistory
                      change some targetState = nextMapped.state at states
                      rw [nextState] at states
                      exact Option.some.inj states
                    have sameSavedPoint :
                        cursor.residual.lift
                            (ProtocolState.entry cursor.residual.tail
                              targetSource) =
                          chosen.residual.lift
                            (ProtocolState.entry chosen.residual.tail nextSaved) := by
                      calc
                        cursor.residual.lift
                            (ProtocolState.entry cursor.residual.tail
                              targetSource) = targetState.saved :=
                          targetSaved.symm
                        _ = nextCurrent.saved :=
                          congrArg CommitRecoveryState.saved atEndState
                        _ = _ := nextSavedPoint
                    have transportConfig {left right :
                        ResidualProgram setup.program}
                        (equal : left = right)
                        (origin : ProtocolSuffix setup.program left.tail left.lift)
                        (source : SourceProgram.Config Player L left.context)
                        (result : SourceProgram.Config Player L right.context)
                        (point : left.lift (ProtocolState.entry left.tail source) =
                          right.lift (ProtocolState.entry right.tail result)) :
                        cast (congrArg (fun residual :
                          ResidualProgram setup.program =>
                            SourceProgram.Config Player L residual.context)
                              equal) source = result := by
                      cases equal
                      exact ProtocolState.entry_injective left.tail
                        (sourceReplaySuffixInjective setup origin point)
                    have sameConfig := transportConfig sameResidual
                      cursor.origin targetSource nextSaved sameSavedPoint
                    have transportAgreement {left right :
                        ResidualProgram setup.program}
                        (equal : left = right)
                        (leftRefs : ContextRefs (graphLayout setup.program)
                          left.context)
                        (rightRefs : ContextRefs (graphLayout setup.program)
                          right.context)
                        (sameRefs : cast (congrArg (fun residual :
                          ResidualProgram setup.program =>
                            ContextRefs (graphLayout setup.program)
                              residual.context) equal) leftRefs = rightRefs)
                        (leftSource : SourceProgram.Config Player L left.context)
                        (rightSource : SourceProgram.Config Player L right.context)
                        (sameSource : cast (congrArg (fun residual :
                          ResidualProgram setup.program =>
                            SourceProgram.Config Player L residual.context)
                              equal) leftSource = rightSource)
                        (store : Store (graphLayout setup.program)) :
                        leftRefs.Agrees leftSource.state store →
                          rightRefs.Agrees rightSource.state store := by
                      cases equal
                      cases sameRefs
                      cases sameSource
                      exact id
                    intro name cell source
                    exact transportAgreement sameResidual cursor.refs
                      chosen.refs sameRefs targetSource nextSaved sameConfig _
                        targetAgrees source
                  have tailRec :
                       ∀ (tail : List (RuntimePhase
                           (serviceGraph setup .concurrent)))
                         (generation : Nat)
                         (live : RecoveryState (serviceGraph setup .concurrent))
                         (retired : List (RetiredCommitAttempt
                           (serviceGraph setup .concurrent)))
                         (witness : RecoverySourceWitness setup .concurrent
                           implementation.plan
                             (⟨tail, generation, live, live, retired⟩ :
                               PhaseRuntimeState
                                 (serviceGraph setup .concurrent)))
                         (targetSource : SourceProgram.Config Player L
                           witness.checkpoint.residual.context)
                         (targetState : CommitRecoveryState setup.program)
                         (targetTrace : setup.proposalRecoveryProtocol.Trace
                           (some targetState)),
                         targetState = CommitRecoveryState.atPoint
                           (witness.checkpoint.residual.lift
                             (ProtocolState.entry witness.checkpoint.residual.tail
                               targetSource)) live.excluded generation →
                         TracePrefix targetTrace nextMapped.trace →
                         witness.checkpoint.refs.Agrees targetSource.state
                           (sourceSnapshotState setup implementation G reference lost
                             live.native).config.store →
                         nextCurrent.excluded = live.excluded →
                         ProtocolState.remaining setup.program nextCurrent.point +
                             nextMapped.trace.length =
                           ProtocolState.remaining setup.program targetState.point +
                             targetTrace.length →
                         next.execution.application =
                           PhaseRuntimeState.settle tail generation live live retired →
                         chosen.refs.Agrees nextSaved.state
                           (sourceSnapshotState setup implementation G reference lost
                             next.execution.application.entry.native).config.store := by
                     intro tail
                     induction tail with
                     | nil =>
                         intro generation live retired witness targetSource
                           targetState targetTrace targetAtPoint targetToSelected
                           targetAgrees endpointMask targetClock selectedSettle
                         let cursor := witness.checkpoint
                         have targetPoint : targetState.point =
                             cursor.residual.lift (ProtocolState.entry
                               cursor.residual.tail targetSource) :=
                           congrArg CommitRecoveryState.point targetAtPoint
                         have targetSaved : targetState.saved =
                             cursor.residual.lift (ProtocolState.entry
                               cursor.residual.tail targetSource) :=
                           congrArg CommitRecoveryState.saved targetAtPoint
                         have samePhase :
                             (⟨[], generation, live, live, retired⟩ :
                               PhaseRuntimeState
                                 (serviceGraph setup .concurrent)).attempt.phase =
                               next.execution.application.attempt.phase := by
                           rw [selectedSettle]
                           rfl
                         have sameResidual :=
                           cursor.residual_eq_of_phase_eq chosen samePhase
                         have sameRefs := sourceReplayCheckpointRefsEq setup cursor
                           chosen samePhase
                         have targetRemaining : ProtocolState.remaining setup.program
                             targetState.point =
                               instructionCount cursor.residual.tail := by
                           rw [targetPoint, cursor.remaining,
                             ProtocolState.remaining_entry]
                         have finalRemaining : ProtocolState.remaining setup.program
                             nextCurrent.point =
                               instructionCount chosen.residual.tail := by
                           rw [nextPoint, chosen.remaining,
                             ProtocolState.remaining_entry]
                         have countEq := congrArg (fun residual :
                           ResidualProgram setup.program =>
                             instructionCount residual.tail) sameResidual
                         have sameLength : targetTrace.length =
                             nextMapped.trace.length := by omega
                         have sameHistory := targetToSelected.eq_of_same_length
                           (TracePrefix.refl (prefixTrace := nextMapped.trace))
                             sameLength
                         have finalAgrees : cursor.refs.Agrees targetSource.state
                             (sourceSnapshotState setup implementation G reference lost
                               next.execution.application.entry.native).config.store := by
                           rw [selectedSettle]
                           exact sourceReplaySettleAssignedSavedAgreement setup implementation
                             cursor.refs targetSource G reference lost [] generation
                               live retired targetAgrees
                         exact fun {name cell} source =>
                           finishCursor cursor targetSource targetState targetTrace
                             targetSaved finalAgrees sameHistory sameResidual sameRefs source
                     | cons following rest ih =>
                         intro generation live retired witness targetSource
                           targetState targetTrace targetAtPoint targetToSelected
                           targetAgrees endpointMask targetClock selectedSettle
                         let cursorState : PhaseRuntimeState
                             (serviceGraph setup .concurrent) :=
                           ⟨following :: rest, generation, live, live, retired⟩
                         let cursor := witness.checkpoint
                         have targetPoint : targetState.point =
                             cursor.residual.lift (ProtocolState.entry
                               cursor.residual.tail targetSource) :=
                           congrArg CommitRecoveryState.point targetAtPoint
                         have targetSaved : targetState.saved =
                             cursor.residual.lift (ProtocolState.entry
                               cursor.residual.tail targetSource) :=
                           congrArg CommitRecoveryState.saved targetAtPoint
                         have targetMask : targetState.excluded = live.excluded :=
                           congrArg CommitRecoveryState.excluded targetAtPoint
                         have targetGeneration : targetState.generation =
                             generation :=
                           congrArg CommitRecoveryState.generation targetAtPoint
                         have seedFrontier := witness.receipts.exclusion.frontier
                         have seedNative := witness.native.choose_spec.active
                         have seedBinding := witness.binding.active
                         have seedReceipts := witness.receipts
                         have seedOrder := witness.order
                         have seedInstalled : cursorState.phases =
                             following :: rest := rfl
                         have seedMember : following ∈
                             cursorState.phases.head? :=
                           Option.mem_some_iff.mpr rfl
                         have followingStart : live.native.config.cut.IsPrefix
                             following.low := seedFrontier.positioned.1
                         have laterMaximal :=
                           operational.maximalPhases.suffix witness.suffix
                         have ordered := seedFrontier.adjacent
                         have last := seedFrontier.last
                         intro observationName observationKind observedCell
                         by_cases followingFinished : following.Finished
                           (following.drain live)
                         · have inheritedOwners :=
                             source_automatic_finished_owners_subset setup following live
                               followingStart followingFinished
                           have noNewMiss : ¬ (following.kind = .commitment ∧
                               (((following.drain live).excluded \ live.excluded) ∩
                                 following.owners).Nonempty) := by
                             rintro ⟨_, failed⟩
                             rw [following.drain_excluded] at failed
                             simp at failed
                           have nextAfterFollowing :
                               next.execution.application =
                                 PhaseRuntimeState.settle rest generation
                                   (following.drain live)
                                     (following.drain live) retired := by
                             rw [selectedSettle]
                             exact PhaseRuntimeState.settle_clean following rest
                               generation live live retired followingFinished
                                 noNewMiss
                           have nextLow : PhaseRuntimeState.phaseLow rest =
                               following.high := by
                             have adjacent := seedFrontier.adjacent
                             have last := seedFrontier.last
                             cases rest with
                             | nil =>
                                 have ending := last following (by
                                   simp only [List.getLast?_singleton,
                                     Option.mem_some_iff])
                                 simpa only [PhaseRuntimeState.phaseLow,
                                   List.head?_nil, Option.map_none,
                                   Option.getD_none, serviceGraph, Setup.eventGraph]
                                     using ending.symm
                             | cons nextPhase tail =>
                                 have boundary := adjacent.rel_head?
                                   (y := nextPhase) (by simp)
                                 simpa only [PhaseRuntimeState.phaseLow,
                                   List.head?_cons, Option.map_some,
                                   Option.getD_some] using boundary.symm
                           have nextAfterFollowingRank : following.high ≤
                               next.execution.application.attempt.phase := by
                             rw [nextAfterFollowing, ← nextLow]
                             exact (PhaseRuntimeState.settle_namespace rest
                               generation (following.drain live)
                                 (following.drain live) retired
                                   seedFrontier.adjacent.tail).2
                           have targetRemaining :
                               ProtocolState.remaining setup.program
                                 targetState.point =
                                   instructionCount cursor.residual.tail := by
                             rw [targetPoint, cursor.remaining,
                               ProtocolState.remaining_entry]
                           have finalRemaining :
                               ProtocolState.remaining setup.program
                                 nextCurrent.point =
                                   instructionCount chosen.residual.tail := by
                             rw [nextPoint, chosen.remaining,
                               ProtocolState.remaining_entry]
                           have phaseDepthBound : targetTrace.length +
                                 (following.high - following.low) ≤
                               nextMapped.trace.length := by
                             have cursorCount := cursor.compiled.countEq
                             have finalCount := chosen.compiled.countEq
                             have cursorPhase : cursorState.attempt.phase =
                                 following.low := rfl
                             rw [cursorPhase] at cursorCount
                             simp only [eventCount_eq_instructionCount] at cursorCount
                             simp only [eventCount_eq_instructionCount] at finalCount
                             have bounded := targetToSelected.length_le
                             omega
                           obtain ⟨phaseState, phaseTrace, phaseToNext,
                             phaseDepth⟩ :=
                             setup.proposalRecovery_prefix_at_depth
                               nextMapped.trace
                                 (targetTrace.length +
                                   (following.high - following.low))
                                     phaseDepthBound
                           change phaseTrace.length = targetTrace.length +
                             (following.high - following.low) at phaseDepth
                           have targetToPhase : TracePrefix targetTrace
                               phaseTrace := by
                             apply commonPrefixOrder
                               ⟨some targetState, targetTrace⟩
                                 ⟨phaseState, phaseTrace⟩ nextMapped
                                   targetToSelected phaseToNext
                             change targetTrace.length ≤ phaseTrace.length
                             omega
                           have phaseToG : TracePrefix phaseTrace g.trace :=
                             phaseToNext.trans (nextEntryKept.trans entryKept)
                           have phaseToGFinal : TracePrefix phaseTrace G.trace :=
                             phaseToNext.trans nextKept
                           obtain ⟨phaseLast, phaseJoints, phaseAddresses,
                             phaseStateEq, phasePath, phaseLength, phaseWord,
                             phaseSignals⟩ :=
                             source_instruction_window setup
                               (setup.initialConfig
                                 setup.initialLaw.support_nonempty.choose)
                                   targetState
                                     (setup.proposalRecoveryEraseTrace targetTrace)
                                       (setup.proposalRecoveryEraseTrace phaseTrace)
                                         (setup.proposalRecoveryEraseTrace_prefix
                                           targetToPhase)
                           cases phaseStateEq
                           have phaseRows : phaseJoints.length =
                               following.high - following.low := by
                             have erasedLength := phaseLength
                             simp only [setup.proposalRecoveryEraseTrace_length] at erasedLength
                             omega
                           have phaseMask : phaseLast.excluded =
                               targetState.excluded := by
                             have lower := setup.prefix_excluded
                               (setup.proposalRecoveryEraseTrace targetTrace)
                               (setup.proposalRecoveryEraseTrace phaseTrace)
                               (setup.proposalRecoveryEraseTrace_prefix
                                 targetToPhase)
                             have upper := setup.prefix_excluded
                               (setup.proposalRecoveryEraseTrace phaseTrace)
                               (setup.proposalRecoveryEraseTrace nextMapped.trace)
                               (setup.proposalRecoveryEraseTrace_prefix phaseToNext)
                             change targetState.excluded ⊆ phaseLast.excluded at lower
                             rw [nextState] at upper
                             change phaseLast.excluded ⊆ nextCurrent.excluded at upper
                             rw [endpointMask] at upper
                             rw [targetMask] at lower
                             rw [targetMask]
                             exact Finset.Subset.antisymm upper lower
                           have phasePhysicalMask : phaseLast.excluded =
                               live.excluded := phaseMask.trans targetMask
                           cases kind : following.kind with
                           | commitment =>
                             have followingGeometry :=
                               cursor.commit_phase_geometry following rest
                                 seedInstalled kind seedFrontier laterMaximal
                             generalize nextDecomposition :
                                 SourceProgram.commitPhase
                                    cursor.residual.tail = nextSegment at followingGeometry
                             rcases nextSegment with ⟨nextContext, nextNames,
                               nextSuffix, nextBlock, nextReconstruct,
                               nextBoundary⟩
                             dsimp only at followingGeometry
                             let nextLift : ProtocolState
                                 (nextBlock.prepend nextSuffix) →
                                   ProtocolState setup.program := fun point =>
                               cursor.residual.lift
                                 (cast (congrArg ProtocolState nextReconstruct) point)
                             have nextOrigin : ProtocolSuffix setup.program
                                 (nextBlock.prepend nextSuffix) nextLift :=
                               transportOrigin nextReconstruct
                                 cursor.residual.lift cursor.origin
                             obtain ⟨nextEmbedding, nextBefore, nextEmbeddingEq,
                               nextCompiled, nextReadout, ⟨nextViews⟩⟩ :=
                               transportCompiled nextReconstruct
                                 cursor.source cursor.refs cursor.registry cursor.embedding
                                   cursor.before cursorState.attempt.phase
                                       cursor.compiled
                                         cursor.terminalAlignment
                                           cursor.residual.lift
                                             cursor.views
                             have targetNextPoint : targetState.point =
                                 nextLift (ProtocolState.entry
                                   (nextBlock.prepend nextSuffix) targetSource) := by
                               rw [targetPoint]
                               dsimp only [nextLift]
                               rw [transportEntry nextReconstruct]
                             have nextPositive : 0 < nextBlock.length := by
                               have width := followingGeometry.1
                               have nonempty := following.nonempty
                               omega
                             have nextLow : following.low = cursorState.attempt.phase := rfl
                             have targetNextCommit : ProtocolState.atCommit
                                 setup.program targetState.saved = true := by
                               rw [targetSaved, cursor.origin.atCommit_lift]
                               have equalEntry {Γ : SourceCtx Player L} {O : Finset VarId}
                                   (program : SourceProgram Player L Γ O)
                                   (left right : SourceProgram.Config Player L Γ) :
                                   ProtocolState.atCommit program
                                     (ProtocolState.entry program left) =
                                     ProtocolState.atCommit program
                                       (ProtocolState.entry program right) := by
                                 cases program <;> rfl
                               rw [equalEntry cursor.residual.tail targetSource cursor.source]
                               exact cursor.compiled.atCommit_of_bindingPhase setup.program
                                 .concurrent cursor.residual.tail cursor.refs
                                   cursor.source.revelations cursor.registry cursor.embedding
                                     cursor.before cursorState.attempt.phase following kind
                                       nextLow cursor.source
                             have targetNextEnd : ProtocolState.commitEnd
                                 setup.program targetState.saved ≤
                                   instructionCount nextSuffix := by
                               rw [targetSaved, cursor.commitEnd, ProtocolState.commitEnd_entry,
                                 nextDecomposition]
                             have nextPhaseEq := compiledCommitPhase_eq_of_maximal
                               setup.program (.concurrent) nextBlock nextSuffix
                                 nextEmbedding nextCompiled nextPositive nextBoundary
                                   following rest ordered last laterMaximal nextLow
                             have nextOwners : following.owners =
                                 nextBlock.owners := by
                               exact (congrArg RuntimePhase.owners nextPhaseEq).trans
                                 (compiledCommitPhase_owners setup.program (.concurrent)
                                   nextBlock nextSuffix nextEmbedding nextCompiled nextPositive)
                             have nextDepth : phaseTrace.length =
                                 targetTrace.length + nextBlock.length := by
                               have width := followingGeometry.1
                               omega
                             obtain ⟨nextFinished, nextExcluded, nextAttempt,
                               nextAddresses, nextPath, nextWord,
                               nextSignals, nextMonotone, nextClosed⟩ :=
                               source_attempt_of_literal_window setup
                                 (setup.initialConfig
                                   setup.initialLaw.support_nonempty.choose)
                                     nextBlock nextSuffix nextLift nextOrigin
                                       targetSource targetState phaseLast
                                         targetTrace phaseTrace targetToPhase
                                           targetNextPoint targetNextCommit
                                             targetNextEnd nextPositive nextDepth
                             have nextAttemptAtStart : nextBlock.Attempt targetSource
                                 (live).excluded nextFinished
                                   nextExcluded := by
                               simpa only [targetMask] using nextAttempt
                             have allOwners : nextBlock.owners ⊆ live.excluded := by
                               rw [← nextOwners]
                               exact inheritedOwners
                             have automaticRows : sourceAttemptTableReads setup
                                 nextAttempt nextSuffix nextEmbedding
                                   (sourceSnapshotState setup implementation G reference
                                     lost (following.drain
                                       (live)).native) := by
                               have failed : ∀ index : Fin
                                   (eventCount (nextBlock.prepend nextSuffix)),
                                   index.val < nextBlock.length →
                                   ∀ (owner : Player) (payload : L.Ty)
                                   (binding : outputLayout
                                     (nextBlock.prepend nextSuffix) index =
                                       .binding owner payload),
                                   (⟨.inr (nextEmbedding.event index),
                                     (nextEmbedding.layout_eq index).trans binding⟩ :
                                       FieldRef (serviceGraph setup .concurrent).layout
                                         (.binding owner payload)).get?
                                       (sourceSnapshotState setup implementation G
                                         reference lost (following.drain
                                           (live)).native).config.store =
                                             some .failure := by
                                 intro index inside owner payload binding
                                 have shape : (serviceGraph setup .concurrent).outputLayout
                                     (nextEmbedding.event index) =
                                       .binding owner payload :=
                                   (nextEmbedding.layout_eq index).trans binding
                                 have member : nextEmbedding.event index ∈
                                     following.events := by
                                   apply (congrArg (fun phase : RuntimePhase
                                     (serviceGraph setup .concurrent) =>
                                       nextEmbedding.event index ∈ phase.events) nextPhaseEq).mpr
                                   exact (compiledCommitPhase_mem_iff setup.program
                                     (.concurrent) nextBlock nextSuffix nextEmbedding
                                       nextCompiled nextPositive _).mpr ⟨index, inside, rfl⟩
                                 simpa only [binding] using
                                   automaticFinishedBindingRows following
                                     (live) followingStart
                                       seedOrder.coverage.active seedBinding
                                         followingFinished
                                         (nextEmbedding.event index) member owner payload
                                           shape lost
                               have allAtTarget : nextBlock.owners ⊆ targetState.excluded := by
                                 simpa only [targetMask] using allOwners
                               exact automaticBindingReads nextBlock targetSource
                                 targetState.excluded allAtTarget nextSuffix nextEmbedding
                                   (sourceSnapshotState setup implementation G reference lost
                                     (following.drain live).native) failed nextAttempt
                             have automaticEntryAgrees : cursor.refs.Agrees
                                 targetSource.state
                                   (sourceSnapshotState setup implementation G
                                     reference lost (following.drain
                                       (live)).native).config.store := by
                               apply sourceReplayEntryAgreesOfPreserved setup
                                 implementation cursor.refs targetSource G
                                   reference lost (live).native
                                     (following.drain
                                       (live)).native
                                         targetAgrees
                               · intro name cell source
                                 let field := (cursor.refs.get source).field
                                 have occupied := targetAgrees source
                                 cases stored : (live).native.config.store
                                     field with
                                 | none =>
                                     have swappedEmpty :
                                         (sourceSnapshotState setup implementation G
                                           reference lost
                                             (live).native).config.store
                                               field = none := by
                                       simp only [sourceSnapshotState,
                                         State.swap_config, Config.swap_store,
                                         ValueSwap.store, stored, Option.map_none]
                                     have emptyRead :
                                         (cursor.refs.get source).get?
                                           (sourceSnapshotState setup implementation G
                                             reference lost
                                               (live).native).config.store = none := by
                                       unfold FieldRef.get?
                                       rw [swappedEmpty]
                                       exact castOptionNone
                                         (cursor.refs.get source).layout_eq
                                     rw [emptyRead] at occupied
                                     cases occupied
                                 | some value =>
                                     exact (following.drain_keepsStore
                                       (live) field value stored).symm
                               · intro name cell source _owner _payload _shape _value
                                   _stored
                                 exact (congrFun (following.drain_tables
                                   (live)).1
                                     (cursor.refs.get source).field).symm
                             have automaticFinalAgrees :
                                 (commitBlockRefs setup.program nextBlock nextSuffix
                                   nextEmbedding cursor.refs).Agrees nextFinished.state
                                     (sourceSnapshotState setup implementation G reference
                                       lost (following.drain live).native).config.store :=
                               target_attempt_state_agrees setup nextAttempt nextSuffix
                                 nextEmbedding
                                   (sourceSnapshotState setup implementation G reference
                                     lost (following.drain
                                       (live)).native)
                                     cursor.refs automaticEntryAgrees
                                       automaticRows
                             have automaticDecoded :=
                               decodeCommitAttempt_eq_of_target_rows setup nextAttempt
                                 nextSuffix nextEmbedding
                                   (sourceSnapshotState setup implementation G reference
                                     lost (following.drain
                                       (live)).native)
                                     automaticRows
                             have automaticVisit : SourceReplayVisitImage setup
                                 nextBlock nextSuffix nextEmbedding nextAttempt
                                   (sourceSnapshotState setup implementation G reference
                                     lost (following.drain
                                       (live)).native)
                                     cursor.refs :=
                               ⟨automaticEntryAgrees, automaticRows, automaticDecoded,
                                 automaticFinalAgrees⟩
                             obtain ⟨automaticTailEmbedding, automaticTailBefore,
                               automaticTailCompiled, automaticTailReadout,
                               ⟨automaticTailViews⟩⟩ :=
                               (nextBlock.automaticAttempt cursor.source live.excluded
                                 allOwners).compiledTail
                                 setup.program nextSuffix cursor.refs cursor.registry
                                   nextEmbedding nextBefore cursorState.attempt.phase
                                       nextCompiled nextReadout nextLift nextViews
                             have noNewFailed : ¬
                                 (((following.drain
                                   (live)).excluded \
                                     (live).excluded) ∩
                                       following.owners).Nonempty := by
                               rw [following.drain_excluded]
                               simp
                             obtain ⟨advancedWitness, _advancedPoint,
                               _advancedReached, _advancedDelta,
                               advancedNormalized⟩ :=
                               witness.completed_binding_history
                                 operational.maximalPhases following rest seedInstalled
                                   kind followingFinished noNewFailed
                             let advancedCheckpoint := advancedWitness.checkpoint
                             have followingWithin :
                                 (live).native.config.cut.Within
                                   following.low following.high := by
                               have positioned := seedFrontier.positioned
                               rw [seedInstalled] at positioned
                               exact positioned.2
                             have followingEndPrefix :
                                 (following.drain (live)).native.config.cut.IsPrefix
                                   following.high :=
                               following.finished_prefix
                                 (following.drain (live))
                                   (following.drain_within (live)
                                     followingWithin) followingFinished
                             have advancedPhase :
                                 (⟨rest, generation,
                                   following.drain (live),
                                   following.drain (live),
                                   retired⟩ :
                                     PhaseRuntimeState
                                       (serviceGraph setup .concurrent)).attempt.phase =
                                   following.high := by
                               have adjacent := seedFrontier.adjacent
                               have last := seedFrontier.last
                               rw [seedInstalled] at adjacent last
                               cases rest with
                               | nil =>
                                   have ending := last following (by
                                     simp only [List.getLast?_singleton,
                                       Option.mem_some_iff])
                                   simpa only [PhaseRuntimeState.attempt,
                                     List.head?_nil, Option.map_none,
                                     Option.getD_none, serviceGraph, Setup.eventGraph]
                                     using ending.symm
                               | cons later tail =>
                                   have boundary := adjacent.rel_head?
                                     (y := later) (by simp)
                                   simpa only [PhaseRuntimeState.attempt,
                                     List.head?_cons, Option.map_some,
                                     Option.getD_some] using boundary.symm
                             have advancedResidual : advancedCheckpoint.residual =
                                 (⟨nextContext, nextNames,
                                   nextSuffix,
                                   fun point => nextLift
                                     (nextBlock.liftPoint nextSuffix point)⟩ :
                                       ResidualProgram setup.program) := by
                               apply advancedCheckpoint.origin.residual_eq_of_instructionCount
                                 nextSuffix
                                   (fun point => nextLift
                                     (nextBlock.liftPoint nextSuffix point))
                                     (nextOrigin.compose
                                       (nextBlock.protocolSuffix nextSuffix))
                               have advancedCount := advancedCheckpoint.compiled.countEq
                               have tailCount := automaticTailCompiled.countEq
                               rw [advancedPhase] at advancedCount
                               simp only [eventCount_eq_instructionCount] at advancedCount
                               simp only [eventCount_eq_instructionCount] at tailCount
                               have width := followingGeometry.1
                               omega
                             have advancedRefs :
                                 cast (congrArg (fun residual :
                                   ResidualProgram setup.program =>
                                     ContextRefs (graphLayout setup.program)
                                       residual.context) advancedResidual)
                                   advancedCheckpoint.refs =
                                     commitBlockRefs setup.program nextBlock nextSuffix
                                       nextEmbedding cursor.refs := by
                               have readoutRefs
                                   {left right : ResidualProgram setup.program}
                                   (equal : left = right)
                                   (leftRefs : ContextRefs
                                     (graphLayout setup.program) left.context)
                                   (rightRefs : ContextRefs
                                     (graphLayout setup.program) right.context)
                                   (leftEmbedding : OutputEmbedding
                                     (inputLayout setup.context)
                                       (outputLayout setup.program) left.tail)
                                   (rightEmbedding : OutputEmbedding
                                     (inputLayout setup.context)
                                       (outputLayout setup.program) right.tail)
                                   (leftReadout : CompiledReadoutSuffix setup.program
                                     left.tail leftRefs leftEmbedding)
                                   (rightReadout : CompiledReadoutSuffix setup.program
                                     right.tail rightRefs rightEmbedding) :
                                   cast (congrArg (fun residual :
                                     ResidualProgram setup.program =>
                                       ContextRefs (graphLayout setup.program)
                                         residual.context) equal) leftRefs =
                                           rightRefs := by
                                 cases equal
                                 exact CompiledReadoutSuffix.refs_eq setup.program
                                   leftReadout rightReadout
                               exact readoutRefs advancedResidual
                                 advancedCheckpoint.refs
                                   (commitBlockRefs setup.program nextBlock nextSuffix
                                     nextEmbedding cursor.refs)
                                     advancedCheckpoint.embedding
                                       automaticTailEmbedding
                                         advancedCheckpoint.terminalAlignment
                                           automaticTailReadout
                             let advancedTarget : SourceProgram.Config Player L
                                 advancedCheckpoint.residual.context :=
                               cast (congrArg (fun residual :
                                 ResidualProgram setup.program =>
                                   SourceProgram.Config Player L residual.context)
                                     advancedResidual.symm) nextFinished
                             have advancedTargetRawAgrees :
                                 advancedCheckpoint.refs.Agrees advancedTarget.state
                                   (sourceSnapshotState setup implementation G
                                     reference lost (following.drain
                                       (live)).native).config.store := by
                               have transportAgreement
                                   {left right : ResidualProgram setup.program}
                                   (equal : left = right)
                                   (leftRefs : ContextRefs
                                     (graphLayout setup.program) left.context)
                                   (rightRefs : ContextRefs
                                     (graphLayout setup.program) right.context)
                                   (sameRefs : cast (congrArg (fun residual :
                                     ResidualProgram setup.program =>
                                       ContextRefs (graphLayout setup.program)
                                         residual.context) equal) leftRefs = rightRefs)
                                   (rightSource : SourceProgram.Config Player L
                                     right.context)
                                   (store : Store (graphLayout setup.program)) :
                                   rightRefs.Agrees rightSource.state store →
                                     leftRefs.Agrees
                                       (cast (congrArg (fun residual :
                                         ResidualProgram setup.program =>
                                           SourceProgram.Config Player L
                                             residual.context) equal.symm)
                                               rightSource).state store := by
                                 cases equal
                                 cases sameRefs
                                 exact id
                               intro name cell source
                               exact transportAgreement advancedResidual
                                 advancedCheckpoint.refs
                                   (commitBlockRefs setup.program nextBlock nextSuffix
                                     nextEmbedding cursor.refs)
                                       advancedRefs nextFinished _
                                         automaticVisit.finalAgrees source
                             have advancedTargetSavedAgrees :
                                 advancedCheckpoint.refs.Agrees advancedTarget.state
                                   (sourceSnapshotState setup implementation G
                                     reference lost
                                       next.execution.application.entry.native).config.store := by
                               rw [selectedSettle]
                               rw [PhaseRuntimeState.settle_clean following rest
                                 generation (live)
                                   (live) retired
                                     followingFinished noNewMiss]
                               exact sourceReplaySettleAssignedSavedAgreement setup implementation
                                 advancedCheckpoint.refs advancedTarget G reference lost
                                   rest generation
                                     (following.drain (live))
                                       retired advancedTargetRawAgrees
                             have nextAdvanced : next.execution.application =
                                 PhaseRuntimeState.settle rest generation
                                   (following.drain (live))
                                     (following.drain
                                       (live))
                                         retired := by
                               rw [selectedSettle]
                               exact advancedNormalized
                             have automaticNoFailure :
                                 nextAttempt.failedOwners = ∅ := by
                               apply Finset.eq_empty_iff_forall_notMem.mpr
                               intro owner member
                               exact Finset.disjoint_left.mp nextAttempt.failed_disjoint member
                                 (by
                                   rw [targetMask]
                                   exact allOwners (nextAttempt.failed_subset_owners member))
                             have automaticMask : nextExcluded = targetState.excluded := by
                               rw [nextAttempt.excluded_eq, automaticNoFailure,
                                 Finset.union_empty]
                             have automaticStart : targetState = CommitRecoveryState.atPoint
                                   (nextLift (ProtocolState.entry
                                     (nextBlock.prepend nextSuffix) targetSource))
                                     targetState.excluded targetState.generation := by
                                 calc
                                   targetState = CommitRecoveryState.atPoint targetState.point
                                       targetState.excluded targetState.generation := by
                                     rw [targetAtPoint]
                                     rfl
                                   _ = _ := by rw [targetNextPoint]
                             have automaticEnd : phaseLast =
                                 CommitRecoveryState.atPoint
                                   (nextLift (nextBlock.liftPoint nextSuffix
                                     (ProtocolState.entry nextSuffix nextFinished)))
                                       nextExcluded targetState.generation := by
                               calc
                                 phaseLast = (targetState.install
                                     (nextLift (nextBlock.liftPoint nextSuffix
                                       (ProtocolState.entry nextSuffix nextFinished)),
                                         nextExcluded) nextMonotone).close := nextClosed
                                 _ = _ := by
                                   rw [installCongr automaticStart _ _ nextMonotone]
                                   exact nextAttempt.close_clean_lift setup.program
                                     nextSuffix nextBoundary nextPositive
                                       targetState.generation nextLift
                                         nextOrigin.remaining_lift
                                           nextOrigin.atCommit_lift
                                             nextOrigin.commitEnd_lift
                                               automaticNoFailure
                             have advancedTargetPoint :
                                 advancedCheckpoint.residual.lift
                                   (ProtocolState.entry
                                     advancedCheckpoint.residual.tail advancedTarget) =
                                       phaseLast.point := by
                               have pointAfterTransport
                                   {left right : ResidualProgram setup.program}
                                   (equal : left = right)
                                   (source : SourceProgram.Config Player L
                                     right.context) :
                                   left.lift (ProtocolState.entry left.tail
                                     (cast (congrArg (fun residual :
                                       ResidualProgram setup.program =>
                                         SourceProgram.Config Player L
                                           residual.context) equal.symm) source)) =
                                     right.lift
                                       (ProtocolState.entry right.tail source) := by
                                 cases equal
                                 rfl
                               exact (pointAfterTransport advancedResidual
                                 nextFinished).trans (by
                                   rw [automaticEnd]
                                   rfl)
                             have advancedTargetSaved : phaseLast.saved =
                                 advancedCheckpoint.residual.lift
                                   (ProtocolState.entry
                                     advancedCheckpoint.residual.tail
                                       advancedTarget) := by
                               calc
                                 phaseLast.saved = phaseLast.point := by
                                   rw [automaticEnd]
                                   rfl
                                 _ = _ := advancedTargetPoint.symm
                             have advancedTargetRemaining :
                                 ProtocolState.remaining setup.program
                                   (advancedCheckpoint.residual.lift
                                     (ProtocolState.entry
                                       advancedCheckpoint.residual.tail
                                         advancedTarget)) =
                                   instructionCount nextSuffix := by
                               rw [advancedTargetPoint, automaticEnd]
                               change ProtocolState.remaining setup.program
                                 (nextLift (nextBlock.liftPoint nextSuffix
                                   (ProtocolState.entry nextSuffix nextFinished))) = _
                               rw [nextOrigin.remaining_lift,
                                 nextBlock.liftPoint_remaining,
                                 ProtocolState.remaining_entry]
                             have advancedTargetMask : phaseLast.excluded =
                                 (following.drain
                                   (live)).excluded := by
                               rw [automaticEnd, automaticMask, targetMask,
                                 following.drain_excluded]
                               rfl
                             have advancedTargetGeneration :
                                 phaseLast.generation = generation := by
                               rw [automaticEnd]
                               exact targetGeneration
                             have advancedAtPoint : phaseLast =
                                 CommitRecoveryState.atPoint
                                   (advancedCheckpoint.residual.lift
                                     (ProtocolState.entry
                                       advancedCheckpoint.residual.tail advancedTarget))
                                         (following.drain live).excluded generation := by
                               calc
                                 phaseLast = CommitRecoveryState.atPoint phaseLast.point
                                     phaseLast.excluded phaseLast.generation := by
                                   rw [automaticEnd]
                                   rfl
                                 _ = _ := by
                                   rw [← advancedTargetPoint, advancedTargetMask,
                                     advancedTargetGeneration]
                             have advancedEndpointMask : nextCurrent.excluded =
                                 (following.drain live).excluded := by
                               rw [following.drain_excluded]
                               exact endpointMask
                             have phaseClock := setup.commitRecovery_same_generation_length
                               (setup.proposalRecoveryEraseTrace_prefix
                                 targetToPhase).reachesWithin
                                   targetState phaseLast rfl rfl
                                     (targetGeneration.trans
                                       advancedTargetGeneration.symm)
                             have advancedClock :
                                 ProtocolState.remaining setup.program
                                     nextCurrent.point + nextMapped.trace.length =
                                   ProtocolState.remaining setup.program phaseLast.point +
                                     phaseTrace.length := by
                               simp only [setup.proposalRecoveryEraseTrace_length] at phaseClock
                               exact targetClock.trans phaseClock.symm
                             exact ih generation (following.drain live) retired
                                 advancedWitness advancedTarget phaseLast phaseTrace
                                   advancedAtPoint phaseToNext advancedTargetRawAgrees
                                     advancedEndpointMask advancedClock nextAfterFollowing
                                       observedCell
                           | reveal =>
                             let count := following.high - following.low
                             have revealLow : following.low =
                                 cursorState.attempt.phase := rfl
                             have revealHigh : following.high =
                                 cursorState.attempt.phase + count := by
                               dsimp only [count]
                               have positive := following.nonempty
                               omega
                             let prefixed :=
                               cursor.compiled.revealPrefix_of_phase setup.program
                                 (.concurrent) cursor.residual.tail cursor.refs
                                   cursor.source.revelations cursor.registry
                                     cursor.embedding cursor.before
                                       cursorState.attempt.phase following kind
                                         revealLow count revealHigh
                             let assignedStore :=
                               (sourceSnapshotState setup implementation G reference
                                 lost (following.drain live).native).config.store
                             have revealRows :
                                 ∀ (rows : Nat) {Γ : SourceCtx Player L}
                                   {O : Finset VarId}
                                   (program : SourceProgram Player L Γ O)
                                    (revealPrefix : RevealPrefix program rows)
                                   (refs : ContextRefs
                                     (graphLayout setup.program) Γ)
                                   (revelations : Revelations Γ)
                                   (registry : Registry Γ)
                                   (embedding : OutputEmbedding
                                     (inputLayout setup.context)
                                     (outputLayout setup.program) program)
                                   (before : ContextRefsBefore refs embedding)
                                   (offset : Nat),
                                   CompiledSuffix setup.program program refs
                                     revelations registry embedding before offset →
                                   ∀ (lift : ProtocolState program →
                                     ProtocolState setup.program),
                                     (∀ point,
                                       ProtocolState.atCommit setup.program
                                         (lift point) =
                                         ProtocolState.atCommit program point) →
                                     (∀ point excluded joint,
                                       ProtocolState.recoveryStep setup.program
                                         (lift point) excluded joint =
                                         (ProtocolState.recoveryStep program point
                                           excluded joint).map
                                           (fun result =>
                                             (lift result.1, result.2))) →
                                     (∀ index : Fin (eventCount program),
                                       index.val < rows → ∀ owner,
                                       (serviceGraph setup .concurrent).actor?
                                         (embedding.event index) = some owner →
                                       owner ∈ live.excluded) →
                                     (∀ index : Fin (eventCount program),
                                       index.val < rows → ∀ payload
                                       (output : (serviceGraph setup .concurrent).outputLayout
                                         (embedding.event index) =
                                           .publication payload),
                                       (⟨.inr (embedding.event index), output⟩ :
                                         FieldRef (graphLayout setup.program)
                                           (.publication payload)).get?
                                             assignedStore = some .failure) →
                                     ∀ (entry : SourceProgram.Config Player L Γ),
                                       refs.Agrees entry.state assignedStore →
                                       ∀ (last : CommitRecoveryState setup.program)
                                         (joints : List (Player → Option
                                           (CommitRecoveryMove Player L)))
                                         (addresses : List (Option Nat ×
                                           (Finset Player × Nat × Nat))),
                                         CommitRecoveryState.InstructionPath
                                           setup.program
                                           (setup.initialConfig
                                             setup.initialLaw.support_nonempty.choose)
                                           joints addresses
                                           (CommitRecoveryState.atPoint
                                             (lift (ProtocolState.entry program entry))
                                             live.excluded generation) last →
                                         joints.length = rows →
                                         ∃ final : SourceProgram.Config Player L
                                            (revealTail rows program revealPrefix).context,
                                           last = CommitRecoveryState.atPoint
                                              (lift ((revealTail rows program revealPrefix).lift
                                               (ProtocolState.entry
                                                  (revealTail rows program revealPrefix).tail
                                                   final))) live.excluded generation ∧
                                            (revealTailRefs setup rows program revealPrefix
                                             refs embedding).Agrees final.state
                                               assignedStore := by
                               intro rows
                               induction rows with
                               | zero =>
                                   intro Γ O program revealPrefix refs revelations registry
                                     embedding before offset compiled lift atCommit
                                       stepEq rowOwners rowFailures entry entryAgree
                                         last joints addresses path length
                                   have empty : joints = [] :=
                                     List.length_eq_zero_iff.mp length
                                   subst joints
                                   cases path with
                                   | refl => exact ⟨entry, rfl, entryAgree⟩
                               | succ previous ih =>
                                   intro Γ O program revealPrefix refs revelations registry
                                     embedding before offset compiled lift atCommit
                                       stepEq rowOwners rowFailures entry entryAgree
                                         last joints addresses path length
                                   cases program with
                                   | ret _ => exact revealPrefix.elim
                                   | sample _ _ _ _ => exact revealPrefix.elim
                                   | commit _ _ _ _ _ => exact revealPrefix.elim
                                   | @reveal Γ O published owner name payload fresh
                                       selected unresolved next =>
                                       cases path with
                                       | refl => simp only [List.length_nil] at length; omega
                                       | @step first middle last joint rest addresses
                                           legal supported later =>
                                           let headIndex : Fin
                                               (eventCount (.reveal published owner
                                                 name fresh selected unresolved
                                                   next)) :=
                                             ⟨0, by simp only [eventCount]; omega⟩
                                           let headEvent := embedding.event headIndex
                                           have outputEq :
                                               (serviceGraph setup .concurrent).outputLayout
                                                 headEvent =
                                                   .publication payload := by
                                             change outputLayout setup.program
                                               (embedding.event headIndex) =
                                                 .publication payload
                                             simpa only [headIndex, outputLayout,
                                               Fin.mk_zero, Fin.cases_zero] using
                                                 embedding.layout_eq headIndex
                                           have codeEq : cast
                                               (congrArg (EventCode
                                                 (graphLayout setup.program)) outputEq)
                                               ((serviceGraph setup .concurrent).nodes headEvent) =
                                               .resolve owner payload
                                                 (refs.get selected)
                                                   (compileChecks
                                                     (published := published)
                                                       refs registry revelations
                                                         selected) := by
                                             simpa only [headEvent, headIndex,
                                               EventGraph.withMode_nodes, Setup.eventGraph,
                                               compileRankedNodes, outputLayout,
                                               Fin.mk_zero, Fin.cases_zero] using
                                                 compiled.nodeEq headIndex
                                           have acting :
                                               (serviceGraph setup .concurrent).actor?
                                                 headEvent = some owner :=
                                             (EventCode.actor_cast outputEq _).symm.trans
                                               (congrArg EventCode.actor codeEq)
                                           have ownerExcluded : owner ∈ live.excluded :=
                                             rowOwners headIndex
                                               (by change 0 < previous + 1; omega)
                                                 owner acting
                                           let kept := {
                                             revealSuccessor published selected entry
                                               false with history := entry.history }
                                           have headFailure :
                                               (revealSuccessor published selected entry
                                                 false).state.get .here = .failure :=
                                             disclosureResult_false published selected
                                               entry
                                           let headRef : FieldRef
                                               (graphLayout setup.program)
                                                 (.publication payload) :=
                                             ⟨.inr headEvent, outputEq⟩
                                           have headStored : headRef.get?
                                               assignedStore = some .failure :=
                                             rowFailures headIndex
                                               (by change 0 < previous + 1; omega)
                                                 payload outputEq
                                           have keptState : kept.state =
                                               Env.cons (x := published)
                                                 (τ := .publication payload)
                                                   PublicationResult.failure
                                                     entry.state := by
                                             change Env.cons (x := published)
                                               (τ := .publication payload)
                                               (disclosureResult published selected entry
                                                 false) entry.state = _
                                             rw [disclosureResult_false]
                                           have nextAgree :
                                               (refs.cons (name := published)
                                                 (cell := .publication payload) headRef).Agrees
                                                   kept.state assignedStore := by
                                             rw [keptState]
                                             exact ContextRefs.Agrees.cons refs
                                               entry.state assignedStore entryAgree
                                                 (name := published)
                                                 (cell := .publication payload)
                                                 headRef PublicationResult.failure
                                                   headStored
                                           have headNotCommit :
                                               ProtocolState.atCommit setup.program
                                                 (lift (ProtocolState.entry
                                                   (.reveal published owner name fresh
                                                     selected unresolved next) entry)) =
                                                   false := by
                                             rw [atCommit]
                                             rfl
                                           obtain ⟨rawResult, rawSupport,
                                             middleAtPoint⟩ :=
                                             (CommitRecoveryState.atPoint
                                               (lift (ProtocolState.entry
                                                 (.reveal published owner name fresh
                                                   selected unresolved next) entry))
                                               live.excluded generation).step_noncommit_atPoint
                                               (CommitRecoveryState.atPoint_blockFrontier
                                                 _ _ _) headNotCommit joint middle
                                                   supported
                                           have sourceLaw :
                                               ProtocolState.recoveryStep
                                                 (.reveal published owner name fresh
                                                   selected unresolved next)
                                                   (ProtocolState.entry _ entry)
                                                     live.excluded joint =
                                               PMF.pure
                                                 ((Sum.inr (ProtocolState.entry next
                                                   kept) : ProtocolState _),
                                                     live.excluded) := by
                                             simp only [ProtocolState.entry,
                                               ProtocolState.recoveryStep,
                                               Sum.elim_inl, ownerExcluded,
                                               ↓reduceIte, headFailure,
                                               Finset.insert_eq_of_mem]
                                             rfl
                                           have rawSource := rawSupport
                                           change rawResult ∈
                                             (ProtocolState.recoveryStep setup.program
                                               (lift (ProtocolState.entry
                                                 (.reveal published owner name fresh
                                                   selected unresolved next) entry))
                                                   live.excluded joint).support at rawSource
                                           rw [stepEq, sourceLaw, PMF.pure_map,
                                             PMF.mem_support_pure_iff] at rawSource
                                           have middleExpected : middle =
                                               CommitRecoveryState.atPoint
                                                 (lift (Sum.inr (ProtocolState.entry next
                                                   kept))) live.excluded generation := by
                                             calc
                                               middle = CommitRecoveryState.atPoint
                                                   rawResult.1 rawResult.2 generation :=
                                                 middleAtPoint
                                               _ = _ := by rw [rawSource]
                                           let tailEmbedding := embedding.tail next
                                             (by simp only [eventCount])
                                               (fun _ => rfl)
                                           let tailRefs := refs.cons
                                             (name := published)
                                             (cell := .publication payload) headRef
                                           have tailBefore : ContextRefsBefore
                                               tailRefs tailEmbedding := by
                                             intro readName cell selectedRef
                                               remainingRef
                                             cases selectedRef with
                                             | here =>
                                                 change (embedding.event headIndex).val <
                                                   (embedding.event
                                                     (Fin.succ remainingRef)).val
                                                 apply embedding.strictMono
                                                 change 0 < remainingRef.val + 1
                                                 omega
                                             | there selectedRef =>
                                                 exact before selectedRef
                                                   (Fin.succ remainingRef)
                                           have tailCompiled : CompiledSuffix
                                               setup.program next tailRefs
                                                 (revelations.reveal
                                                   (published := published) selected)
                                                   registry.weaken tailEmbedding
                                                     tailBefore (offset + 1) := by
                                             exact compiled.revealTail setup.program
                                               fresh selected unresolved next refs
                                                 revelations registry embedding before
                                                   offset
                                           let tailLift : ProtocolState next →
                                               ProtocolState setup.program :=
                                             fun point => lift (Sum.inr point)
                                           have tailAtCommit : ∀ point,
                                               ProtocolState.atCommit setup.program
                                                 (tailLift point) =
                                                 ProtocolState.atCommit next point := by
                                             intro point
                                             exact atCommit (Sum.inr point)
                                           have tailStepEq : ∀ point excluded joint,
                                               ProtocolState.recoveryStep setup.program
                                                 (tailLift point) excluded joint =
                                                 (ProtocolState.recoveryStep next point
                                                   excluded joint).map
                                                   (fun result =>
                                                     (tailLift result.1, result.2)) := by
                                             intro point excluded joint
                                             have inherited := stepEq (Sum.inr point)
                                               excluded joint
                                             simpa only [ProtocolState.recoveryStep,
                                               Sum.elim_inr, PMF.map_comp, Function.comp_def,
                                               tailLift] using inherited
                                           have tailOwners : ∀ index : Fin
                                               (eventCount next), index.val < previous →
                                               ∀ selectedOwner,
                                                 (serviceGraph setup .concurrent).actor?
                                                   (tailEmbedding.event index) =
                                                     some selectedOwner →
                                                 selectedOwner ∈ live.excluded := by
                                             intro index inside selectedOwner actor
                                             exact rowOwners (Fin.succ index)
                                               (by simp only [Fin.val_succ]; omega)
                                                 selectedOwner (by
                                                   simpa only [tailEmbedding,
                                                     OutputEmbedding.tail,
                                                     Fin.cast_eq_self] using actor)
                                           have tailFailures : ∀ index : Fin
                                               (eventCount next), index.val < previous →
                                               ∀ selectedPayload
                                                 (output :
                                                   (serviceGraph setup .concurrent).outputLayout
                                                       (tailEmbedding.event index) =
                                                         .publication
                                                           selectedPayload),
                                                 (⟨.inr (tailEmbedding.event index),
                                                   output⟩ : FieldRef
                                                     (graphLayout setup.program)
                                                       (.publication selectedPayload)).get?
                                                     assignedStore =
                                                   some .failure := by
                                             intro index inside selectedPayload output
                                             simpa only [tailEmbedding,
                                               OutputEmbedding.tail,
                                               Fin.cast_eq_self] using
                                                 rowFailures (Fin.succ index)
                                                   (by simp only [Fin.val_succ]; omega)
                                                     selectedPayload output
                                           have tailLength : rest.length = previous := by
                                             simpa only [List.length_cons,
                                               Nat.succ.injEq] using length
                                           rw [middleExpected] at later
                                           obtain ⟨final, finalAtPoint,
                                             finalAgree⟩ :=
                                              ih next revealPrefix tailRefs
                                               (revelations.reveal
                                                 (published := published) selected)
                                                   registry.weaken tailEmbedding
                                                     tailBefore (offset + 1)
                                                       tailCompiled tailLift tailAtCommit
                                                         tailStepEq tailOwners
                                                           tailFailures kept nextAgree
                                                             last rest addresses later
                                                               tailLength
                                           exact ⟨final, finalAtPoint, finalAgree⟩
                             have graphOrder :=
                               (toEventGraph setup.program).withMode_revealRelaxedOrdered
                                 (toEventGraph_barrierOrdered setup.program)
                                   (.concurrent)
                             have assignedPublic
                                 (field : (serviceGraph setup .concurrent).Field)
                                 (visible : (serviceGraph setup .concurrent).fieldPublic
                                   field) :
                                 (sourceSnapshotState setup implementation G reference
                                   lost (following.drain live).native).config.store
                                     field =
                                   (following.drain live).native.config.store
                                     field := by
                               simp only [sourceSnapshotState, State.swap_config,
                                 Config.swap_store]
                               exact ValueSwap.store_public _ _ field visible
                             have failedAt : ∀ index : Fin
                                 (eventCount cursor.residual.tail),
                                 index.val < count →
                                   (following.drain live).native.PublicFailure
                                     (cursor.embedding.event index) := by
                               intro index inside
                               have rank := cursor.compiled.rankEq index
                               have lower : following.low ≤
                                   (cursor.embedding.event index).val := by
                                 change (cursor.embedding.event index).val =
                                   cursorState.attempt.phase + index.val at rank
                                 rw [rank]
                                 change cursorState.attempt.phase ≤ _
                                 omega
                               have upper : (cursor.embedding.event index).val <
                                   following.high := by
                                 rw [rank, revealHigh]
                                 change cursorState.attempt.phase + index.val <
                                   cursorState.attempt.phase + count
                                 omega
                               have member := (following.mem_events _).mpr
                                 ⟨lower, upper⟩
                               have fields := following.fields
                                 (cursor.embedding.event index) lower upper
                               rw [kind] at fields
                               obtain ⟨payload, publication⟩ := fields
                               exact automaticFinishedPublicFailures following live
                                 followingStart witness.order.coverage.active
                                   graphOrder followingFinished
                                     (cursor.embedding.event index) member
                                       (by rw [publication]; trivial)
                             have failedRows : ∀ index : Fin
                                 (eventCount cursor.residual.tail),
                                 index.val < count → ∀ selectedPayload
                                   (output :
                                     (serviceGraph setup .concurrent).outputLayout
                                       (cursor.embedding.event index) =
                                         .publication selectedPayload),
                                   (⟨.inr (cursor.embedding.event index), output⟩ :
                                     FieldRef (graphLayout setup.program)
                                       (.publication selectedPayload)).get?
                                         assignedStore = some .failure := by
                               intro index inside selectedPayload output
                               let event := cursor.embedding.event index
                               let native := (following.drain live).native
                               let read : FieldRef (graphLayout setup.program)
                                   (.publication selectedPayload) :=
                                 ⟨.inr event, output⟩
                               have failed : native.PublicFailure event :=
                                 failedAt index inside
                               have available :
                                   (native.config.store read.field).isSome = true := by
                                 change (native.config.outputs event).isSome = true
                                 exact (native.config.output_available event).mpr
                                   failed.completed
                               have readSome := read.get?_isSome native.config.store
                                 available
                               let value := (read.get? native.config.store).get
                                 readSome
                               have rawRead : read.get? native.config.store =
                                   some value := (Option.some_get _).symm
                               have visible :
                                   (serviceGraph setup .concurrent).fieldPublic
                                     (.inr event) := by
                                 change ((serviceGraph setup .concurrent).outputLayout
                                   event).IsPublic
                                 rw [output]
                                 trivial
                               have sameRead : read.get? assignedStore =
                                   read.get? native.config.store :=
                                 read.get?_congr assignedStore native.config.store
                                   (assignedPublic (.inr event) visible)
                               cases viewed : nodeView
                                   (serviceGraph setup .concurrent) event with
                               | bind owner payload shape code =>
                                   cases shape.symm.trans output
                               | sample payload law shape code =>
                                   cases shape.symm.trans output
                               | resolve owner payload binding checks shape code =>
                                   have samePayload : payload = selectedPayload :=
                                     EventField.publication.inj
                                       (shape.symm.trans output)
                                   subst payload
                                   have typedRead :
                                       (⟨.inr event, shape⟩ : FieldRef
                                         (graphLayout setup.program)
                                           (.publication selectedPayload)).get?
                                             native.config.store = some value := by
                                     simpa only [read, FieldRef.get?] using rawRead
                                   have valueFailure : value = .failure :=
                                     (publication_failure_iff_read native event binding
                                       checks shape code value typedRead).mp failed
                                   exact sameRead.trans
                                     (rawRead.trans (congrArg some valueFailure))
                             have imageOrder :=
                               following.orderedPublicFailures_drain following.low
                                 (live).excluded
                                   (live)
                                     (seedOrder.publicationOrder following seedMember)
                                       seedOrder.coverage.active
                                         seedOrder.coverage.inherited graphOrder
                             obtain ⟨revealedCheckpoint, revealedPrefix,
                               revealedSteps, revealedAddresses, revealedHistory,
                               revealedIntended, revealedReplay⟩ :=
                               cursor.after_reveal following rest
                                 seedInstalled kind seedReceipts.exclusion
                                   (fun _ _ present => present)
                                     (⟨[], by simp⟩ :
                                       (⟨following :: rest, generation,
                                         live,
                                         live,
                                         retired⟩ :
                                           PhaseRuntimeState
                                             (serviceGraph setup .concurrent)).HistoryCheckpoint)
                                         (following.drain_reachable live
                                           seedNative.reachable) imageOrder
                                           followingFinished
                             obtain ⟨_revealFuel, revealPath⟩ := revealedPrefix
                             have planMember : following ∈
                                 implementation.plan.phases :=
                               witness.suffix.subset (by
                                 rw [seedInstalled]
                                 exact List.mem_cons_self)
                             have revealedNative : ∃ inputs,
                                 (following.drain live).native.Invariant inputs :=
                               ⟨witness.native.choose,
                                 following.drain_invariant
                                   (live)
                                     witness.native.choose_spec.active⟩
                             obtain ⟨revealedAligned, revealedChronology,
                               revealedOrigins, _revealedDelta⟩ :=
                               cursor.public_phase_archive
                                 implementation.plan operational.maximalPhases
                                   following rest seedInstalled planMember
                                     (by simp only [kind]; decide)
                                       witness.aligned witness.chronology
                                         witness.origins witness.exclusions
                                           witness.failures witness.archives
                                             witness.receipts witness.stored
                                               witness.remembered witness.order
                                                 revealedNative followingFinished
                                                   revealedCheckpoint revealPath
                                                     revealedSteps revealedAddresses
                                                       revealedHistory revealedReplay
                             let revealedWitness :=
                               witness.completed_phase_checkpoint following rest
                                 seedInstalled followingFinished revealedCheckpoint
                                   revealedAligned revealedChronology revealedOrigins
                             have revealEntryAgrees : cursor.refs.Agrees
                                 targetSource.state assignedStore := by
                               apply sourceReplayEntryAgreesOfPreserved setup
                                 implementation cursor.refs targetSource G
                                   reference lost live.native
                                     (following.drain live).native targetAgrees
                               · intro name cell source
                                 let field := (cursor.refs.get source).field
                                 have occupied := targetAgrees source
                                 cases stored : live.native.config.store field with
                                 | none =>
                                     have swappedEmpty :
                                         (sourceSnapshotState setup implementation G
                                           reference lost live.native).config.store
                                             field = none := by
                                       simp only [sourceSnapshotState,
                                         State.swap_config, Config.swap_store,
                                         ValueSwap.store, stored, Option.map_none]
                                     have emptyRead :
                                         (cursor.refs.get source).get?
                                           (sourceSnapshotState setup implementation G
                                             reference lost live.native).config.store =
                                           none := by
                                       unfold FieldRef.get?
                                       rw [swappedEmpty]
                                       exact castOptionNone
                                         (cursor.refs.get source).layout_eq
                                     rw [emptyRead] at occupied
                                     cases occupied
                                 | some value =>
                                     exact (following.drain_keepsStore live field value
                                       stored).symm
                               · intro name cell source _owner _payload _shape _value
                                   _stored
                                 exact (congrFun (following.drain_tables live).1
                                   (cursor.refs.get source).field).symm
                             obtain ⟨revealedTarget, revealedAtPoint,
                               revealedTargetAgrees⟩ :=
                               revealRows count cursor.residual.tail prefixed
                                 cursor.refs cursor.source.revelations cursor.registry
                                   cursor.embedding cursor.before
                                     cursorState.attempt.phase cursor.compiled
                                       cursor.residual.lift cursor.atCommit cursor.step
                                         (by
                                           intro index inside owner acting
                                           have rank := cursor.compiled.rankEq index
                                           change (cursor.embedding.event index).val =
                                             cursorState.attempt.phase + index.val at rank
                                           have lower : following.low ≤
                                               (cursor.embedding.event index).val := by
                                             rw [rank, revealLow]
                                             omega
                                           have upper :
                                               (cursor.embedding.event index).val <
                                                 following.high := by
                                             rw [rank, revealHigh]
                                             omega
                                           have member :=
                                             (following.mem_events _).mpr
                                               ⟨lower, upper⟩
                                           obtain ⟨actualOwner, actualActor,
                                             inherited⟩ :=
                                             source_automatic_finished_event_owner setup
                                               following live
                                               followingStart followingFinished
                                                 (cursor.embedding.event index)
                                                   member
                                           exact (Option.some.inj
                                             (actualActor.symm.trans acting)) ▸
                                               inherited)
                                           failedRows targetSource
                                             revealEntryAgrees phaseLast phaseJoints
                                               phaseAddresses
                                                 (by simpa only [targetAtPoint] using
                                                   phasePath)
                                                   (by simpa only [count] using
                                                     phaseRows)
                             let revealTail := Vegas.revealTail count
                               cursor.residual.tail prefixed
                             let revealResidual : ResidualProgram setup.program :=
                               ⟨revealTail.context, revealTail.names, revealTail.tail,
                                 fun point => cursor.residual.lift
                                   (revealTail.lift point)⟩
                             have revealOrigin : ProtocolSuffix setup.program
                                 revealTail.tail revealResidual.lift :=
                               cursor.origin.compose
                                 (revealTail_protocolSuffix count
                                   cursor.residual.tail prefixed)
                             have revealCompiled :=
                               cursor.compiled.revealTailMany setup count
                                 cursor.residual.tail prefixed cursor.refs
                                   cursor.source.revelations cursor.registry
                                     cursor.embedding cursor.before
                                       cursorState.attempt.phase
                             have revealReadout :=
                               cursor.terminalAlignment.revealTailMany setup count
                                 cursor.residual.tail prefixed cursor.refs
                                   cursor.embedding
                             let selectedRevealed := revealedWitness.checkpoint
                             have revealPhase :
                                 (⟨rest, generation, following.drain live,
                                   following.drain live, retired⟩ :
                                     PhaseRuntimeState
                                       (serviceGraph setup .concurrent)).attempt.phase =
                                   following.high := by
                               change PhaseRuntimeState.phaseLow rest = following.high
                               exact nextLow
                             have revealResidualEq : selectedRevealed.residual =
                                 revealResidual := by
                               apply selectedRevealed.origin.residual_eq_of_instructionCount
                                 revealTail.tail
                                   revealResidual.lift revealOrigin
                               have selectedCount :=
                                 selectedRevealed.compiled.countEq
                               rw [revealPhase, revealHigh] at selectedCount
                               have firstCount := cursor.compiled.countEq
                               have tailWidth := eventCount_revealTail count
                                 cursor.residual.tail prefixed
                               simp only [eventCount_eq_instructionCount]
                                 at selectedCount firstCount tailWidth
                               change count + instructionCount revealTail.tail =
                                 instructionCount cursor.residual.tail at tailWidth
                               have total :
                                   (cursorState.attempt.phase + count) +
                                     instructionCount selectedRevealed.residual.tail =
                                   (cursorState.attempt.phase + count) +
                                     instructionCount revealTail.tail := by
                                 calc
                                   _ = instructionCount setup.program := selectedCount
                                   _ = cursorState.attempt.phase +
                                       instructionCount cursor.residual.tail := firstCount.symm
                                   _ = _ := by rw [← tailWidth, Nat.add_assoc]
                               exact Nat.add_left_cancel total
                             have revealRefsEq :
                                 cast (congrArg (fun residual :
                                   ResidualProgram setup.program =>
                                     ContextRefs (graphLayout setup.program)
                                       residual.context) revealResidualEq)
                                       selectedRevealed.refs =
                                   revealTailRefs setup count cursor.residual.tail
                                     prefixed cursor.refs cursor.embedding := by
                               have readoutRefs
                                   {left right : ResidualProgram setup.program}
                                   (equal : left = right)
                                   (leftRefs : ContextRefs
                                     (graphLayout setup.program) left.context)
                                   (rightRefs : ContextRefs
                                     (graphLayout setup.program) right.context)
                                   (leftEmbedding : OutputEmbedding
                                     (inputLayout setup.context)
                                     (outputLayout setup.program) left.tail)
                                   (rightEmbedding : OutputEmbedding
                                     (inputLayout setup.context)
                                     (outputLayout setup.program) right.tail)
                                   (leftReadout : CompiledReadoutSuffix setup.program
                                     left.tail leftRefs leftEmbedding)
                                   (rightReadout : CompiledReadoutSuffix setup.program
                                     right.tail rightRefs rightEmbedding) :
                                   cast (congrArg (fun residual :
                                     ResidualProgram setup.program =>
                                       ContextRefs (graphLayout setup.program)
                                         residual.context) equal) leftRefs =
                                     rightRefs := by
                                 cases equal
                                 exact CompiledReadoutSuffix.refs_eq setup.program
                                   leftReadout rightReadout
                               exact readoutRefs revealResidualEq
                                 selectedRevealed.refs
                                   (revealTailRefs setup count cursor.residual.tail
                                     prefixed cursor.refs cursor.embedding)
                                     selectedRevealed.embedding
                                       (revealTailEmbedding setup count
                                         cursor.residual.tail prefixed
                                           cursor.embedding)
                                         selectedRevealed.terminalAlignment
                                           revealReadout
                             let nextTarget : SourceProgram.Config Player L
                                 selectedRevealed.residual.context :=
                               cast (congrArg (fun residual :
                                 ResidualProgram setup.program =>
                                   SourceProgram.Config Player L residual.context)
                                     revealResidualEq.symm) revealedTarget
                             have nextTargetRawAgrees :
                                 selectedRevealed.refs.Agrees nextTarget.state
                                   assignedStore := by
                               have transportAgreement
                                   {left right : ResidualProgram setup.program}
                                   (equal : left = right)
                                   (leftRefs : ContextRefs
                                     (graphLayout setup.program) left.context)
                                   (rightRefs : ContextRefs
                                     (graphLayout setup.program) right.context)
                                   (sameRefs : cast (congrArg (fun residual :
                                     ResidualProgram setup.program =>
                                       ContextRefs (graphLayout setup.program)
                                         residual.context) equal) leftRefs = rightRefs)
                                   (rightSource : SourceProgram.Config Player L
                                     right.context)
                                   (store : Store (graphLayout setup.program)) :
                                   rightRefs.Agrees rightSource.state store →
                                     leftRefs.Agrees
                                       (cast (congrArg (fun residual :
                                         ResidualProgram setup.program =>
                                           SourceProgram.Config Player L
                                             residual.context) equal.symm)
                                               rightSource).state store := by
                                 cases equal
                                 cases sameRefs
                                 exact id
                               intro name cell source
                               exact transportAgreement revealResidualEq
                                 selectedRevealed.refs
                                   (revealTailRefs setup count cursor.residual.tail
                                     prefixed cursor.refs cursor.embedding)
                                     revealRefsEq revealedTarget assignedStore
                                       revealedTargetAgrees source
                             have nextTargetPoint :
                                 selectedRevealed.residual.lift
                                   (ProtocolState.entry selectedRevealed.residual.tail
                                     nextTarget) = phaseLast.point := by
                               have pointAfterTransport
                                   {left right : ResidualProgram setup.program}
                                   (equal : left = right)
                                   (source : SourceProgram.Config Player L
                                     right.context) :
                                   left.lift (ProtocolState.entry left.tail
                                     (cast (congrArg (fun residual :
                                       ResidualProgram setup.program =>
                                         SourceProgram.Config Player L
                                           residual.context) equal.symm) source)) =
                                     right.lift
                                       (ProtocolState.entry right.tail source) := by
                                 cases equal
                                 rfl
                               exact (pointAfterTransport revealResidualEq
                                 revealedTarget).trans (by
                                   rw [revealedAtPoint]
                                   rfl)
                             have revealedWhole : phaseLast =
                                 CommitRecoveryState.atPoint
                                   (selectedRevealed.residual.lift
                                     (ProtocolState.entry selectedRevealed.residual.tail
                                       nextTarget))
                                     (following.drain live).excluded generation := by
                               calc
                                 phaseLast = CommitRecoveryState.atPoint phaseLast.point
                                     phaseLast.excluded phaseLast.generation := by
                                   rw [revealedAtPoint]
                                   rfl
                                 _ = _ := by
                                   rw [← nextTargetPoint, phasePhysicalMask,
                                     following.drain_excluded]
                                   rw [revealedAtPoint]
                                   rfl
                             have revealEndpointMask : nextCurrent.excluded =
                                 (following.drain live).excluded := by
                               rw [following.drain_excluded]
                               exact endpointMask
                             have revealedGeneration : phaseLast.generation =
                                 generation := by
                               rw [revealedAtPoint]
                               rfl
                             have revealClock := setup.commitRecovery_same_generation_length
                               (setup.proposalRecoveryEraseTrace_prefix
                                 targetToPhase).reachesWithin
                                   targetState phaseLast rfl rfl
                                     (targetGeneration.trans
                                       revealedGeneration.symm)
                             have revealAdvancedClock :
                                 ProtocolState.remaining setup.program nextCurrent.point +
                                     nextMapped.trace.length =
                                   ProtocolState.remaining setup.program phaseLast.point +
                                     phaseTrace.length := by
                               simp only [setup.proposalRecoveryEraseTrace_length] at revealClock
                               exact targetClock.trans revealClock.symm
                             exact ih generation (following.drain live) retired
                                 revealedWitness nextTarget phaseLast phaseTrace
                                   revealedWhole phaseToNext nextTargetRawAgrees
                                     revealEndpointMask revealAdvancedClock
                                       nextAfterFollowing observedCell
                           | sample =>
                               exact (automaticSampleUnfinished following live
                                 followingStart kind followingFinished).elim
                         · have nextUnfinished : next.execution.application =
                               (⟨following :: rest, generation, live,
                                 following.drain live, retired⟩ :
                                   PhaseRuntimeState
                                     (serviceGraph setup .concurrent)) := by
                             rw [selectedSettle]
                             simp only [PhaseRuntimeState.settle,
                               followingFinished, ↓reduceIte]
                           have samePhase : cursorState.attempt.phase =
                               next.execution.application.attempt.phase := by
                             rw [nextUnfinished]
                             rfl
                           have sameResidual :=
                             cursor.residual_eq_of_phase_eq chosen samePhase
                           have sameRefs := sourceReplayCheckpointRefsEq setup
                             cursor chosen samePhase
                           have targetRemaining :
                               ProtocolState.remaining setup.program
                                 targetState.point =
                                   instructionCount cursor.residual.tail := by
                             rw [targetPoint, cursor.remaining,
                               ProtocolState.remaining_entry]
                           have finalRemaining :
                               ProtocolState.remaining setup.program
                                 nextCurrent.point =
                                   instructionCount chosen.residual.tail := by
                             rw [nextPoint, chosen.remaining,
                               ProtocolState.remaining_entry]
                           have sameCount := congrArg (fun residual :
                             ResidualProgram setup.program =>
                               instructionCount residual.tail) sameResidual
                           have sameLength : targetTrace.length =
                               nextMapped.trace.length := by omega
                           have sameHistory :=
                             targetToSelected.eq_of_same_length
                               (TracePrefix.refl
                                 (prefixTrace := nextMapped.trace)) sameLength
                           have finalAgrees : cursor.refs.Agrees
                               targetSource.state
                               (sourceSnapshotState setup implementation G reference
                                 lost next.execution.application.entry.native).config.store := by
                             rw [nextUnfinished]
                             exact targetAgrees
                           exact finishCursor cursor targetSource targetState
                               targetTrace targetSaved finalAgrees sameHistory
                                 sameResidual sameRefs observedCell
                  intro observationName observationKind observedCell
                  by_cases commitment : phase.kind = .commitment
                  · have sourceBounds := source_checkpoint_binding_interval setup
                      implementation first operational.maximalPhases phase remaining
                        installedEq commitment
                    obtain ⟨lastState, closed, starting, labeled, _fuel, path, word,
                      intervalLength, startKept, startErase, closedErase,
                      labeledKept, closedSelected, labeledSelected, _closedMass⟩ :=
                      sourceReplayFactualCommitInterval setup implementation operational
                        previous next reference earlier
                          (earlier.extend joint legal moved) referenceTrace
                            (TracePrefix.extend (TracePrefix.refl (prefixTrace := earlier))
                              joint legal moved) retained phase remaining installedEq physical
                                normalized finished commitment effect (Ne.symm same)
                    have startSame := (startKept.trans labeledKept).eq_of_same_length
                      sourceStartKept (by
                        have count := congrArg (fun trace => trace.length) startErase
                        simpa only [sourceStart, setup.proposalRecoveryEraseTrace_length,
                          setup.proposalRecoveryLiftTrace_length] using count)
                    have startTrace : starting = sourceStart.trace :=
                      eq_of_heq (History.mk.inj startSame).2
                    have originalInterval : TracePrefix sourceStart.trace labeled := by
                      rw [← startTrace]
                      exact startKept
                    have originalDepth : labeled.length = sourceStart.trace.length +
                        (ProtocolState.remaining setup.program originalStart.point -
                          ProtocolState.commitEnd setup.program originalStart.point) := by
                      calc
                        labeled.length = starting.length +
                            (first.checkpoint.commitInstructionWord
                              (phase.drain physical).native).length := intervalLength
                        _ = sourceStart.trace.length +
                            (ProtocolState.remaining setup.program originalStart.point -
                              ProtocolState.commitEnd setup.program originalStart.point) := by
                          rw [startTrace, source_commit_instruction_word_length]
                          rfl
                    let sourceClosed : setup.proposalRecoveryProtocol.History :=
                      ⟨some lastState, labeled⟩
                    have sourceClosedCut : TracePrefix sourceClosed.trace sourceCut.trace :=
                      labeledKept.trans canonicalToCut
                    have rawClosedCut : TracePrefix closed
                        (setup.proposalRecoveryEraseTrace sourceCut.trace) := by
                      rw [← closedErase]
                      exact setup.proposalRecoveryEraseTrace_prefix sourceClosedCut
                    obtain ⟨targetClosed, targetClosedKept, targetClosedLength,
                      targetClosedInfo⟩ :=
                      source_information_prefix setup who
                        (canonicalSource setup implementation operational
                          ⟨some reference, referenceTrace⟩) targetEntry sourceClosed
                            canonicalInfo labeledKept
                    have targetClosedToGSource : TracePrefix targetClosed.trace g.trace :=
                      targetClosedKept.trans entryKept
                    have targetClosedToG : TracePrefix targetClosed.trace G.trace :=
                      targetClosedKept.trans entryToG
                    have targetClosedBeforeNext :
                        TracePrefix targetClosed.trace nextMapped.trace := by
                      have bounded : targetClosed.trace.length ≤ nextMapped.trace.length := by
                        calc
                          targetClosed.trace.length = labeled.length := targetClosedLength
                          _ ≤ (setup.proposalRecoveryLiftTrace
                              (nativeArchiveLabels setup
                                (PhaseProposal.sourceArchive
                                  reference.execution.network.inputs))
                              (checkpointSelection setup implementation operational
                                (earlier.extend joint legal moved)).val.checkpoint.trace).length :=
                            labeledSelected.length_le
                          _ = nextMapped.trace.length := by
                            rw [nextOriginal] at nextDepth
                            exact nextDepth.symm
                      exact commonPrefixOrder targetClosed nextMapped targetEntry
                        targetClosedKept nextEntryKept bounded
                    have targetClosedMetadata := source_information_metadata setup who
                      sourceClosed targetClosed targetClosedInfo
                    rcases targetClosed with ⟨targetClosedState, targetClosedTrace⟩
                    cases targetClosedState with
                    | none => exact targetClosedMetadata.elim
                    | some targetClosedCurrent =>
                        have targetClosedMask : lastState.excluded =
                            targetClosedCurrent.excluded := targetClosedMetadata.2.2.1
                        obtain ⟨targetTailLast, targetTailJoints, targetTailAddresses,
                          targetTailState, targetTailPath, targetTailLength,
                          targetTailWord, targetTailSignals⟩ :=
                          source_instruction_window setup
                            (setup.initialConfig setup.initialLaw.support_nonempty.choose)
                              targetClosedCurrent
                                (setup.proposalRecoveryEraseTrace targetClosedTrace)
                                  (setup.proposalRecoveryEraseTrace nextMapped.trace)
                                    (setup.proposalRecoveryEraseTrace_prefix
                                      targetClosedBeforeNext)
                        have targetTailEndpoint : targetTailLast = nextCurrent := by
                          have endpoint := targetTailState
                          rw [nextState] at endpoint
                          exact Option.some.inj endpoint.symm
                        have targetTailRows : targetTailJoints.length =
                            nextMapped.trace.length - targetClosedTrace.length := by
                          have counted := targetTailLength
                          simp only [setup.proposalRecoveryEraseTrace_length] at counted
                          omega
                        have geometry := first.checkpoint.commit_phase_geometry phase
                          remaining installedEq commitment first.receipts.exclusion.frontier
                            (operational.maximalPhases.suffix first.suffix)
                        generalize decomposition : SourceProgram.commitPhase
                          first.checkpoint.residual.tail = segment at geometry
                        rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
                        dsimp only at geometry
                        let blockLift : ProtocolState (block.prepend suffix) →
                            ProtocolState setup.program := fun point =>
                          first.checkpoint.residual.lift
                            (cast (congrArg ProtocolState reconstruct) point)
                        have blockOrigin : ProtocolSuffix setup.program
                            (block.prepend suffix) blockLift :=
                          transportOrigin reconstruct first.checkpoint.residual.lift
                            first.checkpoint.origin
                        have blockWidth :
                            ProtocolState.remaining setup.program originalStart.point -
                              ProtocolState.commitEnd setup.program originalStart.point =
                                block.length := by
                          dsimp only [originalStart, CommitRecoveryState.atPoint]
                          rw [first.checkpoint.remaining, first.checkpoint.commitEnd,
                            ProtocolState.remaining_entry, ProtocolState.commitEnd_entry,
                            decomposition]
                          change instructionCount first.checkpoint.residual.tail -
                            instructionCount suffix = block.length
                          rw [← reconstruct, block.instructionCount_prepend]
                          omega
                        have blockDepth : labeled.length =
                            sourceStart.trace.length + block.length := by
                          simpa only [blockWidth] using originalDepth
                        have completed := sourceReplayCompletedInterval setup who sourceCut g
                          cutInfo (setup.initialConfig setup.initialLaw.support_nonempty.choose)
                            block suffix blockLift blockOrigin first.checkpoint.source
                              originalStart lastState sourceStart.trace labeled originalInterval
                                sourceClosedCut (by
                                  change first.checkpoint.residual.lift
                                      (ProtocolState.entry first.checkpoint.residual.tail
                                        first.checkpoint.source) =
                                    first.checkpoint.residual.lift
                                      (cast (congrArg ProtocolState reconstruct)
                                        (ProtocolState.entry (block.prepend suffix)
                                          first.checkpoint.source))
                                  rw [transportEntry reconstruct]) (by
                                  simpa only [originalStart, CommitRecoveryState.atPoint]
                                    using sourceBounds.1) (by
                                  change ProtocolState.commitEnd setup.program
                                      (first.checkpoint.residual.lift
                                        (ProtocolState.entry first.checkpoint.residual.tail
                                          first.checkpoint.source)) ≤ instructionCount suffix
                                  rw [first.checkpoint.commitEnd, ProtocolState.commitEnd_entry,
                                    decomposition]) (by
                                  rw [geometry.1]
                                  have nonempty := phase.nonempty
                                  omega) (by
                                  exact blockDepth)
                        obtain ⟨targetFirst, targetLast, targetPrior, targetLastTrace,
                          targetRowEntry, targetFinished, targetExcluded, targetAttempt,
                          addresses, targetInterval, targetFinalKept, targetStartLength,
                          targetEndLength, targetStartInfo, targetEndInfo, targetPoint,
                          targetAtCommit, targetEndpoint, targetMask, targetGeneration,
                          targetPath, targetWord, targetAddress, monotone, targetClosedEq⟩ :=
                            completed
                        have targetEndEq : (⟨some targetLast, targetLastTrace⟩ :
                            setup.proposalRecoveryProtocol.History) =
                              ⟨some targetClosedCurrent, targetClosedTrace⟩ := by
                          exact targetFinalKept.eq_of_same_length targetClosedToGSource
                            (targetEndLength.trans targetClosedLength.symm)
                        have targetClosedCurrentEq : targetClosedCurrent = targetLast := by
                          have stateEq := congrArg
                            (fun history : setup.proposalRecoveryProtocol.History =>
                              history.state) targetEndEq
                          exact Option.some.inj stateEq.symm
                        have targetPriorToG : TracePrefix targetPrior g.trace :=
                          targetInterval.trans targetFinalKept
                        have priorMappedToG : TracePrefix priorMapped.trace g.trace :=
                          priorEntryKept.trans entryKept
                        have targetStartEq : (⟨some targetFirst, targetPrior⟩ :
                            setup.proposalRecoveryProtocol.History) = priorMapped := by
                          apply targetPriorToG.eq_of_same_length priorMappedToG
                          have sourceDepth : sourceStart.trace.length =
                              first.checkpoint.trace.length := by
                            simp only [sourceStart, setup.proposalRecoveryLiftTrace_length]
                          exact targetStartLength.trans (sourceDepth.trans priorDepth.symm)
                        have targetFirstEq : targetFirst = priorCurrent := by
                          have states := congrArg
                            (fun history : setup.proposalRecoveryProtocol.History =>
                              history.state) targetStartEq
                          rw [priorState] at states
                          exact Option.some.inj states
                        have priorRank : ProtocolState.remaining setup.program
                            priorCurrent.point = ProtocolState.remaining setup.program
                              priorCurrent.saved := by
                          rw [priorPoint, priorSavedPoint,
                            first.checkpoint.origin.remaining_lift,
                            first.checkpoint.origin.remaining_lift,
                            ProtocolState.remaining_entry, ProtocolState.remaining_entry]
                        have priorCommit : ProtocolState.atCommit setup.program
                            priorCurrent.point = true := by
                          rw [priorPoint, first.checkpoint.origin.atCommit_lift]
                          have sameEntry {Γ : SourceCtx Player L} {O : Finset VarId}
                              (program : SourceProgram Player L Γ O)
                              (left right : SourceProgram.Config Player L Γ) :
                              ProtocolState.atCommit program
                                     (ProtocolState.entry program left) =
                                ProtocolState.atCommit program
                                  (ProtocolState.entry program right) := by
                            cases program <;> rfl
                          rw [sameEntry first.checkpoint.residual.tail priorLive
                            first.checkpoint.source]
                          exact (first.checkpoint.atCommit _).symm.trans sourceBounds.1
                        have priorEntry := source_commit_entry_eq_atPoint setup priorCurrent
                          (targetFirstEq ▸ targetPrior) priorCommit priorRank
                        have priorSavedEq : priorCurrent.saved = priorCurrent.point := by
                          rw [priorEntry]
                          rfl
                        have targetPointOriginal : targetFirst.point =
                            first.checkpoint.residual.lift
                              (ProtocolState.entry first.checkpoint.residual.tail
                                targetRowEntry) := by
                          rw [targetPoint]
                          dsimp only [blockLift]
                          rw [transportEntry reconstruct]
                        have targetRowEntryEq : targetRowEntry = priorSaved := by
                          apply ProtocolState.entry_injective first.checkpoint.residual.tail
                          apply sourceReplaySuffixInjective setup first.checkpoint.origin
                          calc
                            first.checkpoint.residual.lift
                                (ProtocolState.entry first.checkpoint.residual.tail
                                  targetRowEntry) = targetFirst.point :=
                              targetPointOriginal.symm
                            _ = priorCurrent.point := congrArg CommitRecoveryState.point
                              targetFirstEq
                            _ = priorCurrent.saved := priorSavedEq.symm
                            _ = first.checkpoint.residual.lift
                                  (ProtocolState.entry first.checkpoint.residual.tail
                                    priorSaved) := priorSavedPoint
                        have targetEntryMetadata :
                            first.checkpoint.source.MetadataEq targetRowEntry := by
                          have metadata := source_information_metadata setup who sourceStart
                            ⟨some targetFirst, targetPrior⟩ targetStartInfo
                          obtain ⟨other, otherPoint, related⟩ := config_of_lifted_entry_metadata
                            setup (block.prepend suffix) blockLift blockOrigin
                              first.checkpoint.source targetFirst.point (by
                                have entryPoint : blockLift (ProtocolState.entry
                                    (block.prepend suffix) first.checkpoint.source) =
                                      originalStart.point := by
                                  dsimp only [blockLift, originalStart, CommitRecoveryState.atPoint]
                                  rw [transportEntry reconstruct]
                                rw [entryPoint]
                                exact metadata.1)
                          have equal : other = targetRowEntry :=
                            ProtocolState.entry_injective (block.prepend suffix)
                              (sourceReplaySuffixInjective setup blockOrigin
                                (otherPoint.symm.trans targetPoint))
                          cases equal
                          exact related
                        have targetRows : sourceAttemptTableReads setup targetAttempt suffix
                            (cast (congrArg (fun program => OutputEmbedding
                              (inputLayout setup.context) (outputLayout setup.program)
                                program) reconstruct.symm) first.checkpoint.embedding)
                            (sourceSnapshotState setup implementation G reference lost
                              (phase.drain physical).native) := by
                          have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
                              (PhaseRuntimeState.initial implementation.plan) := by
                            simp only [ReservedConcurrentImplementation.initial,
                              PMF.map_comp, Function.comp_def]
                          have readback := sourceReplayFixedSnapshotTableReads setup values
                            implementation operational reference
                              (sourceCutTrace setup implementation referenceTrace) who event cut g
                              sameInfo good choice properChoice G supported lost next
                                (sourceCutTrace setup implementation
                                  (earlier.extend joint legal moved))
                                (tracePrefix_initializer setup implementation initialEq retained)
                                previous (sourceCutTrace setup implementation earlier)
                                  (tracePrefix_initializer setup implementation initialEq
                                    earlierKept)
                                  first phase remaining installedEq commitment
                                    physical finished (by
                                      simpa only [PhaseRuntimeState.normalize, installedEq]
                                        using normalized) binding effect (Ne.symm same)
                                      stamp restricted first.checkpoint
                                        ⟨some lastState, closed⟩ path word sourceCut
                                          rawClosedCut cutInfo cutGood
                          rw [decomposition] at readback
                          exact readback targetRowEntry targetFirst targetPrior targetFinished
                            targetExcluded targetAttempt ⟨some targetLast, targetLastTrace⟩
                              targetFinalKept targetInterval targetPoint (by
                                simpa only [originalStart, CommitRecoveryState.atPoint]
                                  using targetMask.symm) targetAtCommit targetEndpoint
                                    targetWord (by
                                      have sourceDepth : sourceStart.trace.length =
                                          first.checkpoint.trace.length := by
                                        simp only [sourceStart,
                                          setup.proposalRecoveryLiftTrace_length]
                                      omega) (by
                                      have rawLength := congrArg (fun trace => trace.length)
                                        closedErase
                                      simp only [setup.proposalRecoveryEraseTrace_length]
                                        at rawLength
                                      calc
                                        targetPrior.length + block.length =
                                          sourceStart.trace.length + block.length := by
                                            rw [targetStartLength]
                                        _ = labeled.length := blockDepth.symm
                                        _ = closed.length := rawLength
                                        _ ≤ _ := le_refl _)
                        let targetEmbedding := cast (congrArg (fun program =>
                          OutputEmbedding (inputLayout setup.context)
                            (outputLayout setup.program) program) reconstruct.symm)
                              first.checkpoint.embedding
                        obtain ⟨translated, translatedBefore, translatedEq,
                          compiledBlock, readoutBlock, ⟨viewsBlock⟩⟩ :=
                          transportCompiled reconstruct first.checkpoint.source
                            first.checkpoint.refs first.checkpoint.registry
                              first.checkpoint.embedding first.checkpoint.before
                                previous.execution.application.attempt.phase
                                  first.checkpoint.compiled
                                    first.checkpoint.terminalAlignment
                                      first.checkpoint.residual.lift
                                        first.checkpoint.views
                        have translatedIsTarget : translated = targetEmbedding := translatedEq
                        subst translated
                        have targetCompiled : CompiledSuffix setup.program
                            (block.prepend suffix) first.checkpoint.refs
                              targetRowEntry.revelations first.checkpoint.registry
                                targetEmbedding translatedBefore
                                  previous.execution.application.attempt.phase := by
                          rw [← targetEntryMetadata.2]
                          exact compiledBlock
                        obtain ⟨tailEmbedding, tailBefore, tailCompiled,
                          tailReadout, ⟨tailViews⟩⟩ :=
                          targetAttempt.compiledTail setup.program suffix
                            first.checkpoint.refs first.checkpoint.registry
                              targetEmbedding translatedBefore
                                previous.execution.application.attempt.phase
                                  targetCompiled readoutBlock blockLift viewsBlock
                        let drained := sourceSnapshotState setup implementation G reference
                          lost (phase.drain physical).native
                        have savedCoverage :=
                          (phaseFailureCoverage_history implementation.runtime
                            implementation.leaks implementation.plan inputs
                              implementation.horizon implementation.scheduler rawTrace)
                        have physicalFixed : KeepsFixedCandidates
                            previous.execution.application.entry.native physical.native := by
                          intro handle known
                          rcases effect with
                            ⟨_id, message, native, _found, _reached, handled, rfl⟩ |
                            ⟨command, native, _reached, supported, rfl⟩
                          · have activeFixed :
                                previous.execution.application.current.native.candidates.lookup
                                  handle ≠ .fresh := by
                              rw [bindingRecord.fixed handle known]
                              exact known
                            exact (handle_lookup_of_not_fresh implementation.runtime _ native
                              ⟨message.id, message.payload.packet.call⟩ handle activeFixed
                                handled).trans (bindingRecord.fixed handle known)
                          · change native.candidates.lookup handle =
                              previous.execution.application.entry.native.candidates.lookup
                                handle
                            rw [(environmentStep_tables implementation.runtime _ native
                              command supported).2]
                            exact bindingRecord.fixed handle known
                        have drainedFixed : KeepsFixedCandidates
                            previous.execution.application.entry.native
                              (phase.drain physical).native := by
                          intro handle known
                          rw [(phase.drain_tables physical).2.1]
                          exact physicalFixed handle known
                        have physicalInherited :
                            previous.execution.application.entry.excluded ⊆
                              physical.excluded := by
                          let current := previous.execution.application.current
                          rcases effect with
                            ⟨_id, message, native, _found, _reached, _handled, rfl⟩ |
                            ⟨command, native, _reached, _supported, rfl⟩
                          · exact savedCoverage.inherited.trans
                              (current.inclusionResult_excluded_subset
                                message.payload.packet.call native)
                          · exact savedCoverage.inherited.trans
                              (current.environmentResult_excluded_subset
                                command native)
                        have drainedInherited :
                            previous.execution.application.entry.excluded ⊆
                              (phase.drain physical).excluded := by
                          rw [phase.drain_excluded]
                          exact physicalInherited
                        have visit : SourceReplayVisitImage setup block suffix targetEmbedding
                            targetAttempt drained first.checkpoint.refs := by
                          have entryAgrees : first.checkpoint.refs.Agrees
                              targetRowEntry.state drained.config.store := by
                            rw [targetRowEntryEq]
                            exact oldEntryAgrees
                          exact ⟨entryAgrees, targetRows,
                            decodeCommitAttempt_eq_of_target_rows setup targetAttempt suffix
                              targetEmbedding drained targetRows,
                            target_attempt_state_agrees setup targetAttempt suffix
                              targetEmbedding drained first.checkpoint.refs entryAgrees
                                targetRows⟩
                        by_cases missing : (((phase.drain physical).excluded \
                            previous.execution.application.entry.excluded) ∩
                            phase.owners).Nonempty
                        · have restoredAgreement : first.checkpoint.refs.Agrees
                              priorSaved.state
                                (sourceSnapshotState setup implementation G reference lost
                                  (PhaseRuntimeState.restore previous.execution.application.entry
                                    (phase.drain physical)).native).config.store :=
                            sourceReplayRestoredEntryAgreement setup implementation
                              first.checkpoint.refs priorSaved G reference lost
                                previous.execution.application.entry
                                  (phase.drain physical) priorAgrees
                          by_cases survivors :
                              (phase.owners \ (phase.drain physical).excluded).Nonempty
                          · have retry := PhaseRuntimeState.settle_retry phase remaining
                              previous.execution.application.generation
                                previous.execution.application.entry physical
                                  previous.execution.application.retired finished commitment
                                    missing survivors
                            have nextRetry : next.execution.application =
                                ⟨phase :: remaining,
                                  previous.execution.application.generation + 1,
                                  PhaseRuntimeState.restore
                                    previous.execution.application.entry
                                      (phase.drain physical),
                                  phase.drain (PhaseRuntimeState.restore
                                    previous.execution.application.entry
                                      (phase.drain physical)),
                                  previous.execution.application.retired ++
                                    [⟨⟨phase.low,
                                      previous.execution.application.generation⟩,
                                        (phase.drain physical).native⟩]⟩ := by
                              rw [normalized]
                              simpa only [PhaseRuntimeState.normalize, installedEq] using retry
                            have restoredAtNext : first.checkpoint.refs.Agrees
                                priorSaved.state
                                (sourceSnapshotState setup implementation G reference lost
                                  next.execution.application.entry.native).config.store := by
                              rw [nextRetry]
                              exact restoredAgreement
                            let retrySelected :=
                              (checkpointSelection setup implementation operational
                                (earlier.extend joint legal moved)).val.checkpoint
                            have retryCommitting : ProtocolState.atCommit
                                first.checkpoint.residual.tail
                                  (ProtocolState.entry first.checkpoint.residual.tail
                                    first.checkpoint.source) = true := by
                              have committing := sourceBounds.1
                              change ProtocolState.atCommit setup.program
                                (first.checkpoint.residual.lift
                                  (ProtocolState.entry first.checkpoint.residual.tail
                                    first.checkpoint.source)) = true at committing
                              rw [first.checkpoint.origin.atCommit_lift] at committing
                              exact committing
                            have retryPhase : next.execution.application.attempt.phase =
                                previous.execution.application.attempt.phase := by
                              rw [nextRetry]
                              simp only [PhaseRuntimeState.attempt, installedEq, List.head?_cons,
                                Option.map_some, Option.getD_some]
                            have retryGeneration : next.execution.application.generation =
                                previous.execution.application.generation + 1 := by
                              rw [nextRetry]
                            have retrySurvives : who ∉
                                (setup.commitRecoveryPublic
                                  (some (CommitRecoveryState.atPoint
                                    (retrySelected.residual.lift
                                      (ProtocolState.entry retrySelected.residual.tail
                                        retrySelected.source))
                                      next.execution.application.entry.excluded
                                        next.execution.application.generation))).1 := by
                              change who ∉ next.execution.application.entry.excluded
                              rw [← nextMask]
                              have bounded : TracePrefix nextMapped.trace g.trace :=
                                nextEntryKept.trans entryKept
                              have monotone := setup.commitRecovery_public_excluded_of_reaches
                                (setup.proposalRecoveryEraseTrace_prefix bounded).reachesWithin
                              have metadata := source_information_metadata setup who g
                                sourceCut sameInfo
                              cases g with
                              | mk gState gTrace =>
                                  cases gState with
                                  | none => exact metadata.elim
                                  | some gCurrent =>
                                      have masks : gCurrent.excluded = cut.current.excluded :=
                                        metadata.2.2.1
                                      rw [nextState] at monotone
                                      change nextCurrent.excluded ⊆ gCurrent.excluded at monotone
                                      intro member
                                      exact cut.survives (masks ▸ monotone member)
                            have retryClosedSelected :
                                (⟨some lastState, closed⟩ :
                                  setup.commitRecoveryProtocol.History) =
                                  ⟨_, retrySelected.trace⟩ := by
                              exact first.checkpoint.retry_chosen_history_eq retrySelected
                                (phase.drain physical).native retryCommitting retryPhase
                                  retryGeneration ⟨some lastState, closed⟩
                                    ⟨_, retrySelected.trace⟩ path word
                                      closedSelected.reachesWithin
                                        (ReachesWithin.refl 0 _)
                                          who retrySurvives
                            have retryRawDepth : closed.length = retrySelected.trace.length :=
                              congrArg (fun history : setup.commitRecoveryProtocol.History =>
                                history.trace.length) retryClosedSelected
                            have retryLabeledDepth : labeled.length =
                                retrySelected.trace.length := by
                              have erased := congrArg (fun trace => trace.length) closedErase
                              have erasedLength : labeled.length = closed.length := by
                                simpa only [setup.proposalRecoveryEraseTrace_length]
                                  using erased
                              exact erasedLength.trans retryRawDepth
                            have retryMappedDepth : nextMapped.trace.length =
                                retrySelected.trace.length := by
                              rw [nextOriginal] at nextDepth
                              simpa only [setup.proposalRecoveryLiftTrace_length] using
                                nextDepth
                            have retryMappedClosed :
                                (⟨some targetClosedCurrent, targetClosedTrace⟩ :
                                  setup.proposalRecoveryProtocol.History) = nextMapped := by
                              have depth : targetClosedTrace.length =
                                  nextMapped.trace.length := by
                                calc
                                  targetClosedTrace.length = labeled.length :=
                                    targetClosedLength
                                  _ = retrySelected.trace.length := retryLabeledDepth
                                  _ = nextMapped.trace.length := retryMappedDepth.symm
                              exact targetClosedKept.eq_of_same_length nextEntryKept depth
                            have retryLastState : targetLast = nextCurrent := by
                              have states := congrArg
                                (fun history : setup.proposalRecoveryProtocol.History =>
                                  history.state) retryMappedClosed
                              rw [nextState] at states
                              change some targetClosedCurrent = some nextCurrent at states
                              rw [targetClosedCurrentEq] at states
                              exact Option.some.inj states
                            have retryAfterMask : targetExcluded =
                                (phase.drain physical).excluded := by
                              have finalMask := congrArg CommitRecoveryState.excluded
                                targetClosedEq
                              simp only [CommitRecoveryState.close_excluded,
                                CommitRecoveryState.install] at finalMask
                              calc
                                targetExcluded = targetLast.excluded := finalMask.symm
                                _ = nextCurrent.excluded :=
                                  congrArg CommitRecoveryState.excluded retryLastState
                                _ = next.execution.application.entry.excluded := nextMask
                                _ = (phase.drain physical).excluded := by
                                  rw [nextRetry]
                                  rfl
                            have retryBeforeMask : targetFirst.excluded =
                                previous.execution.application.entry.excluded := by
                              rw [← targetMask]
                              rfl
                            have retryFailed : targetAttempt.failedOwners.Nonempty := by
                              rw [← targetAttempt.newly_excluded,
                                retryAfterMask, retryBeforeMask]
                              obtain ⟨owner, member⟩ := missing
                              exact ⟨owner, (Finset.mem_inter.mp member).1⟩
                            have retryBlockPositive : 0 < block.length := by
                              rw [geometry.1]
                              exact Nat.sub_pos_of_lt phase.nonempty
                            have retryLow : phase.low =
                                previous.execution.application.attempt.phase := by
                              rw [PhaseRuntimeState.attempt, installedEq]
                              rfl
                            have retryPhaseEq : phase =
                                compiledCommitPhase setup.program .concurrent block suffix
                                  targetEmbedding compiledBlock retryBlockPositive := by
                              have adjacent := first.receipts.exclusion.frontier.adjacent
                              have last := first.receipts.exclusion.frontier.last
                              rw [installedEq] at adjacent last
                              have chain := operational.maximalPhases.suffix first.suffix
                              rw [installedEq] at chain
                              exact compiledCommitPhase_eq_of_maximal setup.program .concurrent
                                block suffix targetEmbedding compiledBlock retryBlockPositive
                                  boundary phase remaining adjacent last chain retryLow
                            have retryPhaseOwners : phase.owners = block.owners := by
                              rw [retryPhaseEq]
                              exact compiledCommitPhase_owners setup.program .concurrent block
                                suffix targetEmbedding compiledBlock retryBlockPositive
                            have retrySurvivors : (block.owners \ targetExcluded).Nonempty := by
                              rw [← retryPhaseOwners, retryAfterMask]
                              exact survivors
                            have retryFirstAtEntry : targetFirst =
                                CommitRecoveryState.atPoint
                                  (blockLift (ProtocolState.entry
                                    (block.prepend suffix) targetRowEntry))
                                  targetFirst.excluded targetFirst.generation := by
                              have targetRank : ProtocolState.remaining setup.program
                                  targetFirst.point = ProtocolState.remaining setup.program
                                    targetFirst.saved := by
                                rw [targetFirstEq]
                                exact priorRank
                              have entryState := source_commit_entry_eq_atPoint setup
                                targetFirst targetPrior (by rw [targetFirstEq]; exact priorCommit)
                                targetRank
                              simpa only [targetPoint] using entryState
                            have retryTargetClose : targetLast =
                                CommitRecoveryState.atPoint
                                  (blockLift (ProtocolState.entry (block.prepend suffix)
                                    { targetRowEntry with history := targetFinished.history }))
                                  targetExcluded (targetFirst.generation + 1) := by
                              calc
                                targetLast = (targetFirst.install
                                    (blockLift (block.liftPoint suffix
                                      (ProtocolState.entry suffix targetFinished)),
                                      targetExcluded) monotone).close := targetClosedEq
                                _ = _ := by
                                  rw [installCongr retryFirstAtEntry _ _ monotone]
                                  exact targetAttempt.close_retry_lift setup.program suffix
                                    boundary retryBlockPositive targetFirst.generation
                                      blockLift blockOrigin.remaining_lift
                                        blockOrigin.atCommit_lift
                                          (by
                                            intro point
                                            change ProtocolState.commitOwners setup.program
                                                (first.checkpoint.residual.lift
                                                  (cast (congrArg ProtocolState reconstruct)
                                                    point)) =
                                              ProtocolState.commitOwners
                                                (block.prepend suffix) point
                                            rw [first.checkpoint.owners]
                                            exact castOwners reconstruct point)
                                            blockOrigin.commitEnd_lift (by
                                              intro point
                                              change ProtocolState.history setup.program
                                                  (first.checkpoint.residual.lift
                                                    (cast (congrArg ProtocolState reconstruct)
                                                      point)) =
                                                ProtocolState.history (block.prepend suffix)
                                                  point
                                              rw [first.checkpoint.history]
                                              exact castHistory reconstruct point)
                                              blockOrigin.withHistory_lift retryFailed
                                                retrySurvivors
                            let retryEntry : SourceProgram.Config Player L
                                first.checkpoint.residual.context :=
                              { priorSaved with history := targetFinished.history }
                            have retryPoint : first.checkpoint.residual.lift
                                (ProtocolState.entry first.checkpoint.residual.tail
                                  retryEntry) = retrySelected.residual.lift
                                    (ProtocolState.entry retrySelected.residual.tail
                                      nextSaved) := by
                              calc
                                first.checkpoint.residual.lift
                                    (ProtocolState.entry first.checkpoint.residual.tail
                                      retryEntry) = targetLast.point := by
                                        rw [retryTargetClose, targetRowEntryEq]
                                        change first.checkpoint.residual.lift
                                            (ProtocolState.entry
                                              first.checkpoint.residual.tail retryEntry) =
                                          first.checkpoint.residual.lift
                                            (cast (congrArg ProtocolState reconstruct)
                                              (ProtocolState.entry
                                                (block.prepend suffix) retryEntry))
                                        rw [transportEntry reconstruct]
                                _ = nextCurrent.saved := by
                                  rw [← retryLastState, retryTargetClose]
                                  rfl
                                _ = retrySelected.residual.lift
                                      (ProtocolState.entry retrySelected.residual.tail
                                        nextSaved) := nextSavedPoint
                            have retryResidualEq :=
                              first.checkpoint.residual_eq_of_phase_eq retrySelected
                                retryPhase.symm
                            have retryRefsEq := sourceReplayCheckpointRefsEq setup
                              first.checkpoint retrySelected retryPhase.symm
                            have retryConfigEq :
                                cast (congrArg (fun residual : ResidualProgram setup.program =>
                                  SourceProgram.Config Player L residual.context)
                                    retryResidualEq) retryEntry = nextSaved := by
                              have transport {left right : ResidualProgram setup.program}
                                  (equal : left = right)
                                  (origin : ProtocolSuffix setup.program left.tail left.lift)
                                  (source : SourceProgram.Config Player L left.context)
                                  (result : SourceProgram.Config Player L right.context)
                                  (point : left.lift
                                      (ProtocolState.entry left.tail source) = right.lift
                                        (ProtocolState.entry right.tail result)) :
                                  cast (congrArg (fun residual : ResidualProgram setup.program =>
                                    SourceProgram.Config Player L residual.context) equal)
                                      source = result := by
                                cases equal
                                exact ProtocolState.entry_injective left.tail
                                  (sourceReplaySuffixInjective setup origin point)
                              exact transport retryResidualEq first.checkpoint.origin
                                retryEntry nextSaved retryPoint
                            have retryNextAgrees : retrySelected.refs.Agrees nextSaved.state
                                (sourceSnapshotState setup implementation G reference lost
                                  next.execution.application.entry.native).config.store := by
                              have originalAgrees : first.checkpoint.refs.Agrees
                                  retryEntry.state
                                  (sourceSnapshotState setup implementation G reference lost
                                    next.execution.application.entry.native).config.store := by
                                intro name cell source
                                simpa only [retryEntry] using (restoredAtNext source)
                              have transport {left right : ResidualProgram setup.program}
                                  (equal : left = right)
                                  (leftRefs : ContextRefs (graphLayout setup.program)
                                    left.context)
                                  (rightRefs : ContextRefs (graphLayout setup.program)
                                    right.context)
                                  (refsEq : cast (congrArg (fun residual :
                                    ResidualProgram setup.program => ContextRefs
                                      (graphLayout setup.program) residual.context) equal)
                                        leftRefs = rightRefs)
                                  (leftSource : SourceProgram.Config Player L left.context)
                                  (rightSource : SourceProgram.Config Player L right.context)
                                  (sourceEq : cast (congrArg (fun residual :
                                    ResidualProgram setup.program => SourceProgram.Config
                                      Player L residual.context) equal) leftSource =
                                        rightSource)
                                  (store : Store (graphLayout setup.program)) :
                                  leftRefs.Agrees leftSource.state store →
                                    rightRefs.Agrees rightSource.state store := by
                                cases equal
                                cases refsEq
                                cases sourceEq
                                exact id
                              intro name cell source
                              exact transport retryResidualEq first.checkpoint.refs
                                retrySelected.refs retryRefsEq retryEntry nextSaved
                                  retryConfigEq _ originalAgrees source
                            exact retryNextAgrees observedCell
                          · have exhausted := PhaseRuntimeState.settle_exhausted phase
                              remaining previous.execution.application.generation
                                previous.execution.application.entry physical
                                  previous.execution.application.retired finished commitment
                                    missing survivors
                            let exhaustedRawState : PhaseRuntimeState
                                (serviceGraph setup .concurrent) :=
                              { previous.execution.application with current := physical }
                            obtain ⟨exhaustedRawWitness, exhaustedRawCheckpoint,
                              _exhaustedRawHistory⟩ :=
                              RecoverySourceWitness.raw_closing_checkpoint setup .concurrent
                                implementation.runtime implementation.leaks
                                  implementation.plan previous next first physical effect
                                    (Ne.symm same)
                            have exhaustedRawInstalled : exhaustedRawState.phases =
                                phase :: remaining := installedEq
                            have exhaustedPhase : exhaustedRawState.attempt.phase =
                                phase.low := by
                              simp only [PhaseRuntimeState.attempt, exhaustedRawInstalled,
                                List.head?_cons, Option.map_some, Option.getD_some]
                            let rebuilt := phase.drain (PhaseRuntimeState.restore
                              previous.execution.application.entry (phase.drain physical))
                            have restoredPrefix :
                                (PhaseRuntimeState.restore
                                  previous.execution.application.entry
                                    (phase.drain physical)).native.config.cut.IsPrefix
                                      phase.low := by
                              have positioned := first.receipts.exclusion.frontier.positioned
                              rw [installedEq] at positioned
                              simpa only [PhaseRuntimeState.restore] using positioned.1
                            have rebuiltAll : phase.owners ⊆
                                (PhaseRuntimeState.restore
                                  previous.execution.application.entry
                                    (phase.drain physical)).excluded := by
                              intro owner member
                              change owner ∈ (phase.drain physical).excluded
                              by_contra absent
                              exact survivors ⟨owner,
                                Finset.mem_sdiff.mpr ⟨member, absent⟩⟩
                            have rebuiltFinished : phase.Finished rebuilt := by
                              exact phase.drain_finished_of_excluded
                                (PhaseRuntimeState.restore
                                  previous.execution.application.entry
                                    (phase.drain physical))
                                (restoredPrefix.within phase.nonempty.le)
                                  commitment rebuiltAll
                            have rebuiltEndPrefix :
                                rebuilt.native.config.cut.IsPrefix phase.high := by
                              exact phase.finished_prefix rebuilt
                                (phase.drain_within _
                                  (restoredPrefix.within phase.nonempty.le))
                                    rebuiltFinished
                            have rebuiltRaw : first.checkpoint.refs.Agrees
                                first.checkpoint.source.state rebuilt.native.config.store := by
                              intro name cell source
                              exact (first.checkpoint.refs.get source).get?_preserved _ _
                                (phase.drain_keepsStore _)
                                _ (by
                                  simpa only [PhaseRuntimeState.restore] using
                                    first.checkpoint.agrees source)
                            have rebuiltAssigned : first.checkpoint.refs.Agrees
                                priorSaved.state
                                (sourceSnapshotState setup implementation G reference lost
                                  rebuilt.native).config.store := by
                              apply sourceReplayEntryAgreesOfPreserved setup implementation
                                first.checkpoint.refs priorSaved G reference lost
                                  (PhaseRuntimeState.restore
                                    previous.execution.application.entry
                                      (phase.drain physical)).native
                                    rebuilt.native restoredAgreement
                              · intro name cell source
                                let field := (first.checkpoint.refs.get source).field
                                have occupied : (first.checkpoint.refs.get source).get?
                                    (PhaseRuntimeState.restore
                                      previous.execution.application.entry
                                        (phase.drain physical)).native.config.store =
                                      some (cellValue
                                        (first.checkpoint.source.state.get source)) := by
                                  simpa only [PhaseRuntimeState.restore] using
                                    first.checkpoint.agrees source
                                cases entryStored : (PhaseRuntimeState.restore
                                    previous.execution.application.entry
                                      (phase.drain physical)).native.config.store field with
                                | none =>
                                    have absent : (first.checkpoint.refs.get source).get?
                                        (PhaseRuntimeState.restore
                                          previous.execution.application.entry
                                            (phase.drain physical)).native.config.store =
                                          none := by
                                      unfold FieldRef.get?
                                      rw [entryStored]
                                      exact castOptionNone
                                        (first.checkpoint.refs.get source).layout_eq
                                    rw [absent] at occupied
                                    cases occupied
                                | some value =>
                                    exact (phase.drain_keepsStore _ field value
                                      entryStored).symm
                              · intro _name _cell source _owner _payload _shape _value _stored
                                exact (congrFun (phase.drain_tables _).1
                                  (first.checkpoint.refs.get source).field).symm
                            have nextExhausted : next.execution.application =
                                PhaseRuntimeState.settle remaining
                                  previous.execution.application.generation
                                    rebuilt rebuilt
                                    (previous.execution.application.retired ++
                                      [⟨⟨phase.low,
                                        previous.execution.application.generation⟩,
                                          (phase.drain physical).native⟩]) := by
                              rw [normalized]
                              simpa only [PhaseRuntimeState.normalize, installedEq] using exhausted
                            have exhaustedTailMask :
                                next.execution.application.entry.excluded =
                                  next.execution.application.current.excluded := by
                              rw [nextExhausted]
                              exact PhaseRuntimeState.settle_entry_excluded_of_same
                                remaining previous.execution.application.generation
                                  rebuilt rebuilt
                                    (previous.execution.application.retired ++
                                      [⟨⟨phase.low,
                                        previous.execution.application.generation⟩,
                                          (phase.drain physical).native⟩]) rfl
                            have exhaustedTailGeneration :
                                next.execution.application.generation =
                                  previous.execution.application.generation := by
                              rw [nextExhausted]
                              exact (PhaseRuntimeState.settle_generation_archive_of_same_excluded
                                remaining previous.execution.application.generation
                                  rebuilt rebuilt
                                    (previous.execution.application.retired ++
                                      [⟨⟨phase.low,
                                        previous.execution.application.generation⟩,
                                          (phase.drain physical).native⟩]) rfl).1
                            have exhaustedCommitting : ProtocolState.atCommit
                                first.checkpoint.residual.tail
                                  (ProtocolState.entry first.checkpoint.residual.tail
                                    first.checkpoint.source) = true := by
                              have committing := sourceBounds.1
                              change ProtocolState.atCommit setup.program
                                (first.checkpoint.residual.lift
                                  (ProtocolState.entry first.checkpoint.residual.tail
                                    first.checkpoint.source)) = true at committing
                              rw [first.checkpoint.origin.atCommit_lift] at committing
                              exact committing
                            have chosen := first.checkpoint.chosen_commit_trace
                              (phase.drain physical).native exhaustedCommitting
                                ⟨some lastState, closed⟩ path word
                            rw [decomposition] at chosen
                            let physicalDecoded := decodeCommitAttempt setup.program
                              .concurrent block suffix targetEmbedding
                                (phase.drain physical).native first.checkpoint.source
                                  previous.execution.application.entry.excluded
                            obtain ⟨_chosenTrace, _chosenPath, _chosenWord,
                              chosenEq, _chosenAddresses⟩ := chosen
                            have selectedAfterMask : lastState.excluded =
                                physicalDecoded.2.1 := by
                              have states := congrArg (fun history :
                                  setup.commitRecoveryProtocol.History =>
                                    history.state.map CommitRecoveryState.excluded) chosenEq
                              apply Option.some.inj
                              simpa only [physicalDecoded, Option.map_some,
                                CommitRecoveryState.close_excluded,
                                CommitRecoveryState.install] using states
                            have exhaustedBlockPositive : 0 < block.length := by
                              rw [geometry.1]
                              have positive := phase.nonempty
                              omega
                            have exhaustedLow : phase.low =
                                previous.execution.application.attempt.phase := by
                              rw [PhaseRuntimeState.attempt, installedEq]
                              rfl
                            have exhaustedPhaseEq : phase =
                                compiledCommitPhase setup.program .concurrent block suffix
                                  targetEmbedding compiledBlock exhaustedBlockPositive := by
                              have adjacent := first.receipts.exclusion.frontier.adjacent
                              have last := first.receipts.exclusion.frontier.last
                              rw [installedEq] at adjacent last
                              have chain := operational.maximalPhases.suffix first.suffix
                              rw [installedEq] at chain
                              exact compiledCommitPhase_eq_of_maximal setup.program .concurrent
                                block suffix targetEmbedding compiledBlock exhaustedBlockPositive
                                  boundary phase remaining adjacent last chain exhaustedLow
                            have exhaustedPresent : phase ∈
                                previous.execution.application.phases.head? := by
                              simp only [installedEq, List.head?_cons, Option.mem_some_iff]
                            have exhaustedWithin : (phase.drain physical).native.config.cut.Within
                                previous.execution.application.attempt.phase
                                  (previous.execution.application.attempt.phase +
                                    block.length) := by
                              have positioned :=
                                exhaustedRawWitness.receipts.exclusion.frontier.positioned
                              rw [exhaustedRawInstalled] at positioned
                              have within := phase.drain_within physical positioned.2
                              simpa only [exhaustedPhaseEq, compiledCommitPhase] using within
                            have exhaustedFinished :
                                (compiledCommitPhase setup.program .concurrent block suffix
                                  targetEmbedding compiledBlock exhaustedBlockPositive).Finished
                                    (phase.drain physical) := by
                              rw [← exhaustedPhaseEq]
                              exact finished
                            have decodedPhysical : physicalDecoded.2.1 =
                                (phase.drain physical).excluded := by
                              exact decodeCommitAttempt_excluded_eq_physical setup.program
                                .concurrent block suffix targetEmbedding compiledBlock
                                  exhaustedBlockPositive (phase.drain physical)
                                    first.checkpoint.source
                                      previous.execution.application.entry.excluded
                                        (by
                                          rw [← exhaustedLow]
                                          exact (exhaustedRawWitness.receipts.exclusion.installed
                                            phase exhaustedPresent).phase_drain phase)
                                            exhaustedWithin exhaustedFinished
                            have exhaustedClosedMask : targetClosedCurrent.excluded =
                                (phase.drain physical).excluded :=
                              targetClosedMask.symm.trans
                                (selectedAfterMask.trans decodedPhysical)
                            have exhaustedAfterMask : targetExcluded =
                                (phase.drain physical).excluded := by
                              have finalMask := congrArg CommitRecoveryState.excluded
                                targetClosedEq
                              simp only [CommitRecoveryState.close_excluded,
                                CommitRecoveryState.install] at finalMask
                              calc
                                targetExcluded = targetLast.excluded := finalMask.symm
                                _ = targetClosedCurrent.excluded :=
                                  congrArg CommitRecoveryState.excluded
                                    targetClosedCurrentEq.symm
                                _ = (phase.drain physical).excluded :=
                                  exhaustedClosedMask
                            have exhaustedBeforeMask : targetFirst.excluded =
                                previous.execution.application.entry.excluded := by
                              rw [← targetMask]
                              rfl
                            have exhaustedFailed : targetAttempt.failedOwners.Nonempty := by
                              rw [← targetAttempt.newly_excluded,
                                exhaustedAfterMask, exhaustedBeforeMask]
                              obtain ⟨owner, member⟩ := missing
                              exact ⟨owner, (Finset.mem_inter.mp member).1⟩
                            have exhaustedPhaseOwners : phase.owners = block.owners := by
                              rw [exhaustedPhaseEq]
                              exact compiledCommitPhase_owners setup.program .concurrent block
                                suffix targetEmbedding compiledBlock exhaustedBlockPositive
                            have exhaustedNoSurvivor :
                                ¬ (block.owners \ targetExcluded).Nonempty := by
                              rw [← exhaustedPhaseOwners, exhaustedAfterMask]
                              exact survivors
                            have exhaustedAllOwners : block.owners ⊆ targetExcluded := by
                              intro owner member
                              by_contra absent
                              exact exhaustedNoSurvivor ⟨owner,
                                Finset.mem_sdiff.mpr ⟨member, absent⟩⟩
                            have exhaustedFirstAtEntry : targetFirst =
                                CommitRecoveryState.atPoint
                                  (blockLift (ProtocolState.entry
                                    (block.prepend suffix) targetRowEntry))
                                  targetFirst.excluded targetFirst.generation := by
                              have targetRank : ProtocolState.remaining setup.program
                                  targetFirst.point = ProtocolState.remaining setup.program
                                    targetFirst.saved := by
                                rw [targetFirstEq]
                                exact priorRank
                              have entryState := source_commit_entry_eq_atPoint setup
                                targetFirst targetPrior (by
                                rw [targetFirstEq]
                                exact priorCommit) targetRank
                              simpa only [targetPoint] using entryState
                            have exhaustedTargetClose : targetLast =
                                CommitRecoveryState.atPoint
                                  (blockLift (block.liftPoint suffix
                                    (ProtocolState.entry suffix
                                      (block.automatic { targetRowEntry with
                                        history := targetFinished.history }))))
                                  targetExcluded targetFirst.generation := by
                              calc
                                targetLast = (targetFirst.install
                                    (blockLift (block.liftPoint suffix
                                      (ProtocolState.entry suffix targetFinished)),
                                      targetExcluded) monotone).close := targetClosedEq
                                _ = _ := by
                                  rw [installCongr exhaustedFirstAtEntry _ _ monotone]
                                  exact targetAttempt.close_exhausted_lift setup.program
                                    suffix boundary exhaustedBlockPositive
                                      targetFirst.generation blockLift
                                        blockOrigin.remaining_lift blockOrigin.atCommit_lift
                                          (by
                                            intro point
                                            change ProtocolState.commitOwners setup.program
                                                (first.checkpoint.residual.lift
                                                  (cast (congrArg ProtocolState reconstruct)
                                                    point)) =
                                              ProtocolState.commitOwners
                                                (block.prepend suffix) point
                                            rw [first.checkpoint.owners]
                                            exact castOwners reconstruct point)
                                          blockOrigin.commitEnd_lift (by
                                            intro point
                                            change first.checkpoint.residual.lift
                                                (cast (congrArg ProtocolState reconstruct)
                                                  (ProtocolState.automaticCommitBlock
                                                    (block.prepend suffix) point)) =
                                              ProtocolState.automaticCommitBlock
                                                setup.program (blockLift point)
                                            rw [castAutomatic reconstruct point,
                                              first.checkpoint.automatic])
                                          (by
                                            intro point
                                            change ProtocolState.history setup.program
                                                (first.checkpoint.residual.lift
                                                  (cast (congrArg ProtocolState reconstruct)
                                                    point)) =
                                              ProtocolState.history
                                                (block.prepend suffix) point
                                            rw [first.checkpoint.history]
                                            exact castHistory reconstruct point)
                                          blockOrigin.withHistory_lift exhaustedFailed
                                            exhaustedAllOwners
                            let restored : RecoveryState
                                (serviceGraph setup .concurrent) :=
                              PhaseRuntimeState.restore
                                previous.execution.application.entry (phase.drain physical)
                            have restoredValid : restored.native.BindingInvariant := by
                              exact PhaseRuntimeState.restore_bindingInvariant
                                previous.execution.application.entry (phase.drain physical)
                                  savedBinding drainedFixed
                            have restoredCoverage : restored.FailureCoverage := by
                              exact PhaseRuntimeState.restore_failureCoverage
                                previous.execution.application.entry (phase.drain physical)
                                  savedCoverage.saved drainedInherited
                            let exhaustedEntry : SourceProgram.Config Player L _ :=
                              { priorSaved with history := targetFinished.history }
                            have exhaustedAutomaticRows :
                                sourceAttemptTableReads setup
                                  (block.automaticAttempt exhaustedEntry targetExcluded
                                    exhaustedAllOwners)
                                    suffix targetEmbedding
                                      (sourceSnapshotState setup implementation G reference
                                        lost rebuilt.native) := by
                              have failed : ∀ index : Fin
                                  (eventCount (block.prepend suffix)),
                                  index.val < block.length →
                                  ∀ (owner : Player) (payload : L.Ty)
                                    (shape : outputLayout (block.prepend suffix) index =
                                      .binding owner payload),
                                    (⟨.inr (targetEmbedding.event index),
                                      (targetEmbedding.layout_eq index).trans shape⟩ :
                                        FieldRef (serviceGraph setup .concurrent).layout
                                          (.binding owner payload)).get?
                                      (sourceSnapshotState setup implementation G reference
                                        lost rebuilt.native).config.store = some .failure := by
                                intro index inside owner payload shape
                                have actualShape :
                                    (serviceGraph setup .concurrent).outputLayout
                                      (targetEmbedding.event index) =
                                        .binding owner payload :=
                                  (targetEmbedding.layout_eq index).trans shape
                                have member : targetEmbedding.event index ∈ phase.events := by
                                  rw [exhaustedPhaseEq]
                                  exact (compiledCommitPhase_mem_iff setup.program
                                    (.concurrent) block suffix targetEmbedding compiledBlock
                                      exhaustedBlockPositive _).mpr
                                        ⟨index, inside, rfl⟩
                                exact automaticFinishedBindingRows phase restored
                                  restoredPrefix restoredCoverage restoredValid
                                    (by simpa only [restored, rebuilt] using rebuiltFinished)
                                      (targetEmbedding.event index) member owner payload
                                        actualShape lost
                              exact automaticBindingReads block exhaustedEntry
                                targetExcluded exhaustedAllOwners suffix targetEmbedding
                                  (sourceSnapshotState setup implementation G reference lost
                                    rebuilt.native) failed
                                      (block.automaticAttempt exhaustedEntry targetExcluded
                                        exhaustedAllOwners)
                            have exhaustedAutomaticEntryAgrees :
                                first.checkpoint.refs.Agrees exhaustedEntry.state
                                  (sourceSnapshotState setup implementation G reference lost
                                    rebuilt.native).config.store := by
                              intro name cell source
                              simpa only [exhaustedEntry] using rebuiltAssigned source
                            have exhaustedAutomaticFinalAgrees :
                                (commitBlockRefs setup.program block suffix targetEmbedding
                                  first.checkpoint.refs).Agrees
                                    (block.automatic exhaustedEntry).state
                                    (sourceSnapshotState setup implementation G reference lost
                                      rebuilt.native).config.store :=
                              target_attempt_state_agrees setup
                                (block.automaticAttempt exhaustedEntry targetExcluded
                                  exhaustedAllOwners) suffix targetEmbedding
                                    (sourceSnapshotState setup implementation G reference lost
                                      rebuilt.native) first.checkpoint.refs
                                        exhaustedAutomaticEntryAgrees exhaustedAutomaticRows
                            have exhaustedRawCommitting : ProtocolState.atCommit
                                exhaustedRawWitness.checkpoint.residual.tail
                                  (ProtocolState.entry
                                    exhaustedRawWitness.checkpoint.residual.tail
                                      exhaustedRawWitness.checkpoint.source) = true := by
                              rw [exhaustedRawCheckpoint]
                              exact exhaustedCommitting
                            obtain ⟨⟨exhaustedCheckpoint, exhaustedSourcePrefix,
                              exhaustedSourceWord⟩, exhaustedNormalization⟩ :=
                              exhaustedRawWitness.checkpoint.after_commit_exhausted
                                exhaustedRawCommitting phase remaining
                                  exhaustedRawInstalled
                                    (operational.maximalPhases.suffix
                                      exhaustedRawWitness.suffix)
                                        exhaustedRawWitness.binding
                                          exhaustedRawWitness.receipts
                                            exhaustedRawWitness.stored finished missing survivors
                            have exhaustedSeedPhase :
                                (⟨remaining, exhaustedRawState.generation, rebuilt,
                                  rebuilt, exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩]⟩ :
                                    PhaseRuntimeState
                                      (serviceGraph setup .concurrent)).attempt.phase =
                                  phase.high := by
                              have adjacent :=
                                exhaustedRawWitness.receipts.exclusion.frontier.adjacent
                              have last :=
                                exhaustedRawWitness.receipts.exclusion.frontier.last
                              rw [exhaustedRawInstalled] at adjacent last
                              cases remaining with
                              | nil =>
                                  have ending := last phase (by
                                    simp only [List.getLast?_singleton,
                                      Option.mem_some_iff])
                                  simpa only [PhaseRuntimeState.attempt, List.head?_nil,
                                    Option.map_none, Option.getD_none, serviceGraph,
                                       Setup.eventGraph]
                                       using ending.symm
                              | cons following rest =>
                                  have boundary := adjacent.rel_head? (y := following)
                                    (by simp)
                                  simpa only [PhaseRuntimeState.attempt, List.head?_cons,
                                    Option.map_some, Option.getD_some] using boundary.symm
                            have exhaustedSeedResidual : exhaustedCheckpoint.residual =
                                (⟨Δ, P, suffix, fun point =>
                                  blockLift (block.liftPoint suffix point)⟩ :
                                    ResidualProgram setup.program) := by
                              apply exhaustedCheckpoint.origin.residual_eq_of_instructionCount
                                suffix (fun point => blockLift (block.liftPoint suffix point))
                                  (blockOrigin.compose (block.protocolSuffix suffix))
                              have seedCount := exhaustedCheckpoint.compiled.countEq
                              have tailCount := tailCompiled.countEq
                              rw [exhaustedSeedPhase] at seedCount
                              simp only [eventCount_eq_instructionCount] at seedCount tailCount
                              have width := geometry.1
                              omega
                            have exhaustedSeedRefs :
                                cast (congrArg (fun residual : ResidualProgram setup.program =>
                                  ContextRefs (graphLayout setup.program) residual.context)
                                    exhaustedSeedResidual) exhaustedCheckpoint.refs =
                                  commitBlockRefs setup.program block suffix targetEmbedding
                                    first.checkpoint.refs := by
                              have readoutRefs {left right : ResidualProgram setup.program}
                                  (equal : left = right)
                                  (leftRefs : ContextRefs (graphLayout setup.program)
                                    left.context)
                                  (rightRefs : ContextRefs (graphLayout setup.program)
                                    right.context)
                                  (leftEmbedding : OutputEmbedding (inputLayout setup.context)
                                    (outputLayout setup.program) left.tail)
                                  (rightEmbedding : OutputEmbedding (inputLayout setup.context)
                                    (outputLayout setup.program) right.tail)
                                  (leftReadout : CompiledReadoutSuffix setup.program
                                    left.tail leftRefs leftEmbedding)
                                  (rightReadout : CompiledReadoutSuffix setup.program
                                    right.tail rightRefs rightEmbedding) :
                                  cast (congrArg (fun residual : ResidualProgram
                                    setup.program => ContextRefs (graphLayout setup.program)
                                      residual.context) equal) leftRefs = rightRefs := by
                                cases equal
                                exact CompiledReadoutSuffix.refs_eq setup.program
                                  leftReadout rightReadout
                              exact readoutRefs exhaustedSeedResidual
                                exhaustedCheckpoint.refs
                                (commitBlockRefs setup.program block suffix targetEmbedding
                                  first.checkpoint.refs)
                                    exhaustedCheckpoint.embedding tailEmbedding
                                      exhaustedCheckpoint.terminalAlignment tailReadout
                            obtain ⟨exhaustedFuel, exhaustedPath,
                              exhaustedInstructions⟩ := exhaustedSourcePrefix
                            have rebuiltNative : ∃ nativeInputs,
                                rebuilt.native.Invariant nativeInputs := by
                              obtain ⟨nativeInputs, savedNative, _activeNative⟩ :=
                                exhaustedRawWitness.native
                              have restoredNative := PhaseRuntimeState.restore_invariant
                                previous.execution.application.entry (phase.drain physical)
                                  savedNative
                              exact ⟨nativeInputs,
                                phase.drain_invariant restored restoredNative⟩
                            have rebuiltBinding : rebuilt.native.BindingInvariant :=
                              phase.drain_bindingInvariant restored restoredValid
                            have rebuiltCoverage : rebuilt.FailureCoverage :=
                              restoredCoverage.drain phase
                            have restoredReceipts : restored.native.ReceiptsComplete := by
                              intro event candidate accepted
                              exact exhaustedRawWitness.receipts.exclusion.saved event
                                candidate accepted
                            have exhaustedPosition :=
                              exhaustedRawWitness.receipts.exclusion.frontier.positioned
                            rw [exhaustedRawInstalled] at exhaustedPosition
                            have restoredRecord := SuffixExclusionRecord.of_prefix
                              restoredReceipts exhaustedPosition.1 rfl
                            have rebuiltRecord := restoredRecord.phase_drain phase
                            have rebuiltPrefix : rebuilt.native.config.cut.IsPrefix
                                phase.high := phase.finished_prefix rebuilt
                                  (phase.drain_within restored
                                    (restoredPrefix.within phase.nonempty.le))
                                      rebuiltFinished
                            have exhaustedAdjacent :=
                              exhaustedRawWitness.receipts.exclusion.frontier.adjacent
                            have exhaustedLast :=
                              exhaustedRawWitness.receipts.exclusion.frontier.last
                            rw [exhaustedRawInstalled] at exhaustedAdjacent exhaustedLast
                            have exhaustedNextPosition := PhaseRuntimeState.positioned_next
                              phase remaining rebuilt
                                exhaustedAdjacent exhaustedLast rebuiltPrefix
                            have exhaustedNextFrontier :
                                (⟨remaining, exhaustedRawState.generation, rebuilt, rebuilt,
                                  exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩]⟩ :
                                        PhaseRuntimeState
                                          (serviceGraph setup .concurrent)).Frontier :=
                              ⟨exhaustedNextPosition.adjacent,
                                exhaustedNextPosition.last,
                                  exhaustedNextPosition.positioned⟩
                            have exhaustedArchived :=
                              exhaustedRawWitness.exclusions.active.phase_drain phase
                            have exhaustedArchiveOwners :
                                PhaseRuntimeState.archivedFailureOwners
                                  (exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩]) =
                                    (phase.drain physical).excluded := by
                              have aggregate := exhaustedArchived.failureOwners_union.symm
                              change PhaseRuntimeState.archivedFailureOwners
                                  exhaustedRawState.retired ∪
                                    (phase.drain physical).native.failureOwners =
                                  (phase.drain physical).excluded at aggregate
                              rw [PhaseRuntimeState.archivedFailureOwners_append]
                              simpa only [PhaseRuntimeState.archivedFailureOwners,
                                List.foldr_cons, List.foldr_nil, Finset.union_empty] using aggregate
                            have restoredArchived : SuffixExclusionRecord 0
                                (PhaseRuntimeState.archivedFailureOwners
                                  (exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩])) restored := by
                              rw [exhaustedArchiveOwners]
                              exact restoredCoverage.suffixRecord
                            have rebuiltArchived := restoredArchived.phase_drain phase
                            have exhaustedArchiveBefore :
                                ∀ record ∈ exhaustedRawState.retired ++
                                  [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                    (phase.drain physical).native⟩],
                                  record.attempt.phase ≤ phase.low := by
                              intro record member
                              rcases List.mem_append.mp member with old | new
                              · calc
                                  record.attempt.phase ≤ exhaustedRawState.attempt.phase :=
                                    exhaustedRawWitness.archives record old
                                  _ = phase.low := exhaustedPhase
                              · obtain rfl := List.mem_singleton.mp new
                                exact Nat.le_refl _
                            have exhaustedNextArchives :
                                (⟨remaining, exhaustedRawState.generation, rebuilt, rebuilt,
                                  exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩]⟩ :
                                        PhaseRuntimeState
                                          (serviceGraph setup .concurrent)).ArchivesBefore := by
                              intro record member
                              exact (exhaustedArchiveBefore record member).trans
                                (PhaseRuntimeState.phaseLow_suffix exhaustedAdjacent
                                  (List.suffix_cons phase remaining))
                            have exhaustedNextAligned :
                                exhaustedCheckpoint.ArchivedRecall := by
                              intro who active
                              have activeImage :
                                  who ∉ (phase.drain physical).excluded := by
                                have same : rebuilt.excluded =
                                    (phase.drain physical).excluded :=
                                  phase.drain_excluded restored
                                rwa [same] at active
                              have outside : who ∉ phase.owners :=
                                fun owned => activeImage (rebuiltAll owned)
                              have retained :
                                  List.IsPrefix
                                    previous.execution.application.entry.native.config.history
                                    (phase.drain physical).native.config.history :=
                                exhaustedRawWitness.remembered.trans
                                  (phase.drain_history_prefix physical)
                              have within := phase.drain_within physical
                                exhaustedPosition.2
                              have unchanged := phase.ownCompletions_eq_of_unowned
                                previous.execution.application.entry.native.config
                                  (phase.drain physical).native.config exhaustedPosition.1
                                    within retained who outside
                              have rebuiltUnchanged := phase.drain_ownCompletions
                                restored who activeImage
                              have recovered : PhaseRuntimeState.archivedHistory
                                  (exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩])
                                    previous.execution.application.entry.native.config.history =
                                      PhaseRuntimeState.archivedHistory
                                        exhaustedRawState.retired
                                          (phase.drain physical).native.config.history :=
                                PhaseRuntimeState.archivedHistory_retry
                                  exhaustedRawState.retired
                                    ⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩
                                        previous.execution.application.entry.native.config
                                          exhaustedPosition.1 retained
                              rw [exhaustedSourceWord who activeImage,
                                exhaustedRawWitness.aligned who
                                  (fun inactive => activeImage (drainedInherited inactive))]
                              exact (decodeHistory_fromMode_congr setup.program .concurrent
                                _ _ who
                                  ((PhaseRuntimeState.archivedHistory_own_congr _
                                    rebuilt.native.config.history
                                      previous.execution.application.entry.native.config.history
                                        who rebuiltUnchanged).trans
                                          ((congrArg (fun past =>
                                            (serviceGraph setup .concurrent).ownCompletions who
                                              past) recovered).trans
                                                (PhaseRuntimeState.archivedHistory_own_congr
                                                  exhaustedRawState.retired
                                                    (phase.drain physical).native.config.history
                                        previous.execution.application.entry.native.config.history
                                                          who unchanged)))).symm
                            have exhaustedImageAgrees :
                                exhaustedRawWitness.checkpoint.refs.Agrees
                                  exhaustedRawWitness.checkpoint.source.state
                                    (phase.drain physical).native.config.store := by
                              intro name cell selected
                              exact
                                (exhaustedRawWitness.checkpoint.refs.get selected).get?_preserved
                                  _ _ oldStore _
                                  (exhaustedRawWitness.checkpoint.agrees selected)
                            have exhaustedSourcePositive :
                                0 < eventCount
                                  exhaustedRawWitness.checkpoint.residual.tail := by
                              have counted :=
                                exhaustedRawWitness.checkpoint.compiled.countEq
                              have nonempty := phase.nonempty
                              have bounded := phase.bounded
                              change phase.high ≤ eventCount setup.program at bounded
                              change exhaustedRawState.attempt.phase + eventCount
                                exhaustedRawWitness.checkpoint.residual.tail =
                                  eventCount setup.program at counted
                              rw [exhaustedPhase] at counted
                              omega
                            have exhaustedHistoryPrefix :
                                List.IsPrefix
                                    previous.execution.application.entry.native.config.history
                                    (phase.drain physical).native.config.history :=
                              exhaustedRawWitness.remembered.trans
                                (phase.drain_history_prefix physical)
                            have exhaustedNextOrigins : ArchivedSourceOrigins setup .concurrent
                                (exhaustedRawState.retired ++
                                  [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                    (phase.drain physical).native⟩])
                                      ⟨_, exhaustedCheckpoint.trace⟩ := by
                              exact ArchivedSourceOrigins.append
                                exhaustedRawWitness.checkpoint
                                  exhaustedRawWitness.origins
                                    exhaustedRawWitness.aligned
                                      ⟨⟨phase.low, exhaustedRawState.generation⟩,
                                        (phase.drain physical).native⟩ (by
                                          change (⟨exhaustedRawState.attempt.phase,
                                            exhaustedRawState.generation⟩ : CommitAttemptId) =
                                              ⟨phase.low, exhaustedRawState.generation⟩
                                          exact congrArg (fun low =>
                                            (⟨low, exhaustedRawState.generation⟩ : CommitAttemptId))
                                              exhaustedPhase)
                                          exhaustedHistoryPrefix (by
                                            rw [exhaustedPhase]
                                            exact exhaustedPosition.1)
                                            exhaustedImageAgrees exhaustedSourcePositive
                                              exhaustedPath exhaustedInstructions
                                            (exhaustedRawWitness.checkpoint.chosen_commit_addresses
                                                    (phase.drain physical).native
                                                      exhaustedRawCommitting
                                                        ⟨_, exhaustedCheckpoint.trace⟩
                                                          exhaustedPath exhaustedInstructions)
                            have exhaustedPlanMember : phase ∈
                                implementation.plan.phases :=
                              exhaustedRawWitness.suffix.subset (by
                                rw [exhaustedRawInstalled]
                                exact List.mem_cons_self)
                            have exhaustedNextChronology :
                                exhaustedCheckpoint.PublicChronology
                                  implementation.plan := by
                              apply RecoverySourceCheckpoint.PublicChronology.failed_commit
                                exhaustedRawWitness.checkpoint exhaustedCheckpoint
                                  implementation.plan exhaustedRawWitness.chronology
                                    phase remaining exhaustedRawInstalled
                                      exhaustedPlanMember commitment
                                        exhaustedRawWitness.receipts.exclusion.frontier
                                          (operational.maximalPhases.suffix
                                            exhaustedRawWitness.suffix)
                                              exhaustedRawWitness.exclusions
                                                exhaustedRawWitness.failures finished
                              · rfl
                              · exact phase.drain_excluded restored
                              · simp only [survivors, ↓reduceIte, Nat.add_zero]
                              · simp only [survivors, ↓reduceIte]
                                exact exhaustedSeedPhase
                              · exact exhaustedPath
                              · exact exhaustedInstructions
                            let exhaustedSeedWitness : RecoverySourceWitness setup
                                .concurrent implementation.plan
                                  (⟨remaining, exhaustedRawState.generation, rebuilt,
                                    rebuilt, exhaustedRawState.retired ++
                                      [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                        (phase.drain physical).native⟩]⟩ :
                                          PhaseRuntimeState
                                            (serviceGraph setup .concurrent)) := {
                              checkpoint := exhaustedCheckpoint
                              aligned := exhaustedNextAligned
                              chronology := exhaustedNextChronology
                              origins := exhaustedNextOrigins
                              native := by
                                obtain ⟨nativeInputs, nativeValid⟩ := rebuiltNative
                                exact ⟨nativeInputs, nativeValid, nativeValid⟩
                              binding := ⟨rebuiltBinding, rebuiltBinding, fun _ _ => rfl⟩
                              receipts := PhaseRuntimeState.fresh_receiptRecord remaining
                                exhaustedRawState.generation rebuilt
                                  (exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩])
                                        exhaustedNextFrontier rebuiltRecord.receipts
                              stored := fun _ _ present => present
                              remembered := ⟨[], by simp⟩
                              order := PhaseRuntimeState.fresh_publicFailureOrder remaining
                                exhaustedRawState.generation rebuilt
                                  (exhaustedRawState.retired ++
                                    [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                      (phase.drain physical).native⟩])
                                        exhaustedNextFrontier rebuiltCoverage
                              suffix := (List.suffix_cons phase remaining).trans
                                (exhaustedRawInstalled ▸ exhaustedRawWitness.suffix)
                              archives := exhaustedNextArchives
                              exclusions := ⟨⟨rebuiltCoverage, rebuiltCoverage,
                                Finset.Subset.refl _⟩, rebuiltArchived, rebuiltArchived⟩
                              failures := State.PublicFailureExtension.refl _
                            }
                            let exhaustedSeedTarget : SourceProgram.Config Player L
                                exhaustedCheckpoint.residual.context :=
                              cast (congrArg (fun residual : ResidualProgram setup.program =>
                                SourceProgram.Config Player L residual.context)
                                  exhaustedSeedResidual.symm)
                                    (block.automatic exhaustedEntry)
                            have exhaustedSeedPoint : exhaustedCheckpoint.residual.lift
                                (ProtocolState.entry exhaustedCheckpoint.residual.tail
                                  exhaustedSeedTarget) = targetClosedCurrent.point := by
                              have pointAfterTransport {left right :
                                  ResidualProgram setup.program}
                                  (equal : left = right)
                                  (source : SourceProgram.Config Player L right.context) :
                                  left.lift (ProtocolState.entry left.tail
                                    (cast (congrArg (fun residual :
                                      ResidualProgram setup.program =>
                                        SourceProgram.Config Player L residual.context)
                                          equal.symm) source)) =
                                    right.lift (ProtocolState.entry right.tail source) := by
                                cases equal
                                rfl
                              have targetPoint : targetClosedCurrent.point =
                                  blockLift (block.liftPoint suffix
                                    (ProtocolState.entry suffix
                                      (block.automatic exhaustedEntry))) := by
                                rw [targetClosedCurrentEq, exhaustedTargetClose,
                                  targetRowEntryEq]
                                rfl
                              exact (pointAfterTransport exhaustedSeedResidual
                                (block.automatic exhaustedEntry)).trans targetPoint.symm
                            have exhaustedSeedRawAgrees :
                                exhaustedCheckpoint.refs.Agrees exhaustedSeedTarget.state
                                  (sourceSnapshotState setup implementation G reference lost
                                    rebuilt.native).config.store := by
                              have transportAgreement
                                  {left right : ResidualProgram setup.program}
                                  (equal : left = right)
                                  (leftRefs : ContextRefs (graphLayout setup.program)
                                    left.context)
                                  (rightRefs : ContextRefs (graphLayout setup.program)
                                    right.context)
                                  (sameRefs : cast (congrArg (fun residual :
                                    ResidualProgram setup.program =>
                                      ContextRefs (graphLayout setup.program)
                                        residual.context) equal) leftRefs = rightRefs)
                                  (rightSource : SourceProgram.Config Player L right.context)
                                  (store : Store (graphLayout setup.program)) :
                                  rightRefs.Agrees rightSource.state store →
                                    leftRefs.Agrees
                                      (cast (congrArg (fun residual :
                                        ResidualProgram setup.program =>
                                          SourceProgram.Config Player L residual.context)
                                            equal.symm) rightSource).state store := by
                                cases equal
                                cases sameRefs
                                exact id
                              intro name cell source
                              exact transportAgreement exhaustedSeedResidual
                                exhaustedCheckpoint.refs
                                  (commitBlockRefs setup.program block suffix
                                    targetEmbedding first.checkpoint.refs)
                                      exhaustedSeedRefs (block.automatic exhaustedEntry)
                                        _ exhaustedAutomaticFinalAgrees source
                            have exhaustedSeedAtPoint : targetClosedCurrent =
                                CommitRecoveryState.atPoint
                                  (exhaustedCheckpoint.residual.lift
                                    (ProtocolState.entry
                                      exhaustedCheckpoint.residual.tail
                                        exhaustedSeedTarget))
                                          rebuilt.excluded exhaustedRawState.generation := by
                              have shape : targetClosedCurrent =
                                  CommitRecoveryState.atPoint targetClosedCurrent.point
                                    targetClosedCurrent.excluded
                                      targetClosedCurrent.generation := by
                                rw [targetClosedCurrentEq, exhaustedTargetClose]
                                rfl
                              calc
                                targetClosedCurrent = CommitRecoveryState.atPoint
                                    targetClosedCurrent.point targetClosedCurrent.excluded
                                      targetClosedCurrent.generation := shape
                                _ = _ := by
                                  have maskAt : targetClosedCurrent.excluded = rebuilt.excluded :=
                                    exhaustedClosedMask.trans
                                      (phase.drain_excluded restored).symm
                                  have generationAt : targetClosedCurrent.generation =
                                      exhaustedRawState.generation := by
                                    calc
                                      _ = targetFirst.generation := by
                                        rw [targetClosedCurrentEq, exhaustedTargetClose]
                                        rfl
                                      _ = _ := targetGeneration.symm
                                  rw [exhaustedSeedPoint, maskAt, generationAt]
                            have exhaustedTargetTailGeneration :
                                targetClosedCurrent.generation =
                                  nextCurrent.generation := by
                              rw [targetClosedCurrentEq, exhaustedTargetClose,
                                ← targetGeneration, nextGeneration]
                              exact exhaustedTailGeneration.symm
                            have exhaustedSeedEndpointMask :
                                nextCurrent.excluded = rebuilt.excluded := by
                              calc
                                nextCurrent.excluded =
                                    next.execution.application.entry.excluded := nextMask
                                _ = next.execution.application.current.excluded :=
                                  exhaustedTailMask
                                _ = rebuilt.excluded := by
                                  rw [nextExhausted]
                                  exact (PhaseRuntimeState.settle_physical remaining
                                    exhaustedRawState.generation rebuilt rebuilt
                                      (exhaustedRawState.retired ++
                                        [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                          (phase.drain physical).native⟩])).1
                            have exhaustedSeedClock := setup.commitRecovery_same_generation_length
                              (setup.proposalRecoveryEraseTrace_prefix
                                targetClosedBeforeNext).reachesWithin
                                  targetClosedCurrent nextCurrent rfl nextState
                                    exhaustedTargetTailGeneration
                            have exhaustedStartClock :
                                ProtocolState.remaining setup.program nextCurrent.point +
                                    nextMapped.trace.length =
                                  ProtocolState.remaining setup.program
                                      targetClosedCurrent.point + targetClosedTrace.length := by
                              simp only [setup.proposalRecoveryEraseTrace_length]
                                at exhaustedSeedClock
                              exact exhaustedSeedClock
                            exact tailRec remaining exhaustedRawState.generation rebuilt
                              (exhaustedRawState.retired ++
                                [⟨⟨phase.low, exhaustedRawState.generation⟩,
                                  (phase.drain physical).native⟩]) exhaustedSeedWitness
                                    exhaustedSeedTarget targetClosedCurrent targetClosedTrace
                                      exhaustedSeedAtPoint targetClosedBeforeNext
                                        exhaustedSeedRawAgrees exhaustedSeedEndpointMask
                                          exhaustedStartClock nextExhausted observedCell
                        · have clean : ¬ (phase.kind = .commitment ∧
                              (((phase.drain physical).excluded \
                                previous.execution.application.entry.excluded) ∩
                                phase.owners).Nonempty) := by
                            intro failed
                            exact missing failed.2
                          have cleanExit := PhaseRuntimeState.settle_clean phase remaining
                            previous.execution.application.generation
                              previous.execution.application.entry physical
                                previous.execution.application.retired finished clean
                          have nextClean : next.execution.application =
                              PhaseRuntimeState.settle remaining
                                previous.execution.application.generation
                                  (phase.drain physical) (phase.drain physical)
                                    previous.execution.application.retired := by
                            rw [normalized]
                            simpa only [PhaseRuntimeState.normalize, installedEq] using cleanExit
                          let rawState : PhaseRuntimeState
                              (serviceGraph setup .concurrent) :=
                            { previous.execution.application with current := physical }
                          obtain ⟨rawWitness, _rawCheckpoint, _rawHistory⟩ :=
                            RecoverySourceWitness.raw_closing_checkpoint setup .concurrent
                              implementation.runtime implementation.leaks implementation.plan
                                previous next first physical effect (Ne.symm same)
                          have rawInstalled : rawState.phases = phase :: remaining := installedEq
                          have rawClean : ¬ (((phase.drain rawState.current).excluded \
                              rawState.entry.excluded) ∩ phase.owners).Nonempty := by
                            intro failure
                            exact clean ⟨commitment, failure⟩
                          have rawChanged : rawState.normalize.attempt ≠ rawState.attempt := by
                            change rawState.normalize.attempt ≠
                              previous.execution.application.attempt
                            rw [← normalized]
                            exact Ne.symm same
                          have cleanMask := clean_exit_excluded setup implementation rawState
                            rawWitness phase remaining rawInstalled rawClean rawChanged
                          have sourceCommitting : ProtocolState.atCommit
                              first.checkpoint.residual.tail
                                (ProtocolState.entry first.checkpoint.residual.tail
                                  first.checkpoint.source) = true := by
                            have committing := sourceBounds.1
                            change ProtocolState.atCommit setup.program
                              (first.checkpoint.residual.lift
                                (ProtocolState.entry first.checkpoint.residual.tail
                                  first.checkpoint.source)) = true at committing
                            rw [first.checkpoint.origin.atCommit_lift] at committing
                            exact committing
                          have rawCommitting : ProtocolState.atCommit
                              rawWitness.checkpoint.residual.tail
                                (ProtocolState.entry rawWitness.checkpoint.residual.tail
                                  rawWitness.checkpoint.source) = true := by
                            rw [_rawCheckpoint]
                            exact sourceCommitting
                          obtain ⟨seedWitness, _seedPoint, _seedReached, _seedDelta,
                            _seedNormalized⟩ :=
                            rawWitness.completed_binding_history
                              operational.maximalPhases phase remaining rawInstalled commitment
                                finished rawClean
                          let seedCheckpoint := seedWitness.checkpoint
                          have seedPhase :
                              (⟨remaining, rawState.generation, phase.drain rawState.current,
                                phase.drain rawState.current, rawState.retired⟩ :
                                  PhaseRuntimeState
                                    (serviceGraph setup .concurrent)).attempt.phase =
                                phase.high := by
                            have adjacent := rawWitness.receipts.exclusion.frontier.adjacent
                            have last := rawWitness.receipts.exclusion.frontier.last
                            rw [rawInstalled] at adjacent last
                            cases remaining with
                            | nil =>
                                have ending := last phase (by
                                  simp only [List.getLast?_singleton, Option.mem_some_iff])
                                simpa only [PhaseRuntimeState.attempt, List.head?_nil,
                                  Option.map_none, Option.getD_none, serviceGraph,
                                       Setup.eventGraph]
                                       using ending.symm
                            | cons following rest =>
                                have boundary := adjacent.rel_head? (y := following) (by simp)
                                simpa only [PhaseRuntimeState.attempt, List.head?_cons,
                                  Option.map_some, Option.getD_some] using boundary.symm
                          have phaseLow : phase.low =
                              previous.execution.application.attempt.phase := by
                            rw [PhaseRuntimeState.attempt, installedEq]
                            rfl
                          have seedResidual : seedCheckpoint.residual =
                              (⟨Δ, P, suffix, fun point =>
                                blockLift (block.liftPoint suffix point)⟩ :
                                  ResidualProgram setup.program) := by
                            apply seedCheckpoint.origin.residual_eq_of_instructionCount suffix
                              (fun point => blockLift (block.liftPoint suffix point))
                                (blockOrigin.compose (block.protocolSuffix suffix))
                            have seedCount := seedCheckpoint.compiled.countEq
                            have tailCount := tailCompiled.countEq
                            rw [seedPhase] at seedCount
                            simp only [eventCount_eq_instructionCount] at seedCount tailCount
                            change phase.high + instructionCount seedCheckpoint.residual.tail =
                              instructionCount setup.program at seedCount
                            change (previous.execution.application.attempt.phase + block.length) +
                              instructionCount suffix = instructionCount setup.program at tailCount
                            have width := geometry.1
                            have nonempty := phase.nonempty
                            omega
                          have seedRefs :
                              cast (congrArg (fun residual : ResidualProgram setup.program =>
                                ContextRefs (graphLayout setup.program) residual.context)
                                  seedResidual) seedCheckpoint.refs =
                                commitBlockRefs setup.program block suffix targetEmbedding
                                  first.checkpoint.refs := by
                            have readoutRefs {left right : ResidualProgram setup.program}
                                (equal : left = right)
                                (leftRefs : ContextRefs (graphLayout setup.program)
                                  left.context)
                                (rightRefs : ContextRefs (graphLayout setup.program)
                                  right.context)
                                (leftEmbedding : OutputEmbedding (inputLayout setup.context)
                                  (outputLayout setup.program) left.tail)
                                (rightEmbedding : OutputEmbedding (inputLayout setup.context)
                                  (outputLayout setup.program) right.tail)
                                (leftReadout : CompiledReadoutSuffix setup.program left.tail
                                  leftRefs leftEmbedding)
                                (rightReadout : CompiledReadoutSuffix setup.program right.tail
                                  rightRefs rightEmbedding) :
                                cast (congrArg (fun residual : ResidualProgram setup.program =>
                                  ContextRefs (graphLayout setup.program) residual.context)
                                    equal) leftRefs = rightRefs := by
                              cases equal
                              exact CompiledReadoutSuffix.refs_eq setup.program
                                leftReadout rightReadout
                            exact readoutRefs seedResidual seedCheckpoint.refs
                              (commitBlockRefs setup.program block suffix targetEmbedding
                                first.checkpoint.refs)
                                seedCheckpoint.embedding tailEmbedding
                                  seedCheckpoint.terminalAlignment tailReadout
                          have sourceClosedMask : lastState.excluded =
                              previous.execution.application.entry.excluded := by
                            have lower := setup.prefix_excluded
                              first.checkpoint.trace closed path.tracePrefix
                            have upper := setup.prefix_excluded closed
                              (checkpointSelection setup implementation operational
                                (earlier.extend joint legal moved)).val.checkpoint.trace
                                closedSelected
                            change previous.execution.application.entry.excluded ⊆
                              lastState.excluded at lower
                            change lastState.excluded ⊆
                              next.execution.application.entry.excluded at upper
                            rw [normalized, cleanMask.2] at upper
                            exact Finset.Subset.antisymm upper lower
                          have targetClosedMaskAtEntry : targetClosedCurrent.excluded =
                              previous.execution.application.entry.excluded :=
                            targetClosedMask.symm.trans sourceClosedMask
                          have targetFirstMaskAtEntry : targetFirst.excluded =
                              previous.execution.application.entry.excluded := by
                            rw [← targetMask]
                            rfl
                          have targetFinalExcluded : targetLast.excluded =
                              targetExcluded := by
                            simpa only [CommitRecoveryState.close_excluded,
                              CommitRecoveryState.install] using
                                congrArg CommitRecoveryState.excluded targetClosedEq
                          have targetNoFailure : targetAttempt.failedOwners = ∅ := by
                            rw [← targetAttempt.newly_excluded]
                            have finalMask : targetLast.excluded =
                                previous.execution.application.entry.excluded := by
                              rw [← targetClosedCurrentEq]
                              exact targetClosedMaskAtEntry
                            rw [← targetFinalExcluded, finalMask, targetFirstMaskAtEntry]
                            exact Finset.sdiff_self _
                          have targetFirstAtEntry : targetFirst =
                              CommitRecoveryState.atPoint
                                (blockLift (ProtocolState.entry
                                  (block.prepend suffix) targetRowEntry))
                                targetFirst.excluded targetFirst.generation := by
                            have targetRank : ProtocolState.remaining setup.program
                                targetFirst.point = ProtocolState.remaining setup.program
                                  targetFirst.saved := by
                              rw [targetFirstEq]
                              exact priorRank
                            have entryState := source_commit_entry_eq_atPoint setup
                              targetFirst targetPrior (by
                                rw [targetFirstEq]
                                exact priorCommit) targetRank
                            simpa only [targetPoint] using entryState
                          have targetBlockPositive : 0 < block.length := by
                            rw [geometry.1]
                            have nonempty := phase.nonempty
                            omega
                          have targetClosedAtSuffix : targetLast =
                              CommitRecoveryState.atPoint
                                (blockLift (block.liftPoint suffix
                                  (ProtocolState.entry suffix targetFinished)))
                                targetExcluded targetFirst.generation := by
                            calc
                              targetLast = (targetFirst.install
                                  (blockLift (block.liftPoint suffix
                                    (ProtocolState.entry suffix targetFinished)),
                                    targetExcluded) monotone).close := targetClosedEq
                              _ = CommitRecoveryState.atPoint
                                  (blockLift (block.liftPoint suffix
                                    (ProtocolState.entry suffix targetFinished)))
                                  targetExcluded targetFirst.generation := by
                                    rw [installCongr targetFirstAtEntry _ _ monotone]
                                    exact targetAttempt.close_clean_lift setup.program
                                      suffix boundary targetBlockPositive
                                        targetFirst.generation blockLift
                                          blockOrigin.remaining_lift
                                            blockOrigin.atCommit_lift
                                              blockOrigin.commitEnd_lift targetNoFailure
                          have targetTailStartsAtSuffix : targetClosedCurrent.point =
                              blockLift (block.liftPoint suffix
                                (ProtocolState.entry suffix targetFinished)) := by
                            rw [targetClosedCurrentEq, targetClosedAtSuffix]
                            rfl
                          have targetTailSavedAtSuffix : targetClosedCurrent.saved =
                              blockLift (block.liftPoint suffix
                                (ProtocolState.entry suffix targetFinished)) := by
                            rw [targetClosedCurrentEq, targetClosedAtSuffix]
                            rfl
                          have cleanWithin :
                              physical.native.config.cut.Within phase.low phase.high := by
                            have positioned := rawWitness.receipts.exclusion.frontier.positioned
                            rw [rawInstalled] at positioned
                            exact positioned.2
                          have cleanEndPrefix :
                              (phase.drain physical).native.config.cut.IsPrefix
                                phase.high :=
                            phase.finished_prefix (phase.drain physical)
                              (phase.drain_within physical cleanWithin) finished
                          have cleanTailAtStart
                              (following : RuntimePhase
                                (serviceGraph setup .concurrent))
                              (rest : List (RuntimePhase
                                (serviceGraph setup .concurrent)))
                              (head : remaining = following :: rest) :
                              (phase.drain physical).native.config.cut.IsPrefix
                                following.low := by
                            have adjacent := rawWitness.receipts.exclusion.frontier.adjacent
                            rw [rawInstalled, head] at adjacent
                            have boundary := adjacent.rel_head? (y := following) (by simp)
                            rw [← boundary]
                            exact cleanEndPrefix
                          have seedFrontier := seedWitness.receipts.exclusion.frontier
                          have seedNative := seedWitness.native.choose_spec.active
                          have seedBinding := seedWitness.binding.active
                          have seedReceipts := seedWitness.receipts
                          have seedOrder := seedWitness.order
                          have cleanPhaseAgreement :
                              (commitBlockRefs setup.program block suffix targetEmbedding
                                first.checkpoint.refs).Agrees targetFinished.state
                                (sourceSnapshotState setup implementation G reference lost
                                  (phase.drain physical).native).config.store :=
                            visit.finalAgrees
                          have cleanFinalAtSaved :
                              (commitBlockRefs setup.program block suffix targetEmbedding
                                first.checkpoint.refs).Agrees targetFinished.state
                                  (sourceSnapshotState setup implementation G reference lost
                                    next.execution.application.entry.native).config.store := by
                            rw [nextClean]
                            exact sourceReplaySettleAssignedSavedAgreement setup implementation
                              (commitBlockRefs setup.program block suffix targetEmbedding
                                first.checkpoint.refs) targetFinished G reference
                                  lost remaining previous.execution.application.generation
                                    (phase.drain physical)
                                      previous.execution.application.retired
                                        cleanPhaseAgreement
                          let seedTarget : SourceProgram.Config Player L
                              seedCheckpoint.residual.context :=
                            cast (congrArg (fun residual : ResidualProgram setup.program =>
                              SourceProgram.Config Player L residual.context)
                                seedResidual.symm) targetFinished
                          have seedTargetPoint :
                              seedCheckpoint.residual.lift
                                (ProtocolState.entry seedCheckpoint.residual.tail seedTarget) =
                                  targetClosedCurrent.point := by
                            have pointAfterTransport {left right :
                                ResidualProgram setup.program}
                                (equal : left = right)
                                (source : SourceProgram.Config Player L right.context) :
                                left.lift (ProtocolState.entry left.tail
                                  (cast (congrArg (fun residual :
                                    ResidualProgram setup.program =>
                                      SourceProgram.Config Player L residual.context)
                                        equal.symm) source)) =
                                  right.lift (ProtocolState.entry right.tail source) := by
                              cases equal
                              rfl
                            exact (pointAfterTransport seedResidual targetFinished).trans
                              targetTailStartsAtSuffix.symm
                          have seedTargetSaved : targetClosedCurrent.saved =
                              seedCheckpoint.residual.lift
                                (ProtocolState.entry seedCheckpoint.residual.tail
                                  seedTarget) := by
                            calc
                              targetClosedCurrent.saved = targetClosedCurrent.point := by
                                rw [targetClosedCurrentEq, targetClosedAtSuffix]
                                rfl
                              _ = seedCheckpoint.residual.lift
                                  (ProtocolState.entry seedCheckpoint.residual.tail
                                    seedTarget) := seedTargetPoint.symm
                          have seedTargetRemaining : ProtocolState.remaining setup.program
                              (seedCheckpoint.residual.lift
                                (ProtocolState.entry seedCheckpoint.residual.tail
                                  seedTarget)) = instructionCount suffix := by
                            rw [seedTargetPoint, targetTailStartsAtSuffix,
                              blockOrigin.remaining_lift,
                              block.liftPoint_remaining,
                              ProtocolState.remaining_entry]
                          have seedTargetMask : targetClosedCurrent.excluded =
                              (phase.drain rawState.current).excluded :=
                            targetClosedMaskAtEntry.trans cleanMask.1.symm
                          have seedTargetGeneration :
                              targetClosedCurrent.generation = rawState.generation := by
                            rw [targetClosedCurrentEq, targetClosedAtSuffix,
                              ← targetGeneration]
                            rfl
                          have seedTargetRawAgrees : seedCheckpoint.refs.Agrees
                              seedTarget.state
                                (sourceSnapshotState setup implementation G reference lost
                                  (phase.drain physical).native).config.store := by
                            have transportAgreement
                                {left right : ResidualProgram setup.program}
                                (equal : left = right)
                                (leftRefs : ContextRefs (graphLayout setup.program)
                                  left.context)
                                (rightRefs : ContextRefs (graphLayout setup.program)
                                  right.context)
                                (sameRefs : cast (congrArg (fun residual :
                                  ResidualProgram setup.program =>
                                    ContextRefs (graphLayout setup.program)
                                      residual.context) equal) leftRefs = rightRefs)
                                (rightSource : SourceProgram.Config Player L right.context)
                                (store : Store (graphLayout setup.program)) :
                                rightRefs.Agrees rightSource.state store →
                                  leftRefs.Agrees
                                    (cast (congrArg (fun residual :
                                      ResidualProgram setup.program =>
                                        SourceProgram.Config Player L residual.context)
                                          equal.symm) rightSource).state store := by
                              cases equal
                              cases sameRefs
                              exact id
                            intro name cell member
                            exact transportAgreement seedResidual seedCheckpoint.refs
                              (commitBlockRefs setup.program block suffix targetEmbedding
                                first.checkpoint.refs) seedRefs targetFinished _
                                  (fun {name cell} source => cleanPhaseAgreement source) member
                          have seedTargetAgrees : seedCheckpoint.refs.Agrees
                              seedTarget.state
                                (sourceSnapshotState setup implementation G reference lost
                                  next.execution.application.entry.native).config.store := by
                            rw [nextClean]
                            exact sourceReplaySettleAssignedSavedAgreement setup implementation
                              seedCheckpoint.refs seedTarget G reference lost remaining
                                previous.execution.application.generation
                                  (phase.drain physical)
                                    previous.execution.application.retired
                                      seedTargetRawAgrees
                          have cleanTailMask :
                              next.execution.application.entry.excluded =
                                next.execution.application.current.excluded := by
                            rw [nextClean]
                            exact PhaseRuntimeState.settle_entry_excluded_of_same remaining
                              previous.execution.application.generation
                                (phase.drain physical) (phase.drain physical)
                                  previous.execution.application.retired rfl
                          have cleanTailGeneration :
                              next.execution.application.generation =
                                previous.execution.application.generation := by
                            rw [nextClean]
                            exact (PhaseRuntimeState.settle_generation_archive_of_same_excluded
                              remaining previous.execution.application.generation
                                (phase.drain physical) (phase.drain physical)
                                  previous.execution.application.retired rfl).1
                          have targetTailGeneration :
                              targetClosedCurrent.generation =
                                nextCurrent.generation := by
                            rw [targetClosedCurrentEq, targetClosedAtSuffix,
                              ← targetGeneration, nextGeneration]
                            exact cleanTailGeneration.symm
                          have targetTailMask : targetClosedCurrent.excluded =
                              nextCurrent.excluded := by
                            have nativeMask : next.execution.application.entry.excluded =
                                previous.execution.application.entry.excluded := by
                              rw [normalized]
                              exact cleanMask.2
                            rw [targetClosedMaskAtEntry, nextMask]
                            exact nativeMask.symm
                          have seedAtPoint : targetClosedCurrent =
                               CommitRecoveryState.atPoint
                                 (seedCheckpoint.residual.lift
                                   (ProtocolState.entry seedCheckpoint.residual.tail
                                     seedTarget))
                                   (phase.drain physical).excluded
                                     rawState.generation := by
                             have shape : targetClosedCurrent =
                                 CommitRecoveryState.atPoint targetClosedCurrent.point
                                   targetClosedCurrent.excluded
                                     targetClosedCurrent.generation := by
                               rw [targetClosedCurrentEq, targetClosedAtSuffix]
                               rfl
                             calc
                               targetClosedCurrent = CommitRecoveryState.atPoint
                                   targetClosedCurrent.point targetClosedCurrent.excluded
                                     targetClosedCurrent.generation := shape
                               _ = _ := by
                                 rw [seedTargetPoint, seedTargetMask,
                                   seedTargetGeneration]
                          have seedEndpointMask : nextCurrent.excluded =
                               (phase.drain physical).excluded :=
                             targetTailMask.symm.trans seedTargetMask
                          have seedClock := setup.commitRecovery_same_generation_length
                             (setup.proposalRecoveryEraseTrace_prefix
                               targetClosedBeforeNext).reachesWithin
                                 targetClosedCurrent nextCurrent rfl nextState
                                   targetTailGeneration
                          have startClock :
                               ProtocolState.remaining setup.program nextCurrent.point +
                                   nextMapped.trace.length =
                                 ProtocolState.remaining setup.program
                                     targetClosedCurrent.point +
                                   targetClosedTrace.length := by
                             simp only [setup.proposalRecoveryEraseTrace_length] at seedClock
                             exact seedClock
                          exact tailRec remaining rawState.generation
                             (phase.drain rawState.current) rawState.retired seedWitness
                               seedTarget targetClosedCurrent targetClosedTrace seedAtPoint
                                 targetClosedBeforeNext seedTargetRawAgrees seedEndpointMask
                                  startClock nextClean observedCell
                  · cases kind : phase.kind with
                    | commitment => exact (commitment kind).elim
                    | reveal =>
                         let rawState : PhaseRuntimeState
                             (serviceGraph setup .concurrent) :=
                           { previous.execution.application with current := physical }
                         obtain ⟨rawWitness, rawCheckpoint, rawHistory⟩ :=
                           RecoverySourceWitness.raw_closing_checkpoint setup .concurrent
                             implementation.runtime implementation.leaks
                               implementation.plan previous next first physical effect
                                 (Ne.symm same)
                         have rawInstalled : rawState.phases = phase :: remaining :=
                           installedEq
                         have rawMember : phase ∈ rawState.phases.head? := by
                           rw [rawInstalled]
                           exact Option.mem_some_iff.mpr rfl
                         have graphOrder :=
                           (toEventGraph setup.program).withMode_revealRelaxedOrdered
                             (toEventGraph_barrierOrdered setup.program) (.concurrent)
                         have drainedNative : ∃ inputs,
                             (phase.drain physical).native.Invariant inputs :=
                           ⟨rawWitness.native.choose,
                             phase.drain_invariant physical
                               rawWitness.native.choose_spec.active⟩
                         have drainedOrder :=
                           phase.orderedPublicFailures_drain phase.low
                             rawState.entry.excluded physical
                               (rawWitness.order.publicationOrder phase rawMember)
                                 rawWitness.order.coverage.active
                                   rawWitness.order.coverage.inherited graphOrder
                         obtain ⟨revealCheckpoint, revealPath, revealSteps,
                           revealAddresses, revealWord, _revealIntended,
                           revealReplay⟩ :=
                           rawWitness.checkpoint.after_reveal phase remaining
                             rawInstalled kind rawWitness.receipts.exclusion
                               rawWitness.stored rawWitness.remembered
                                 drainedNative.choose_spec.reachable drainedOrder
                                   finished
                         obtain ⟨_revealFuel, retainedRevealPath⟩ := revealPath
                         have rawPlanMember : phase ∈ implementation.plan.phases :=
                           rawWitness.suffix.subset (by
                             rw [rawInstalled]
                             exact List.mem_cons_self)
                         obtain ⟨revealAligned, revealChronology, revealOrigins,
                           _revealDelta⟩ :=
                           rawWitness.checkpoint.public_phase_archive
                             implementation.plan operational.maximalPhases
                               phase remaining rawInstalled rawPlanMember
                                 (by simp only [kind]; decide)
                                   rawWitness.aligned rawWitness.chronology
                                     rawWitness.origins rawWitness.exclusions
                                       rawWitness.failures rawWitness.archives
                                         rawWitness.receipts rawWitness.stored
                                           rawWitness.remembered rawWitness.order
                                             drainedNative finished revealCheckpoint
                                               retainedRevealPath revealSteps
                                                 revealAddresses revealWord revealReplay
                         let revealWitness :=
                           rawWitness.completed_phase_checkpoint phase remaining
                             rawInstalled finished revealCheckpoint revealAligned
                               revealChronology revealOrigins
                         have noRetry : ¬ (phase.kind = .commitment ∧
                             (((phase.drain physical).excluded \
                               previous.execution.application.entry.excluded) ∩
                                 phase.owners).Nonempty) := by
                           rintro ⟨impossible, _⟩
                           cases kind.symm.trans impossible
                         have nextSettle : next.execution.application =
                             PhaseRuntimeState.settle remaining
                               previous.execution.application.generation
                                 (phase.drain physical) (phase.drain physical)
                                   previous.execution.application.retired := by
                           rw [normalized]
                           simp only [PhaseRuntimeState.normalize, installedEq]
                           exact PhaseRuntimeState.settle_clean phase remaining
                             previous.execution.application.generation
                               previous.execution.application.entry physical
                                 previous.execution.application.retired finished noRetry
                         let count := phase.high - phase.low
                         have low : phase.low =
                             previous.execution.application.attempt.phase := by
                           simp only [PhaseRuntimeState.attempt, installedEq, List.head?_cons,
                             Option.map_some, Option.getD_some]
                         have high : phase.high =
                             previous.execution.application.attempt.phase + count := by
                           dsimp only [count]
                           have nonempty := phase.nonempty
                           omega
                         have prefixed := first.checkpoint.compiled.revealPrefix_of_phase
                           setup.program (.concurrent) first.checkpoint.residual.tail
                             first.checkpoint.refs first.checkpoint.source.revelations
                               first.checkpoint.registry first.checkpoint.embedding
                                 first.checkpoint.before
                                   previous.execution.application.attempt.phase phase kind
                                     low count high
                         have headNotCommit : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
                             (program : SourceProgram Player L Γ O) (width : Nat),
                             0 < width → RevealPrefix program width →
                             ∀ source, ProtocolState.atCommit program
                               (ProtocolState.entry program source) = false := by
                           intro Γ O program width positive revealPrefix source
                           cases width with
                           | zero => omega
                           | succ width =>
                               cases program with
                               | ret _ => exact revealPrefix.elim
                               | sample _ _ _ _ => exact revealPrefix.elim
                               | commit _ _ _ _ _ => exact revealPrefix.elim
                               | reveal _ _ _ _ _ _ _ => rfl
                         have priorNotCommit : ProtocolState.atCommit setup.program
                             priorCurrent.point = false := by
                           rw [priorPoint, first.checkpoint.atCommit]
                           exact headNotCommit _ count (by
                             dsimp only [count]
                             have nonempty := phase.nonempty
                             omega) prefixed priorLive
                         have priorFrontier : priorCurrent.BlockFrontier :=
                           setup.commitRecovery_blockFrontier
                             (setup.proposalRecoveryEraseTrace priorActual)
                         have savedAtLive : priorCurrent.saved = priorCurrent.point :=
                           priorFrontier.saved_eq_point_of_not_atCommit priorNotCommit
                         have liveConfig : priorLive = priorSaved := by
                           apply ProtocolState.entry_injective first.checkpoint.residual.tail
                           apply sourceReplaySuffixInjective setup first.checkpoint.origin
                           exact priorPoint.symm.trans (savedAtLive.symm.trans priorSavedPoint)
                         have priorInformation : setup.proposalRecoveryModel.infoOf who
                             sourceStart.trace =
                               setup.proposalRecoveryModel.infoOf who priorActual :=
                           _priorInfo.symm.trans (congrArg
                             (fun history : setup.proposalRecoveryProtocol.History =>
                               setup.proposalRecoveryModel.infoOf who history.trace)
                                 priorActualEq).symm
                         have entryMask : priorCurrent.entryExcluded =
                             priorCurrent.excluded := by
                           have metadata := source_information_metadata setup who
                             sourceStart ⟨some priorCurrent, priorActual⟩ priorInformation
                           exact metadata.2.2.2.1.symm.trans metadata.2.2.1
                         have initialAtPoint : priorCurrent = CommitRecoveryState.atPoint
                             (first.checkpoint.residual.lift
                               (ProtocolState.entry first.checkpoint.residual.tail priorLive))
                               priorCurrent.excluded priorCurrent.generation := by
                           rw [← priorPoint]
                           cases priorCurrent with
                           | mk point saved excluded entryExcluded generation entered =>
                               dsimp only at savedAtLive entryMask ⊢
                               subst saved
                               subst entryExcluded
                               rfl
                         have nextGenerationEq : next.execution.application.generation =
                             previous.execution.application.generation := by
                           rw [nextSettle]
                           exact (PhaseRuntimeState.settle_generation_archive_of_same_excluded
                             remaining
                               previous.execution.application.generation (phase.drain physical)
                                 (phase.drain physical)
                                   previous.execution.application.retired rfl).1
                         have clock := setup.commitRecovery_same_generation_length
                           (setup.proposalRecoveryEraseTrace_prefix actualPriorToNext).reachesWithin
                             priorCurrent nextCurrent rfl nextState
                               (priorGeneration.trans
                                 (nextGeneration.trans nextGenerationEq).symm)
                         simp only [setup.proposalRecoveryEraseTrace_length] at clock
                         have frontier := rawWitness.receipts.exclusion.frontier
                         have adjacent := frontier.adjacent
                         have last := frontier.last
                         rw [rawInstalled] at adjacent last
                         have nextLow : PhaseRuntimeState.phaseLow remaining = phase.high := by
                           cases remaining with
                           | nil =>
                               have boundary := last phase (by simp)
                               simpa only [PhaseRuntimeState.phaseLow, List.head?_nil,
                                 Option.map_none, Option.getD_none, serviceGraph,
                                       Setup.eventGraph]
                                 using boundary.symm
                           | cons following rest =>
                               have boundary := adjacent.rel_head? (y := following) (by simp)
                               simpa only [PhaseRuntimeState.phaseLow, List.head?_cons,
                                 Option.map_some, Option.getD_some] using boundary.symm
                         have laterRank : phase.high ≤ next.execution.application.attempt.phase :=
                           by
                             rw [nextSettle, ← nextLow]
                             exact (PhaseRuntimeState.settle_namespace remaining
                               previous.execution.application.generation (phase.drain physical)
                                 (phase.drain physical) previous.execution.application.retired
                                   adjacent.tail).2
                         have bound : priorMapped.trace.length + count ≤
                             nextMapped.trace.length := by
                           have firstCount := first.checkpoint.compiled.countEq
                           have finalCount := chosen.compiled.countEq
                           simp only [eventCount_eq_instructionCount] at firstCount finalCount
                           have firstRemaining : ProtocolState.remaining setup.program
                               priorCurrent.point =
                                 instructionCount first.checkpoint.residual.tail := by
                             rw [priorPoint, first.checkpoint.remaining,
                               ProtocolState.remaining_entry]
                           have finalRemaining : ProtocolState.remaining setup.program
                               nextCurrent.point = instructionCount chosen.residual.tail := by
                             rw [nextPoint, chosen.remaining, ProtocolState.remaining_entry]
                           omega
                         obtain ⟨phaseState, phaseTrace, phaseKept, phaseDepth⟩ :=
                           setup.proposalRecovery_prefix_at_depth nextMapped.trace
                             (priorMapped.trace.length + count) bound
                         have priorToPhase : TracePrefix priorActual phaseTrace := by
                           apply commonPrefixOrder ⟨some priorCurrent, priorActual⟩
                             ⟨phaseState, phaseTrace⟩ nextMapped actualPriorToNext phaseKept
                           rw [priorActualLength, phaseDepth]
                           omega
                         obtain ⟨phaseLast, phaseJoints, phaseAddresses, phaseStateEq,
                           phasePath, phaseLength, _phaseWord, _phaseSignals⟩ :=
                           source_instruction_window setup
                             (setup.initialConfig setup.initialLaw.support_nonempty.choose)
                               priorCurrent (setup.proposalRecoveryEraseTrace priorActual)
                                 (setup.proposalRecoveryEraseTrace phaseTrace)
                                   (setup.proposalRecoveryEraseTrace_prefix priorToPhase)
                         cases phaseStateEq
                         have phaseRows : phaseJoints.length = count := by
                           simp only [setup.proposalRecoveryEraseTrace_length] at phaseLength
                           omega
                         obtain ⟨revealedTarget, revealedAtPoint, inheritedPrivate⟩ :=
                           sourceReplay_reveal_prefix_state setup count
                             first.checkpoint.residual.tail prefixed first.checkpoint.refs
                               first.checkpoint.embedding first.checkpoint.residual.lift
                                 first.checkpoint.origin priorLive priorCurrent.excluded
                                   priorCurrent.generation phaseLast phaseJoints phaseAddresses
                                     (by rw [initialAtPoint] at phasePath; exact phasePath)
                                       phaseRows
                         let tail := Vegas.revealTail count first.checkpoint.residual.tail
                           prefixed
                         let tailRefs := revealTailRefs setup count
                           first.checkpoint.residual.tail prefixed first.checkpoint.refs
                             first.checkpoint.embedding
                         let tailEmbedding := revealTailEmbedding setup count
                           first.checkpoint.residual.tail prefixed first.checkpoint.embedding
                         let residual : ResidualProgram setup.program :=
                           ⟨tail.context, tail.names, tail.tail,
                             fun point => first.checkpoint.residual.lift (tail.lift point)⟩
                         have tailOrigin : ProtocolSuffix setup.program tail.tail residual.lift :=
                           first.checkpoint.origin.compose
                             (revealTail_protocolSuffix count first.checkpoint.residual.tail
                               prefixed)
                         have tailCompiled := first.checkpoint.compiled.revealTailMany setup
                           count first.checkpoint.residual.tail prefixed first.checkpoint.refs
                             first.checkpoint.source.revelations first.checkpoint.registry
                               first.checkpoint.embedding first.checkpoint.before
                                 previous.execution.application.attempt.phase
                         have tailAligned := first.checkpoint.terminalAlignment.revealTailMany
                           setup count first.checkpoint.residual.tail prefixed first.checkpoint.refs
                             first.checkpoint.embedding
                         have residualEq : revealWitness.checkpoint.residual = residual := by
                           apply revealWitness.checkpoint.origin.residual_eq_of_instructionCount
                             tail.tail residual.lift tailOrigin
                           have seedCount := revealWitness.checkpoint.compiled.countEq
                           have remainingCount := tailCompiled.countEq
                           change PhaseRuntimeState.phaseLow remaining +
                             eventCount revealWitness.checkpoint.residual.tail =
                               eventCount setup.program at seedCount
                           rw [nextLow] at seedCount
                           simp only [eventCount_eq_instructionCount] at seedCount remainingCount
                           change (previous.execution.application.attempt.phase + count) +
                             instructionCount tail.tail = instructionCount setup.program
                               at remainingCount
                           omega
                         let rawEndpoint : CommitRecoveryState setup.program :=
                           CommitRecoveryState.atPoint (revealWitness.checkpoint.residual.lift
                             (ProtocolState.entry revealWitness.checkpoint.residual.tail
                               revealWitness.checkpoint.source))
                             (phase.drain physical).excluded
                               previous.execution.application.generation
                         obtain ⟨rawSource, rawPoint, rawAgrees⟩ :=
                           transportPublicEndpoint residualEq.symm tailRefs
                             revealWitness.checkpoint.refs tailEmbedding
                               revealWitness.checkpoint.embedding tailAligned
                                 revealWitness.checkpoint.terminalAlignment
                                   revealWitness.checkpoint.source rawEndpoint
                                     (phase.drain physical).excluded
                                       previous.execution.application.generation rfl
                                         (phase.drain physical).native.config.store
                                           revealWitness.checkpoint.agrees
                         have unique : (tail.context.map Prod.fst).Nodup := by
                           have unique := revealWitness.checkpoint.unique
                           rw [residualEq] at unique
                           exact unique
                         have phaseActualKept : TracePrefix phaseTrace nextActual := by
                           have kept := phaseKept
                           rw [← nextActualEq] at kept
                           exact kept
                         have publicReads {name : VarId} {kind : CellTy Player L}
                             (member : HasVar tail.context name kind)
                             (visible : (cellField kind).IsPublic) :
                             (tailRefs.get member).get? (phase.drain physical).native.config.store =
                               some (cellValue (revealedTarget.state.get member)) := by
                           have actual := sourceReplay_public_prefix_read setup chosen who
                             labels nextCurrent nextActual nextActualInfo tail.tail residual.lift
                               tailOrigin unique tailRefs tailEmbedding tailAligned phaseLast
                                 (setup.proposalRecoveryEraseTrace phaseTrace)
                                   (ProtocolState.entry tail.tail revealedTarget)
                                   (ProtocolState.entry tail.tail revealedTarget)
                                   (by rw [revealedAtPoint]; rfl)
                                   (by rw [revealedAtPoint]; rfl) rfl
                                   (setup.proposalRecoveryEraseTrace_prefix phaseActualKept)
                                     member visible
                           have preserved := (tailRefs.get member).get?_preserved
                             (phase.drain physical).native.config.store
                               next.execution.application.entry.native.config.store
                                 (by
                                   rw [nextSettle]
                                   exact sourceReplaySettleSavedStore setup
                                     remaining previous.execution.application.generation
                                       (phase.drain physical)
                                         previous.execution.application.retired)
                                 (cellValue (rawSource.state.get member)) (rawAgrees member)
                           simp only [ProtocolState.base_entry] at actual
                           have values := Option.some.inj (preserved.symm.trans actual)
                           exact (rawAgrees member).trans (congrArg some values)
                         have targetAgrees : tailRefs.Agrees revealedTarget.state
                             (sourceSnapshotState setup implementation G reference lost
                               (phase.drain physical).native).config.store := by
                           intro name kind member
                           by_cases visible : (cellField kind).IsPublic
                           · have fieldPublic : (serviceGraph setup .concurrent).fieldPublic
                                 (tailRefs.get member).field := by
                               change (graphLayout setup.program
                                 (tailRefs.get member).field).IsPublic
                               rw [(tailRefs.get member).layout_eq]
                               exact visible
                             have storeEq :
                                 (sourceSnapshotState setup implementation G reference lost
                                   (phase.drain physical).native).config.store
                                     (tailRefs.get member).field =
                                 (phase.drain physical).native.config.store
                                   (tailRefs.get member).field := by
                               simp only [sourceSnapshotState, State.swap_config, Config.swap_store]
                               exact ValueSwap.store_public _ _ _ fieldPublic
                             exact ((tailRefs.get member).get?_congr _ _ storeEq).trans
                               (publicReads member visible)
                           · obtain ⟨original, referenceEq, valueEq⟩ :=
                               inheritedPrivate member visible
                             rw [referenceEq, valueEq, liveConfig]
                             exact oldEntryAgrees original
                         have publicValues {name : VarId} {kind : CellTy Player L}
                             (member : HasVar tail.context name kind)
                             (visible : (cellField kind).IsPublic) :
                             rawSource.state.get member = revealedTarget.state.get member := by
                           have values := Option.some.inj
                             ((rawAgrees member).symm.trans (publicReads member visible))
                           cases kind with
                           | publicData payload => exact values
                           | publication payload => exact values
                           | privateInput owner payload => exact visible.elim
                           | commitment owner payload => exact visible.elim
                         have lookup (name : VarId) (kind : CellTy Player L) :
                             ∀ (Γ : SourceCtx Player L) (left right : State L Γ),
                             (∀ member : HasVar Γ name kind,
                               left.get member = right.get member) →
                             State.cell? left name kind = State.cell? right name kind := by
                           intro Γ
                           induction Γ with
                           | nil => intro left right equal; rfl
                           | cons head Γ ih =>
                               rcases head with ⟨headName, headKind⟩
                               intro left right equal
                               rw [State.cell?.eq_2, State.cell?.eq_2]
                               split_ifs with same
                               · rcases same with ⟨rfl, rfl⟩
                                 exact congrArg some (equal .here)
                               · exact ih _ _ (fun member => equal (.there member))
                         have publicLookup (name : VarId) (kind : CellTy Player L)
                             (visible : (cellField kind).IsPublic) :
                             ProtocolState.cell? setup.program rawEndpoint.point name kind =
                               ProtocolState.cell? setup.program phaseLast.point name kind := by
                           rw [rawPoint, revealedAtPoint]
                           dsimp only [CommitRecoveryState.atPoint]
                           rw [tailOrigin.cell?_lift, tailOrigin.cell?_lift,
                             ProtocolState.cell?_entry, ProtocolState.cell?_entry]
                           exact lookup name kind tail.context _ _
                             (fun member => publicValues member visible)
                         have rawKept : TracePrefix first.checkpoint.trace
                             revealWitness.checkpoint.trace := by
                           have kept := retainedRevealPath
                           rw [rawHistory] at kept
                           simpa only [revealWitness,
                             RecoverySourceWitness.completed_phase_checkpoint]
                             using kept.tracePrefix
                         have rawClock := setup.commitRecovery_same_generation_length
                           rawKept.reachesWithin originalStart rawEndpoint rfl rfl rfl
                         have rawRemaining : ProtocolState.remaining setup.program
                             rawEndpoint.point = instructionCount tail.tail := by
                           rw [rawPoint]
                           change ProtocolState.remaining setup.program
                             (residual.lift (ProtocolState.entry residual.tail rawSource)) = _
                           rw [tailOrigin.remaining_lift, ProtocolState.remaining_entry]
                         have rawLength : revealWitness.checkpoint.trace.length =
                             first.checkpoint.trace.length + count := by
                           have width := eventCount_revealTail count
                             first.checkpoint.residual.tail prefixed
                           change ProtocolState.remaining setup.program rawEndpoint.point +
                             revealWitness.checkpoint.trace.length =
                               ProtocolState.remaining setup.program originalStart.point +
                                 first.checkpoint.trace.length at rawClock
                           rw [rawRemaining] at rawClock
                           simp only [originalStart, CommitRecoveryState.atPoint,
                             first.checkpoint.remaining, ProtocolState.remaining_entry]
                               at rawClock
                           simp only [eventCount_eq_instructionCount] at width
                           change count + instructionCount tail.tail =
                             instructionCount first.checkpoint.residual.tail at width
                           omega
                         have targetInitial : priorCurrent = CommitRecoveryState.atPoint
                             (first.checkpoint.residual.lift
                               (ProtocolState.entry first.checkpoint.residual.tail priorLive))
                               previous.execution.application.entry.excluded
                                 priorCurrent.generation := by
                           simpa only [priorMask] using initialAtPoint
                         have phaseMask : phaseLast.excluded =
                             (phase.drain physical).excluded := by
                           have mask := revealMasksEqual count first.checkpoint.residual.tail
                             prefixed first.checkpoint.residual.lift first.checkpoint.origin
                               first.checkpoint.unique first.checkpoint.source priorLive
                                 previous.execution.application.entry.excluded
                                   previous.execution.application.generation
                                     priorCurrent.generation priorCurrent targetInitial
                                       first.checkpoint.trace
                                         (setup.proposalRecoveryEraseTrace priorActual)
                                           rawEndpoint phaseLast revealWitness.checkpoint.trace
                                             (setup.proposalRecoveryEraseTrace phaseTrace)
                                               rawKept
                                                 (setup.proposalRecoveryEraseTrace_prefix
                                                   priorToPhase) rawLength
                                                 (by
                                                   simp only
                                                     [setup.proposalRecoveryEraseTrace_length]
                                                   omega) publicLookup
                           exact mask.symm
                         have seedPoint : phaseLast = CommitRecoveryState.atPoint
                             (residual.lift (ProtocolState.entry tail.tail revealedTarget))
                               (phase.drain physical).excluded
                                 previous.execution.application.generation := by
                           simpa only [phaseMask, priorGeneration] using revealedAtPoint
                         obtain ⟨seedTarget, seedAtPoint, seedAgrees⟩ :=
                           transportPublicEndpoint residualEq revealWitness.checkpoint.refs
                             tailRefs revealWitness.checkpoint.embedding tailEmbedding
                               revealWitness.checkpoint.terminalAlignment tailAligned
                                 revealedTarget phaseLast (phase.drain physical).excluded
                                   previous.execution.application.generation seedPoint _
                                     targetAgrees
                         have nativeEntryMask : next.execution.application.entry.excluded =
                             (phase.drain physical).excluded := by
                           rw [nextSettle]
                           exact (PhaseRuntimeState.settle_entry_excluded_of_same remaining
                             previous.execution.application.generation (phase.drain physical)
                               (phase.drain physical)
                                 previous.execution.application.retired rfl).trans
                             (PhaseRuntimeState.settle_physical remaining
                               previous.execution.application.generation (phase.drain physical)
                                 (phase.drain physical)
                                   previous.execution.application.retired).1
                         have seedClock := setup.commitRecovery_same_generation_length
                           (setup.proposalRecoveryEraseTrace_prefix phaseKept).reachesWithin
                             phaseLast nextCurrent rfl nextState (by
                               rw [seedAtPoint]
                               exact (nextGeneration.trans nextGenerationEq).symm)
                         simp only [setup.proposalRecoveryEraseTrace_length] at seedClock
                         exact tailRec remaining previous.execution.application.generation
                           (phase.drain physical) previous.execution.application.retired
                             revealWitness seedTarget phaseLast phaseTrace seedAtPoint phaseKept
                                seedAgrees (nextMask.trans nativeEntryMask) seedClock nextSettle
                                  observedCell
                    | sample =>
                         let rawState : PhaseRuntimeState
                             (serviceGraph setup .concurrent) :=
                           { previous.execution.application with current := physical }
                         obtain ⟨rawWitness, rawCheckpoint, rawHistory⟩ :=
                           RecoverySourceWitness.raw_closing_checkpoint setup .concurrent
                             implementation.runtime implementation.leaks
                               implementation.plan previous next first physical effect
                                 (Ne.symm same)
                         have rawInstalled : rawState.phases = phase :: remaining :=
                           installedEq
                         obtain ⟨sampleWitness, samplePath, sampleSteps,
                           sampleAddresses, sampleWord, sampleIntended, sampleReplay,
                           sampleMask, sampleDelta, sampleObserved⟩ :=
                           rawWitness.completed_sample_history
                             operational.maximalPhases phase remaining rawInstalled kind
                               finished
                         have noRetry : ¬ (phase.kind = .commitment ∧
                             (((phase.drain physical).excluded \
                               previous.execution.application.entry.excluded) ∩
                                 phase.owners).Nonempty) := by
                           rintro ⟨impossible, _⟩
                           cases kind.symm.trans impossible
                         have nextSettle : next.execution.application =
                             PhaseRuntimeState.settle remaining
                               previous.execution.application.generation
                                 (phase.drain physical) (phase.drain physical)
                                   previous.execution.application.retired := by
                           rw [normalized]
                           simp only [PhaseRuntimeState.normalize, installedEq]
                           exact PhaseRuntimeState.settle_clean phase remaining
                             previous.execution.application.generation
                               previous.execution.application.entry physical
                                 previous.execution.application.retired finished noRetry
                         have nextEntryMask : next.execution.application.entry.excluded =
                             (phase.drain physical).excluded := by
                           rw [nextSettle]
                           exact (PhaseRuntimeState.settle_entry_excluded_of_same remaining
                             previous.execution.application.generation (phase.drain physical)
                               (phase.drain physical)
                                 previous.execution.application.retired rfl).trans
                             (PhaseRuntimeState.settle_physical remaining
                               previous.execution.application.generation (phase.drain physical)
                                 (phase.drain physical)
                                   previous.execution.application.retired).1
                         have equalMasks : nextCurrent.excluded = priorCurrent.excluded := by
                           calc
                             nextCurrent.excluded = next.execution.application.entry.excluded :=
                               nextMask
                             _ = (phase.drain physical).excluded := nextEntryMask
                             _ = previous.execution.application.entry.excluded := sampleMask
                             _ = priorCurrent.excluded := priorMask.symm
                         have unpackSample {Γ : SourceCtx Player L} {O : Finset VarId}
                             (program : SourceProgram Player L Γ O)
                             (source : SourceProgram.Config Player L Γ)
                             (lift : ProtocolState program → ProtocolState setup.program)
                             (observed : (let read : ∀ {Ξ : SourceCtx Player L}
                                 {Q : Finset VarId} (program : SourceProgram Player L Ξ Q),
                                 SourceProgram.Config Player L Ξ →
                                   (ProtocolState program → ProtocolState setup.program) → Prop :=
                               fun {_Ξ} {_Q} program => match program with
                             | .sample (payload := ty) name _fresh law suffix => fun source lift =>
                                 ∃ (event : (serviceGraph setup .concurrent).EventId)
                                   (output : (serviceGraph setup .concurrent).outputLayout
                                     event = .publicData ty) (sampled : L.Val ty),
                                   sampled ∈ (L.evalDist law
                                   (sourcePublicEnv source.state)).support ∧
                                   event.val = rawState.attempt.phase ∧
                                   (⟨.inr event, output⟩ : FieldRef (graphLayout setup.program)
                                     (.publicData ty)).get?
                                     (phase.drain physical).native.config.store =
                                       some sampled ∧
                                   sampleWitness.checkpoint.residual.lift
                                   (ProtocolState.entry sampleWitness.checkpoint.residual.tail
                                     sampleWitness.checkpoint.source) =
                                     lift (.inr (ProtocolState.entry suffix
                                       (sampleSuccessor name source sampled)))
                             | .ret _ => fun _ _ => False
                             | .commit _ _ _ _ _ => fun _ _ => False
                             | .reveal _ _ _ _ _ _ _ => fun _ _ => False;
                               read program source lift)) :
                             ProtocolState.atCommit program
                               (ProtocolState.entry program source) = false ∧
                             ∃ (name : VarId) (ty : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
                               (law : L.DistExpr (SourcePublicCtx L Γ) ty)
                               (suffix : SourceProgram Player L ((name, .publicData ty) :: Γ) O)
                               (same : program = .sample name fresh law suffix),
                               ∃ (event : (serviceGraph setup .concurrent).EventId)
                                 (output : (serviceGraph setup .concurrent).outputLayout
                                   event = .publicData ty) (sampled : L.Val ty),
                                 sampled ∈ (L.evalDist law
                                   (sourcePublicEnv source.state)).support ∧
                                 event.val = rawState.attempt.phase ∧
                                 (⟨.inr event, output⟩ : FieldRef (graphLayout setup.program)
                                   (.publicData ty)).get?
                                     (phase.drain physical).native.config.store =
                                     some sampled ∧
                                 sampleWitness.checkpoint.residual.lift
                                   (ProtocolState.entry sampleWitness.checkpoint.residual.tail
                                     sampleWitness.checkpoint.source) = lift
                                   (cast (congrArg ProtocolState same.symm)
                                     (.inr (ProtocolState.entry suffix
                                       (sampleSuccessor name source sampled)))) := by
                           cases program with
                           | ret _ => exact observed.elim
                           | commit _ _ _ _ _ => exact observed.elim
                           | reveal _ _ _ _ _ _ _ => exact observed.elim
                           | sample name fresh law suffix =>
                               refine ⟨rfl, name, _, fresh, law, suffix, rfl, ?_⟩
                               simpa only [cast_eq] using observed
                         have observed := sampleObserved
                         rw [rawCheckpoint] at observed
                         dsimp only [RecoverySourceCheckpoint.transfer] at observed
                         obtain ⟨sourceNotCommit, name, payload, fresh, law, suffix,
                           reconstruct, nativeEvent, nativeOutput, nativeSample,
                           nativeSupport, nativeRank, nativeRead, seedPoint⟩ :=
                           unpackSample first.checkpoint.residual.tail first.checkpoint.source
                             first.checkpoint.residual.lift observed
                         have rawNotCommit : ProtocolState.atCommit setup.program
                             (rawWitness.checkpoint.residual.lift
                               (ProtocolState.entry rawWitness.checkpoint.residual.tail
                                 rawWitness.checkpoint.source)) = false := by
                           rw [rawCheckpoint]
                           exact (first.checkpoint.atCommit _).trans sourceNotCommit
                         have priorNotCommit : ProtocolState.atCommit setup.program
                             priorCurrent.point = false := by
                           have information : setup.proposalRecoveryModel.infoOf who
                               sourceStart.trace =
                                 setup.proposalRecoveryModel.infoOf who priorActual :=
                             _priorInfo.symm.trans (congrArg
                               (fun history : setup.proposalRecoveryProtocol.History =>
                                 setup.proposalRecoveryModel.infoOf who history.trace)
                                   priorActualEq).symm
                           have metadata := source_information_metadata setup who
                             sourceStart ⟨some priorCurrent, priorActual⟩ information
                           have controls := ProtocolState.MetadataEq.controls setup.program
                             originalStart.point priorCurrent.point metadata.1
                           have originalNotCommit : ProtocolState.atCommit setup.program
                               originalStart.point = false := by
                             rw [rawCheckpoint] at rawNotCommit
                             simpa only [RecoverySourceCheckpoint.transfer,
                               originalStart, CommitRecoveryState.atPoint] using rawNotCommit
                           exact controls.2.1.symm.trans originalNotCommit
                         have priorFrontier : priorCurrent.BlockFrontier :=
                           setup.commitRecovery_blockFrontier
                             (setup.proposalRecoveryEraseTrace priorActual)
                         have savedAtLive : priorCurrent.saved = priorCurrent.point :=
                           priorFrontier.saved_eq_point_of_not_atCommit priorNotCommit
                         have liveConfig : priorLive = priorSaved := by
                           apply ProtocolState.entry_injective first.checkpoint.residual.tail
                           apply sourceReplaySuffixInjective setup first.checkpoint.origin
                           exact priorPoint.symm.trans (savedAtLive.symm.trans priorSavedPoint)
                         have erasedPriorToNext := setup.proposalRecoveryEraseTrace_prefix
                           actualPriorToNext
                         rcases erasedPriorToNext.reachesWithin.eq_or_step with
                           sameHistory | firstStep
                         · have lengths := congrArg
                             (fun history : setup.commitRecoveryProtocol.History =>
                               history.trace.length) sameHistory
                           simp only [setup.proposalRecoveryEraseTrace_length] at lengths
                           rw [priorActualLength] at lengths
                           omega
                         · obtain ⟨targetJoint, targetLegal, reached, targetMoved,
                             _targetFuel, targetOnward⟩ := firstStep
                           obtain ⟨targetAfter, targetSupport, rfl⟩ :=
                             (PMF.mem_support_map_iff ..).mp targetMoved
                           obtain ⟨targetResult, targetResultSupport, targetInstalled⟩ :=
                             priorCurrent.step_noncommit_atPoint
                               (setup.commitRecovery_blockFrontier
                                 (setup.proposalRecoveryEraseTrace priorActual))
                                   priorNotCommit targetJoint targetAfter targetSupport
                           have targetStepKept : TracePrefix
                               ((setup.proposalRecoveryEraseTrace priorActual).extend
                                 targetJoint targetLegal targetMoved)
                               (setup.proposalRecoveryEraseTrace nextMapped.trace) :=
                             targetOnward.tracePrefix
                           have targetActualStepKept : TracePrefix
                               ((setup.proposalRecoveryEraseTrace priorActual).extend
                                 targetJoint targetLegal targetMoved)
                               (setup.proposalRecoveryEraseTrace nextActual) := by
                             have kept := targetStepKept
                             rw [← nextActualEq] at kept
                             exact kept
                           let Γ := first.checkpoint.residual.context
                           let sampleLift : ProtocolState (.sample name fresh law suffix) →
                               ProtocolState setup.program := fun point =>
                             first.checkpoint.residual.lift
                               (cast (congrArg ProtocolState reconstruct.symm) point)
                           have sampleOrigin : ProtocolSuffix setup.program
                               (.sample name fresh law suffix) sampleLift :=
                             transportOrigin reconstruct.symm first.checkpoint.residual.lift
                               first.checkpoint.origin
                           obtain ⟨embedding, _before, _embeddingEq, compiled, aligned,
                             _views⟩ := transportCompiled reconstruct.symm
                               first.checkpoint.source first.checkpoint.refs
                                 first.checkpoint.registry first.checkpoint.embedding
                                   first.checkpoint.before
                                     previous.execution.application.attempt.phase
                                       first.checkpoint.compiled
                                         first.checkpoint.terminalAlignment
                                           first.checkpoint.residual.lift
                                             first.checkpoint.views
                           have samplePoint : priorCurrent.point =
                               sampleLift (ProtocolState.entry _ priorLive) := by
                             rw [priorPoint]
                             dsimp only [sampleLift]
                             rw [transportEntry reconstruct.symm]
                           change targetResult ∈ (ProtocolState.recoveryStep setup.program
                             priorCurrent.point priorCurrent.excluded targetJoint).support
                               at targetResultSupport
                           rw [samplePoint, sampleOrigin.recoveryStep_lift]
                             at targetResultSupport
                           obtain ⟨sampleResult, sampleSupported, resultEq⟩ :=
                             (PMF.mem_support_map_iff ..).mp targetResultSupport
                           change sampleResult ∈ ((L.evalDist law
                             (sourcePublicEnv priorLive.state)).map (fun value =>
                               ((Sum.inr (ProtocolState.entry suffix
                                 (sampleSuccessor name priorLive value)) :
                                   ProtocolState (.sample name fresh law suffix)),
                                     priorCurrent.excluded))).support at sampleSupported
                           obtain ⟨sampled, _drawSupport, sampleResultEq⟩ :=
                             (PMF.mem_support_map_iff ..).mp sampleSupported
                           subst sampleResult
                           have afterPoint : targetAfter = CommitRecoveryState.atPoint
                               (sampleLift (.inr (ProtocolState.entry suffix
                                 (sampleSuccessor name priorLive sampled))))
                                   priorCurrent.excluded priorCurrent.generation := by
                             rw [targetInstalled, ← resultEq]
                           let head : Fin (eventCount (.sample name fresh law suffix)) :=
                             ⟨0, by simp only [eventCount]; omega⟩
                           let headRef : FieldRef (graphLayout setup.program)
                               (.publicData payload) :=
                             ⟨.inr (embedding.event head), by
                               change outputLayout setup.program (embedding.event head) = _
                               simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero]
                                 using embedding.layout_eq head⟩
                           let nextRefs := first.checkpoint.refs.cons
                             (name := name) (cell := .publicData payload) headRef
                           let nextEmbedding := embedding.tail suffix
                             (by simp only [eventCount]) (fun _ => rfl)
                           have nextAligned : CompiledReadoutSuffix setup.program suffix
                               nextRefs nextEmbedding :=
                             aligned.sampleTail setup.program fresh law suffix
                               first.checkpoint.refs embedding
                           have nextUnique :
                               (((name, .publicData payload) :: Γ).map Prod.fst).Nodup := by
                             simpa only [List.map_cons] using
                               List.nodup_cons.mpr ⟨fresh, first.checkpoint.unique⟩
                           have afterRead : headRef.get?
                               next.execution.application.entry.native.config.store =
                                 some sampled := by
                             have actual := sourceReplay_public_prefix_read setup chosen who
                               labels nextCurrent nextActual nextActualInfo suffix
                                 (fun point => sampleLift (.inr point))
                                   (sampleOrigin.sampleTail fresh law suffix) nextUnique
                                     nextRefs nextEmbedding nextAligned targetAfter
                                       ((setup.proposalRecoveryEraseTrace priorActual).extend
                                         targetJoint targetLegal targetMoved)
                                           (ProtocolState.entry suffix
                                             (sampleSuccessor name priorLive sampled))
                                           (ProtocolState.entry suffix
                                             (sampleSuccessor name priorLive sampled))
                                           (by rw [afterPoint]; rfl)
                                           (by rw [afterPoint]; rfl) rfl targetActualStepKept
                                             (name := name) (kind := .publicData payload)
                                               .here (by trivial)
                             simpa only [ProtocolState.base_entry, nextRefs, ContextRefs.cons,
                               sampleSuccessor, Env.cons_get_here, cellValue] using actual
                           have sameEvent : embedding.event head = nativeEvent := by
                             change nativeEvent.val =
                               previous.execution.application.attempt.phase at nativeRank
                             apply Fin.ext
                             exact (compiled.rankEq head).trans (by
                               simpa only [head, Nat.add_zero] using nativeRank.symm)
                           have nativeHeadRead : headRef.get?
                               (phase.drain physical).native.config.store =
                                 some nativeSample := by
                             simpa only [headRef, sameEvent] using nativeRead
                           have preserved := headRef.get?_preserved
                             (phase.drain physical).native.config.store
                               next.execution.application.entry.native.config.store
                                 (by
                                   rw [nextSettle]
                                   exact sourceReplaySettleSavedStore setup
                                     remaining previous.execution.application.generation
                                       (phase.drain physical)
                                         previous.execution.application.retired)
                                 nativeSample nativeHeadRead
                           have valueEq : sampled = nativeSample :=
                             Option.some.inj (afterRead.symm.trans preserved)
                           have headRead : headRef.get?
                               (sourceSnapshotState setup implementation G reference lost
                                 (phase.drain physical).native).config.store =
                                   some sampled := by
                             have publicStore : (sourceSnapshotState setup implementation G
                                 reference lost (phase.drain physical).native).config.store
                                   headRef.field =
                                     (phase.drain physical).native.config.store
                                       headRef.field := by
                               simp only [sourceSnapshotState, State.swap_config,
                                 Config.swap_store]
                               have visible : (serviceGraph setup .concurrent).fieldPublic
                                   headRef.field := by
                                 change (graphLayout setup.program headRef.field).IsPublic
                                 rw [headRef.layout_eq]
                                 trivial
                               exact ValueSwap.store_public
                                 (graph := serviceGraph setup .concurrent) _ _ _ visible
                             exact (headRef.get?_congr _ _ publicStore).trans
                               (nativeHeadRead.trans (congrArg some valueEq.symm))
                           have nextAgree : nextRefs.Agrees
                               (sampleSuccessor name priorLive sampled).state
                                 (sourceSnapshotState setup implementation G reference lost
                                   (phase.drain physical).native).config.store := by
                             apply ContextRefs.Agrees.cons
                             · intro readName cell member
                               simpa only [liveConfig] using (oldEntryAgrees member)
                             · exact headRead
                           let sampleResidual : ResidualProgram setup.program :=
                             ⟨_, _, suffix, fun point => sampleLift (.inr point)⟩
                           have suffixOrigin : ProtocolSuffix setup.program suffix
                               sampleResidual.lift := sampleOrigin.sampleTail fresh law suffix
                           have seedRemaining :
                               instructionCount sampleWitness.checkpoint.residual.tail =
                                 instructionCount suffix := by
                             have remaining := congrArg
                               (ProtocolState.remaining setup.program) seedPoint
                             rw [sampleWitness.checkpoint.remaining,
                               ProtocolState.remaining_entry] at remaining
                             change instructionCount
                                 sampleWitness.checkpoint.residual.tail =
                               ProtocolState.remaining setup.program
                                 (sampleLift (.inr (ProtocolState.entry suffix
                                   (sampleSuccessor name first.checkpoint.source
                                     nativeSample)))) at remaining
                             simpa only [sampleOrigin.remaining_lift,
                               ProtocolState.remaining, Sum.elim_inr,
                               ProtocolState.remaining_entry] using remaining
                           have residualEq : sampleWitness.checkpoint.residual =
                               sampleResidual :=
                             sampleWitness.checkpoint.origin.residual_eq_of_instructionCount
                               suffix sampleResidual.lift suffixOrigin seedRemaining
                           have targetSeedPoint : targetAfter =
                               CommitRecoveryState.atPoint
                                 (sampleResidual.lift (ProtocolState.entry suffix
                                   (sampleSuccessor name priorLive sampled)))
                                 (phase.drain physical).excluded
                                 previous.execution.application.generation := by
                             rw [afterPoint, priorMask, priorGeneration, ← sampleMask]
                           obtain ⟨seedTarget, seedAtPoint, seedAgrees⟩ :=
                             transportPublicEndpoint residualEq
                               sampleWitness.checkpoint.refs nextRefs
                                 sampleWitness.checkpoint.embedding nextEmbedding
                                   sampleWitness.checkpoint.terminalAlignment nextAligned
                                     (sampleSuccessor name priorLive sampled) targetAfter
                                       (phase.drain physical).excluded
                                         previous.execution.application.generation
                                           targetSeedPoint _ nextAgree
                           obtain ⟨seedState, seedTrace, seedKept, seedDepth⟩ :=
                             setup.proposalRecovery_prefix_at_depth nextMapped.trace
                               (priorMapped.trace.length + 1) (by omega)
                           have literalSeed :
                               (⟨_, (setup.proposalRecoveryEraseTrace priorActual).extend
                                  targetJoint targetLegal targetMoved⟩ :
                                   setup.commitRecoveryProtocol.History) =
                               ⟨_, setup.proposalRecoveryEraseTrace seedTrace⟩ := by
                             apply targetStepKept.eq_of_same_length
                               (setup.proposalRecoveryEraseTrace_prefix seedKept)
                             simpa only [Trace.length,
                               setup.proposalRecoveryEraseTrace_length,
                               priorActualLength] using seedDepth.symm
                           have seedStateEq : seedState = some targetAfter :=
                             (congrArg History.state literalSeed).symm
                           cases seedStateEq
                           have endpointMask : nextCurrent.excluded =
                               (phase.drain physical).excluded :=
                             nextMask.trans nextEntryMask
                           have nativeGeneration : next.execution.application.generation =
                               previous.execution.application.generation := by
                             rw [nextSettle]
                             exact (PhaseRuntimeState.settle_generation_archive_of_same_excluded
                             remaining
                                 previous.execution.application.generation
                                   (phase.drain physical) (phase.drain physical)
                                     previous.execution.application.retired rfl).1
                           have sameGeneration : targetAfter.generation =
                               nextCurrent.generation := by
                             rw [seedAtPoint]
                             exact (nextGeneration.trans nativeGeneration).symm
                           have clock := setup.commitRecovery_same_generation_length
                             (setup.proposalRecoveryEraseTrace_prefix seedKept).reachesWithin
                               targetAfter nextCurrent rfl nextState sameGeneration
                           simp only [setup.proposalRecoveryEraseTrace_length] at clock
                           exact tailRec remaining
                             previous.execution.application.generation (phase.drain physical)
                               previous.execution.application.retired sampleWitness
                                 seedTarget targetAfter seedTrace seedAtPoint seedKept
                                    seedAgrees endpointMask clock nextSettle observedCell
  have completedVisits : ∀ lost, SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who lost →
    ∀ (before after : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before))
      (afterTrace : (nativeProtocol).Trace (some after)),
      TracePrefix prior afterTrace → TracePrefix afterTrace referenceTrace →
    ∀ (phase : RuntimePhase (serviceGraph setup .concurrent))
      (remaining : List (RuntimePhase (serviceGraph setup .concurrent))),
      before.execution.application.phases = phase :: remaining →
    ∀ (physical : RecoveryState (serviceGraph setup .concurrent)),
      after.execution.application =
        ({ before.execution.application with current := physical } :
          PhaseRuntimeState (serviceGraph setup .concurrent)).normalize →
      phase.Finished (phase.drain physical) → phase.kind = .commitment →
      PhaseClosingEffect implementation.runtime implementation.leaks
        before.execution after.execution physical →
      after.execution.application.attempt ≠ before.execution.application.attempt →
      (phase.drain physical).native.BindingInvariant →
      BindingStamp (fun owner => (nativeApplication).outputs
        (before.execution.recall owner)) before.execution.application.attempt
          (phase.drain physical).native →
      let first := (checkpointSelection setup implementation operational prior).val.checkpoint
      let last := (checkpointSelection setup implementation operational afterTrace).val.checkpoint
      let segment := SourceProgram.commitPhase first.residual.tail
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          segment.reconstruct.symm) first.embedding
      ∃ (sourceLast : CommitRecoveryState setup.program)
        (closed : setup.commitRecoveryProtocol.Trace (some sourceLast))
        (labeled : setup.proposalRecoveryProtocol.Trace (some sourceLast))
        (fuel : Nat)
        (targetFirst targetLast : CommitRecoveryState setup.program)
        (targetPrior : setup.proposalRecoveryProtocol.Trace (some targetFirst))
        (targetEnd : setup.proposalRecoveryProtocol.Trace (some targetLast))
        (targetEntry : SourceProgram.Config Player L first.residual.context)
        (finished : SourceProgram.Config Player L segment.context)
        (excluded : Finset Player)
        (attempt : segment.block.Attempt targetEntry targetFirst.excluded
          finished excluded)
        (monotone : targetFirst.excluded ⊆ excluded),
        setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, first.trace⟩
          ⟨some sourceLast, closed⟩ ∧
        setup.recoveryJointRecall closed =
          (first.commitInstructionWord (phase.drain physical).native).reverse ++
            setup.recoveryJointRecall first.trace ∧
        TracePrefix closed last.trace ∧
        TracePrefix labeled
          (canonicalSource setup implementation operational
            ⟨some reference, referenceTrace⟩).trace ∧
        setup.proposalRecoveryEraseTrace labeled = closed ∧
        TracePrefix targetPrior targetEnd ∧
        TracePrefix targetEnd g.trace ∧
        TracePrefix targetEnd targetTrace ∧
        targetPrior.length = first.trace.length ∧
        targetEnd.length = closed.length ∧
        targetFirst.point = first.residual.lift
          (cast (congrArg ProtocolState segment.reconstruct)
            (ProtocolState.entry (segment.block.prepend segment.suffix) targetEntry)) ∧
        ProtocolState.atCommit setup.program targetFirst.saved = true ∧
        ProtocolState.commitEnd setup.program targetFirst.saved ≤
          instructionCount segment.suffix ∧
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetEnd) =
          attempt.joints.reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetPrior) ∧
        targetLast = (targetFirst.install
          (first.residual.lift
            (cast (congrArg ProtocolState segment.reconstruct)
              (segment.block.liftPoint segment.suffix
                (ProtocolState.entry segment.suffix finished))), excluded)
          monotone).close ∧
        SourceReplayVisitImage setup segment.block segment.suffix embedding attempt
          (sourceSnapshotState setup implementation
            ⟨some targetCurrent, targetTrace⟩ reference lost
              (phase.drain physical).native) first.refs ∧
        BindingStamp (fun owner => (nativeApplication).outputs
          (reference.execution.recall owner)) before.execution.application.attempt
            (phase.drain physical).native := by
    intro lost restricted before after prior afterTrace priorToAfter afterRetained
      phase remaining installed physical normalized finished commitment effect changed
      binding rawStamp
    have priorRetained : TracePrefix prior referenceTrace :=
      priorToAfter.trans afterRetained
    obtain ⟨priorMapped, priorCurrent, priorLive, priorSaved, priorEntryKept,
      priorToG, priorDepth, priorInfo, priorState, priorPoint, priorSavedPoint,
      priorMask, priorGeneration, priorAgrees⟩ :=
      chronology lost restricted prior priorRetained
    obtain ⟨sourceLast, closed, starting, labeled, fuel, sourcePath,
      sourceWord, intervalLength, startingKept, startingErase, closedErase,
      labeledKept, closedSelected, _labeledSelected, _closedMass⟩ :=
      sourceReplayFactualCommitInterval setup implementation operational
        before after reference prior afterTrace referenceTrace priorToAfter
          afterRetained phase remaining installed physical normalized finished
            commitment effect changed
    have referenceStamp : BindingStamp
        (fun owner => (nativeApplication).outputs (reference.execution.recall owner))
        before.execution.application.attempt (phase.drain physical).native :=
      (sourceReplayCloseEvidence setup implementation reference before after
        referenceTrace prior priorRetained
          (checkpointSelection setup implementation operational prior).val
            phase (by rw [installed]; rfl) commitment physical effect changed
              rawStamp).2
    let firstWitness := (checkpointSelection setup implementation operational prior).val
    let first := firstWitness.checkpoint
    let originalStart : CommitRecoveryState setup.program :=
      CommitRecoveryState.atPoint
        (first.residual.lift (ProtocolState.entry first.residual.tail first.source))
          before.execution.application.entry.excluded
            before.execution.application.generation
    let sourceStart : setup.proposalRecoveryProtocol.History :=
      ⟨some originalStart, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup
          (PhaseProposal.sourceArchive reference.execution.network.inputs)) first.trace⟩
    have sourceStartKept : TracePrefix sourceStart.trace
        (canonicalSource setup implementation operational
          ⟨some reference, referenceTrace⟩).trace := by
      have kept := checkpointSelection_prefix setup implementation operational
        before reference prior referenceTrace priorRetained
      exact setup.proposalRecoveryLiftTrace_prefix _ kept
    have startSame : starting = sourceStart.trace := by
      have equalHistory := (startingKept.trans labeledKept).eq_of_same_length
        sourceStartKept (by
          have count := congrArg (fun trace => trace.length) startingErase
          simpa only [sourceStart, setup.proposalRecoveryEraseTrace_length,
            setup.proposalRecoveryLiftTrace_length] using count)
      exact eq_of_heq (History.mk.inj equalHistory).2
    have originalInterval : TracePrefix sourceStart.trace labeled := by
      rw [← startSame]
      exact startingKept
    let sourceClosed : setup.proposalRecoveryProtocol.History :=
      ⟨some sourceLast, labeled⟩
    have sourceClosedCut : TracePrefix sourceClosed.trace sourceCut.trace :=
      labeledKept.trans canonicalToCut
    have sourceBounds := source_checkpoint_binding_interval setup implementation
      firstWitness operational.maximalPhases phase remaining installed commitment
    have geometry := first.commit_phase_geometry phase remaining installed commitment
      firstWitness.receipts.exclusion.frontier
        (operational.maximalPhases.suffix firstWitness.suffix)
    let segment := SourceProgram.commitPhase first.residual.tail
    have blockPositive : 0 < segment.block.length := by
      rw [geometry.1]
      have nonempty := phase.nonempty
      omega
    let blockLift : ProtocolState (segment.block.prepend segment.suffix) →
        ProtocolState setup.program := fun point => first.residual.lift
          (cast (congrArg ProtocolState segment.reconstruct) point)
    have transportOrigin {Γ : SourceCtx Player L} {O : Finset VarId}
        {left right : SourceProgram Player L Γ O} (equal : left = right)
        (lift : ProtocolState right → ProtocolState setup.program)
        (origin : ProtocolSuffix setup.program right lift) :
        ProtocolSuffix setup.program left
          (fun point => lift (cast (congrArg ProtocolState equal) point)) := by
      cases equal
      exact origin
    have transportEntry {Γ : SourceCtx Player L} {O : Finset VarId}
        {left right : SourceProgram Player L Γ O} (equal : left = right)
        (entry : SourceProgram.Config Player L Γ) :
        cast (congrArg ProtocolState equal) (ProtocolState.entry left entry) =
          ProtocolState.entry right entry := by
      cases equal
      rfl
    have blockOrigin : ProtocolSuffix setup.program
        (segment.block.prepend segment.suffix) blockLift :=
      transportOrigin segment.reconstruct first.residual.lift first.origin
    have originalDepth : labeled.length = sourceStart.trace.length +
        segment.block.length := by
      have wordLength := source_commit_instruction_word_length setup first
        (phase.drain physical).native
      rw [intervalLength, startSame, wordLength]
      change sourceStart.trace.length +
        (ProtocolState.remaining setup.program originalStart.point -
          ProtocolState.commitEnd setup.program originalStart.point) = _
      dsimp only [originalStart, CommitRecoveryState.atPoint]
      rw [first.remaining, first.commitEnd, ProtocolState.remaining_entry,
        ProtocolState.commitEnd_entry]
      have count := segment.block.instructionCount_prepend segment.suffix
      rw [segment.reconstruct] at count
      change sourceStart.trace.length +
        (instructionCount first.residual.tail - instructionCount segment.suffix) = _
      omega
    have paired := sourceReplayCompletedInterval setup who sourceCut g cutInfo
      (setup.initialConfig setup.initialLaw.support_nonempty.choose)
        segment.block segment.suffix blockLift blockOrigin first.source originalStart
          sourceLast sourceStart.trace labeled originalInterval sourceClosedCut
            (by
              change first.residual.lift
                  (ProtocolState.entry first.residual.tail first.source) =
                first.residual.lift
                  (cast (congrArg ProtocolState segment.reconstruct)
                    (ProtocolState.entry
                      (segment.block.prepend segment.suffix) first.source))
              rw [transportEntry segment.reconstruct])
            (by simpa only [originalStart, CommitRecoveryState.atPoint] using
              sourceBounds.1)
            (by
              change ProtocolState.commitEnd setup.program
                  (first.residual.lift
                    (ProtocolState.entry first.residual.tail first.source)) ≤
                instructionCount segment.suffix
              rw [first.commitEnd, ProtocolState.commitEnd_entry])
            blockPositive originalDepth
    obtain ⟨targetFirst, targetLast, targetPrior, targetEnd, targetRowEntry,
      targetFinished, targetExcluded, targetAttempt, addresses, targetInterval,
      targetToG, targetPriorDepth, targetEndDepth, targetPriorInfo, targetEndInfo,
      targetPoint, targetAtCommit, targetEndpoint, targetMask, targetGeneration,
      targetPath, targetWord, targetAddress, monotone, targetClosedEq⟩ := paired
    have gToG : TracePrefix g.trace G.trace := by
      have support := supported
      unfold sourceForcedBlock at support
      obtain ⟨middle, firstStep, laterSteps⟩ := (PMF.mem_support_bind_iff ..).mp support
      exact (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
        g middle firstStep).tracePrefix.trans
          (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
            middle G laterSteps).tracePrefix
    have targetToGFull : TracePrefix targetEnd G.trace := targetToG.trans gToG
    have targetPriorDepth' : targetPrior.length = first.trace.length := by
      rw [targetPriorDepth]
      simp only [sourceStart, setup.proposalRecoveryLiftTrace_length]
    have targetEndDepth' : targetEnd.length = closed.length := by
      rw [targetEndDepth]
      have length := congrArg (fun trace => trace.length) closedErase
      simpa only [setup.proposalRecoveryEraseTrace_length] using length
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program)
        segment.reconstruct.symm) first.embedding
    have visit : SourceReplayVisitImage setup segment.block segment.suffix embedding
        targetAttempt
        (sourceSnapshotState setup implementation G reference lost
          (phase.drain physical).native) first.refs := by
      have targetPriorToG : TracePrefix targetPrior g.trace :=
        targetInterval.trans targetToG
      have priorMappedToG : TracePrefix priorMapped.trace g.trace :=
        priorEntryKept.trans entryKept
      have targetStartEq : (⟨some targetFirst, targetPrior⟩ :
          setup.proposalRecoveryProtocol.History) = priorMapped :=
        targetPriorToG.eq_of_same_length priorMappedToG
          (targetPriorDepth'.trans priorDepth.symm)
      have targetFirstEq : targetFirst = priorCurrent := by
        have states := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
          history.state) targetStartEq
        rw [priorState] at states
        exact Option.some.inj states
      have priorRank : ProtocolState.remaining setup.program priorCurrent.point =
          ProtocolState.remaining setup.program priorCurrent.saved := by
        rw [priorPoint, priorSavedPoint, first.origin.remaining_lift,
          first.origin.remaining_lift, ProtocolState.remaining_entry,
          ProtocolState.remaining_entry]
      have priorCommit : ProtocolState.atCommit setup.program
          priorCurrent.point = true := by
        rw [priorPoint, first.origin.atCommit_lift]
        have sameEntry {Γ : SourceCtx Player L} {O : Finset VarId}
            (program : SourceProgram Player L Γ O)
            (left right : SourceProgram.Config Player L Γ) :
            ProtocolState.atCommit program
                                     (ProtocolState.entry program left) =
              ProtocolState.atCommit program
                                  (ProtocolState.entry program right) := by
          cases program <;> rfl
        rw [sameEntry first.residual.tail priorLive first.source]
        exact (first.atCommit _).symm.trans sourceBounds.1
      have priorEntry := source_commit_entry_eq_atPoint setup priorCurrent
        (targetFirstEq ▸ targetPrior) priorCommit priorRank
      have priorSavedEq : priorCurrent.saved = priorCurrent.point := by
        rw [priorEntry]
        rfl
      have targetPointOriginal : targetFirst.point = first.residual.lift
          (ProtocolState.entry first.residual.tail targetRowEntry) := by
        rw [targetPoint]
        dsimp only [blockLift]
        rw [transportEntry segment.reconstruct]
      have targetRowEntryEq : targetRowEntry = priorSaved := by
        apply ProtocolState.entry_injective first.residual.tail
        apply sourceReplaySuffixInjective setup first.origin
        calc
          first.residual.lift
              (ProtocolState.entry first.residual.tail targetRowEntry) =
            targetFirst.point := targetPointOriginal.symm
          _ = priorCurrent.point := congrArg CommitRecoveryState.point targetFirstEq
          _ = priorCurrent.saved := priorSavedEq.symm
          _ = first.residual.lift
                (ProtocolState.entry first.residual.tail priorSaved) := priorSavedPoint
      have rawClosedCut : TracePrefix closed
          (setup.proposalRecoveryEraseTrace sourceCut.trace) := by
        rw [← closedErase]
        exact setup.proposalRecoveryEraseTrace_prefix sourceClosedCut
      have normalizedSettle : after.execution.application =
          PhaseRuntimeState.settle (phase :: remaining)
            before.execution.application.generation
              before.execution.application.entry physical
                before.execution.application.retired := by
        rw [normalized]
        simp only [PhaseRuntimeState.normalize, installed]
      let inputs := setup.initialLaw.map encodeInputs
      have initialEq : nativeInitial = inputs.map
          (PhaseRuntimeState.initial implementation.plan) := by
        simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp,
          Function.comp_def]
      have rawTrace := (nativeMenu).toRawTrace nativeInitial
        implementation.horizon implementation.scheduler prior
      rw [initialEq] at rawTrace
      have rows : sourceAttemptTableReads setup targetAttempt segment.suffix embedding
          (sourceSnapshotState setup implementation G reference lost
            (phase.drain physical).native) := by
        have readback := sourceReplayFixedSnapshotTableReads setup values
          implementation operational reference
            (sourceCutTrace setup implementation referenceTrace) who event cut g sameInfo
            good choice properChoice G supported lost after
              (sourceCutTrace setup implementation afterTrace)
              (tracePrefix_initializer setup implementation initialEq afterRetained)
              before (sourceCutTrace setup implementation prior)
              (tracePrefix_initializer setup implementation initialEq priorRetained)
              firstWitness phase remaining installed commitment
                physical finished normalizedSettle binding effect changed rawStamp restricted
                  first ⟨some sourceLast, closed⟩ sourcePath sourceWord sourceCut
                    rawClosedCut cutInfo cutGood
        dsimp only [segment] at readback
        exact readback targetRowEntry targetFirst targetPrior targetFinished
          targetExcluded targetAttempt ⟨some targetLast, targetEnd⟩ targetToG
            targetInterval targetPoint (by
              simpa only [originalStart, CommitRecoveryState.atPoint] using
                targetMask.symm) targetAtCommit targetEndpoint targetWord
              (by rw [targetPriorDepth']) (by
                have length := congrArg (fun trace => trace.length) closedErase
                simp only [setup.proposalRecoveryEraseTrace_length] at length
                simp only [sourceStart, setup.proposalRecoveryLiftTrace_length]
                  at originalDepth
                calc
                  targetPrior.length + segment.block.length =
                    first.trace.length + segment.block.length := by rw [targetPriorDepth']
                  _ = labeled.length := originalDepth.symm
                  _ = closed.length := length
                  _ ≤ _ := le_refl _)
      have stored := phaseStoredCheckpoint_history implementation.runtime
        implementation.leaks implementation.plan inputs implementation.horizon
          implementation.scheduler rawTrace
      have accepted := phaseAcceptedCheckpoint_history implementation.runtime
        implementation.leaks implementation.plan inputs implementation.horizon
          implementation.scheduler rawTrace
      have rawStore : KeepsStore before.execution.application.current.native
          physical.native := by
        rcases effect with ⟨_id, message, native, _found, _reached, handled, rfl⟩ |
          ⟨command, native, _reached, supported, rfl⟩
        · intro field value present
          change native.config.store field = some value
          exact handle_store_of_some implementation.runtime _ native
            ⟨message.id, message.payload.packet.call⟩ handled field value present
        · intro field value present
          change native.config.store field = some value
          exact environmentStep_store_of_some implementation.runtime _ native
            command supported field value present
      have oldStore : KeepsStore before.execution.application.entry.native
          (phase.drain physical).native := by
        intro field value present
        exact phase.drain_keepsStore physical field value
          (rawStore field value (stored field value present))
      have castOptionNone {α β : Type} (equal : α = β) :
          cast (congrArg Option equal) (none : Option α) = (none : Option β) := by
        cases equal
        rfl
      have castOptionSome {α β : Type} (equal : α = β) (value : α) :
          cast (congrArg Option equal) (some value) = some (cast equal value) := by
        cases equal
        rfl
      have entryAgrees : first.refs.Agrees targetRowEntry.state
          (sourceSnapshotState setup implementation G reference lost
            (phase.drain physical).native).config.store := by
        rw [targetRowEntryEq]
        apply sourceReplayEntryAgreesOfPreserved setup implementation first.refs
          priorSaved G reference lost before.execution.application.entry.native
            (phase.drain physical).native priorAgrees
        · intro name cell source
          let field := (first.refs.get source).field
          have occupied := first.agrees source
          cases present : before.execution.application.entry.native.config.store field with
          | none =>
              have empty : (first.refs.get source).get?
                  before.execution.application.entry.native.config.store = none := by
                unfold FieldRef.get?
                rw [present]
                exact castOptionNone (congrArg EventField.Value
                  (first.refs.get source).layout_eq)
              rw [empty] at occupied
              cases occupied
          | some value => exact (oldStore field value present).symm
        · intro name cell source owner payload shape value successful
          let field := (first.refs.get source).field
          have read : (⟨field, shape⟩ : EventGraph.FieldRef
              (serviceGraph setup .concurrent).layout (.binding owner payload)).get?
              before.execution.application.entry.native.config.store =
                some (.success value) := by
            unfold EventGraph.FieldRef.get?
            rw [successful]
            rw [castOptionSome (congrArg EventField.Value shape)]
            exact congrArg some
              ((cast_cast (congrArg EventField.Value shape.symm)
                (congrArg EventField.Value shape) (.success value)).trans (cast_eq _ _))
          obtain ⟨candidate, candidatePresent, _owned, _openable⟩ :=
            (phaseBindingRecord_history implementation.runtime implementation.leaks
              implementation.plan inputs implementation.horizon
                implementation.scheduler rawTrace).saved.success_provenance
                  ⟨field, shape⟩ value read
          have live := accepted field candidate candidatePresent
          have raw := effect.accepted_preserved implementation.runtime
            implementation.leaks field candidate live
          have drained : (phase.drain physical).native.accepted field =
              some candidate := by
            rw [(phase.drain_tables physical).1]
            exact raw
          exact candidatePresent.trans drained.symm
      exact ⟨entryAgrees, rows,
        decodeCommitAttempt_eq_of_target_rows setup targetAttempt segment.suffix
          embedding (sourceSnapshotState setup implementation G reference lost
            (phase.drain physical).native) rows,
        target_attempt_state_agrees setup targetAttempt segment.suffix embedding
          (sourceSnapshotState setup implementation G reference lost
            (phase.drain physical).native) first.refs entryAgrees rows⟩
    refine ⟨sourceLast, closed, labeled, fuel, targetFirst, targetLast,
      targetPrior, targetEnd, targetRowEntry, targetFinished, targetExcluded,
      targetAttempt, monotone, sourcePath, sourceWord, closedSelected,
      labeledKept, closedErase, targetInterval, targetToG,
      targetToGFull, targetPriorDepth', targetEndDepth', targetPoint,
      targetAtCommit, targetEndpoint, targetWord, targetClosedEq, visit,
      referenceStamp⟩
  have selectedAgreement : SourceReplaySelectedAgreement
      (setup := setup) (implementation := implementation)
      operational who reference referenceTrace g targetCurrent targetTrace := by
    intro lost restricted before prior retained
    obtain ⟨mapped, current, live, saved, mappedEntryKept, mappedToG,
      depth, information, state, point, savedPoint, mask, generation,
      agrees⟩ := chronology lost restricted prior retained
    exact ⟨mapped, current, live, saved, mappedEntryKept.trans entryKept,
      mappedToG, depth, information, state, point, savedPoint, mask,
      generation, agrees⟩
  exact ⟨selectedAgreement, completedVisits⟩


end Vegas.PhaseProposalQualifiedBinding

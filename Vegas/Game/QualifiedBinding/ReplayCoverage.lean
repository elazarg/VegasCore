/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.RawReplay
import Vegas.Game.QualifiedBinding.ForeignPosterior

/-! # Original annotation readback and normalized replay coverage -/

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

/-- A supported ordinary commitment interval preserves the absence of generated
foreign failures and has its literal source depth, including an empty interval. -/
private theorem ordinary_source_supported_good
    (who : Player) (anchor : (nativeApplication).Control)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase block suffix)
    (good : setup.proposalRecoveryForeignGood who ⟨some cursor.current, cursor.trace⟩)
    (finished : setup.proposalRecoveryProtocol.History)
    (supported : finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length
        ⟨some cursor.current, cursor.trace⟩).support) :
    setup.proposalRecoveryForeignGood who finished ∧
      finished.trace.length = cursor.trace.length + block.length := by
  obtain ⟨_config, last, lastTrace, attempt, historyEq, _point, _excluded, _entry,
      _generation, word, labels, proper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values block suffix cursor.lift
      cursor.origin cursor.source cursor.current cursor.trace cursor.point
        (cursor.excluded.trans cursor.entryExcluded.symm) finished supported
  have wordFailure (owner : Player) {state : setup.proposalRecoveryProtocol.State}
      (trace : setup.proposalRecoveryProtocol.Trace state) :
      setup.GeneratedPreparationHistory owner ⟨state, trace⟩ ↔
        ∃ joint ∈ setup.proposalRecoveryJointRecall trace,
          ProposalRecoveryMove.GeneratedPreparationFailure (joint owner) := by
    induction trace with
    | start =>
      simp [Setup.GeneratedPreparationHistory, Setup.proposalRecoveryJointRecall,
        InfoSignals.ownPlay]
    | extend prior joint legal moved ih =>
      unfold Setup.GeneratedPreparationHistory at ih ⊢
      rw [InfoSignals.ownPlay_extend]
      cases selected : joint owner with
      | none =>
        simpa only [Setup.proposalRecoveryJointRecall, selected,
          ProposalRecoveryMove.GeneratedPreparationFailure, Option.elim_none,
          List.mem_cons, exists_eq_or_imp, false_or] using ih
      | some move =>
        simpa only [Setup.proposalRecoveryJointRecall, selected, List.mem_cons,
          exists_eq_or_imp] using (or_congr Iff.rfl ih)
  constructor
  · rw [historyEq]
    intro owner foreign generated
    obtain ⟨joint, member, failed⟩ := (wordFailure owner lastTrace).mp generated
    rw [labels] at member
    rcases List.mem_append.mp member with fresh | earlier
    · obtain ⟨raw, rawMember, same⟩ := List.mem_map.mp fresh
      rw [← same] at failed
      cases selected : raw owner with
      | none =>
        simp only [selected, Option.map_none,
          ProposalRecoveryMove.GeneratedPreparationFailure, Option.elim_none] at failed
      | some move =>
        have noFailure := (proper raw (List.mem_reverse.mp rawMember) owner move selected).2
        exact noFailure (ProposalRecoveryMove.generatedPreparationFailure_flags _ (by
          simpa only [selected, Option.map_some] using failed)).2
    · exact good owner foreign ((wordFailure owner cursor.trace).mpr ⟨joint, earlier, failed⟩)
  · rw [historyEq]
    have length := congrArg List.length word
    simpa only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
      List.length_append, List.length_reverse, attempt.joints_length, Nat.add_comm] using length

open Classical in
/-- Every positive original annotated atom belongs to the ordinary source pair,
and its structural foreign word is determined by the completed source history.
The entry tag and the whole original joint input remain those of the annotation. -/
theorem positive_original_annotated_pair
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    let low := control.execution.application.attempt.phase
    let high := low + block.block.length
    let k := event.val - low
    let ordinary := sourceUnflaggedStrategy setup values
    let pair := (setup.proposalRecoveryModel.runBehavioralFrom ordinary k target).bind fun g =>
      (setup.proposalRecoveryModel.runBehavioralFrom ordinary (block.block.length - k) g).map
        (Prod.mk g)
    let completed := fun history : setup.proposalRecoveryProtocol.History =>
      history.state.bind fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point
    let observed := fun point : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completed point.2 with
      | none => false
      | some result => decide (
          issuedLedger setup implementation block.block low control high who (result.view who) ∧
          block.block.wordAction who k (result.view who) = decodeEventAction setup.program event
            (cast (congrArg EventField.Action clean.binding.symm) (.success value)) ∧
          ∀ owner, owner ≠ who → issuedLedger setup implementation block.block low control high
            owner (result.view owner))
    setup.proposalRecoveryClosedKey who target = setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational ⟨some control, trace⟩) ∧
      setup.proposalRecoveryModel.historyReachWeight sourceProfile target ≠ 0 ∧
      (cut, finished) ∈ pair.support ∧ observed (cut, finished) = true ∧
      TracePrefix target.trace cut.trace ∧ TracePrefix cut.trace finished.trace ∧
      ∃ sourceRead : setup.proposalRecoveryProtocol.History → SourceProgram.History Player L,
        sourceRead finished = word ∧
        (∀ other, (other, true) ∈ (ordinaryForeignJoint setup values implementation operational who
          ⟨some control, trace⟩ target).support →
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event
            payload target other value (cut, finished) ≠ 0 → other = word) ∧
        ∃ (phase : RuntimePhase (serviceGraph setup .concurrent))
          (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
            implementation.leaks implementation.plan control phase block.block block.suffix)
          (result : SourceProgram.Config Player L block.context)
          (last : CommitRecoveryState setup.program)
          (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
          (attempt : block.block.Attempt cursor.source cursor.current.excluded result
            last.excluded),
          target = (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) ∧
          (∀ point, cursor.lift point = checkpoint.residual.lift
            (cast (congrArg ProtocolState block.reconstruct) point)) ∧
          finished = ⟨some last, lastTrace⟩ ∧
          word = (fun owner => if owner = who then [] else
            (attempt.withoutMisses ∅ cursor.source).history owner) ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
            attempt.joints.reverse ++ setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace cursor.trace) ∧
          setup.proposalRecoveryJointRecall lastTrace = attempt.joints.reverse.map
            (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) ++
              setup.proposalRecoveryJointRecall cursor.trace ∧
          last.point = cursor.lift (block.block.liftPoint block.suffix
            (ProtocolState.entry block.suffix result)) ∧
          last.excluded = cursor.current.excluded ∧
          (∀ owner, issuedLedger setup implementation block.block low control high owner
            (result.view owner)) ∧ cursor.offset = low ∧
          ∀ (owner : Player), owner ∉ cursor.current.excluded →
            ∀ (index : Fin (eventCount (block.block.prepend block.suffix))),
              index.val < block.block.length → ∀ (ty : L.Ty)
              (binding : (serviceGraph setup .concurrent).outputLayout
                (cursor.embedding.event index) = .binding owner ty)
              (selected : PublicationResult (L.Val ty))
              (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
              message ∈ (nativeApplication).outputs (control.execution.recall owner) →
              message.payload.attempt = control.execution.application.attempt →
              ∀ (handle : Handle (serviceGraph setup .concurrent)),
                message.payload.packet.call = .commitment (cursor.embedding.event index) handle →
                control.execution.application.current.native.bindingResult handle ty =
                  selected →
                sourceBindingAt setup control.execution.application.attempt
                  (cursor.embedding.event index) owner ty binding finished.trace =
                    PublicationResult.equivOption selected ∧
                sourceHandleMeaning setup implementation finished control handle =
                  (PublicationResult.equivOption selected).map
                    (fun raw => (⟨ty, raw⟩ : Raw L)) := by
  classical
  intro checkpoint block low high k ordinary pair completed observed
  have factors := mul_ne_zero_iff.mp positive
  have prefixPositive := (mul_ne_zero_iff.mp factors.1).1
  have gatePositive := (mul_ne_zero_iff.mp factors.1).2
  have admitted : bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape =
      true := by
    cases bit : bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
    · simp only [bit, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at gatePositive
    · rfl
  have annotation := annotatedPrefixWeight_support setup values implementation operational
    sourceProfile nativeProfile who ⟨some control, trace⟩ tape target word canonicalSupported
      prefixPositive
  have atoms := foreign_posterior_cut_pair_atoms setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape target word canonicalSupported prefixPositive
      past view information event payload clean admitted value
  obtain ⟨sourceRead, _marginal, atom, structural⟩ := atoms.2.2.2.2.2.2
  let foreign := ordinaryForeignJoint setup values implementation operational who
    ⟨some control, trace⟩ target
  have foreignPresent : true ∈ (foreign.map Prod.snd).support := atoms.2.1
  have posteriorPositive (other : SourceProgram.History Player L)
      (supported : (other, true) ∈ foreign.support) :
      (fiberPosterior foreign Prod.snd true) (other, true) ≠ 0 := by
    apply (PMF.mem_support_iff ..).mp
    rw [fiberPosterior_support _ _ _ foreignPresent]
    exact ⟨rfl, supported⟩
  have sourceAtom (other : SourceProgram.History Player L)
      (supported : (other, true) ∈ foreign.support)
      (forcedPositive : sourceForcedBlockJoint setup values implementation who
        ⟨some control, trace⟩ event payload target other value (cut, finished) ≠ 0) :
      (cut, finished) ∈ pair.support ∧ observed (cut, finished) = true ∧
        sourceRead finished = other := by
    have nonzero : (pair.map observed) true *
        ((fiberPosterior foreign Prod.snd true) (other, true) *
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event
            payload target other value (cut, finished)) ≠ 0 :=
      mul_ne_zero ((PMF.mem_support_iff ..).mp atoms.1)
        (mul_ne_zero (posteriorPositive other supported) forcedPositive)
    have identity := atom other (cut, finished) supported
    change (pair.map observed) true *
        ((fiberPosterior foreign Prod.snd true) (other, true) *
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event
            payload target other value (cut, finished)) =
        if observed (cut, finished) = true ∧ sourceRead finished = other then
          pair (cut, finished) else 0 at identity
    rw [identity] at nonzero
    split at nonzero
    · rename_i matched
      exact ⟨(PMF.mem_support_iff ..).mpr nonzero, matched⟩
    · exact (nonzero rfl).elim
  have supported := sourceAtom word annotation.2.2 factors.2
  obtain ⟨g, first, rest⟩ := (PMF.mem_support_bind_iff ..).mp supported.1
  obtain ⟨G, last, same⟩ := (PMF.mem_support_map_iff ..).mp rest
  have cutEq : g = cut := congrArg Prod.fst same
  have finishedEq : G = finished := congrArg Prod.snd same
  subst g
  subst G
  refine ⟨annotation.1, annotation.2.1, supported.1, supported.2.1, ?_, ?_,
    sourceRead, supported.2.2, ?_, ?_⟩
  · exact (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary k target cut
      first).tracePrefix
  · exact (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary
      (block.block.length - k) cut finished last).tracePrefix
  · intro other member forcedPositive
    exact ((sourceAtom other member forcedPositive).2.2).symm.trans supported.2.2
  · have complete : finished ∈ (pair.map Prod.snd).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨(cut, finished), supported.1, rfl⟩
    obtain ⟨phase, cursor, targetEq, cursorLift, related⟩ := structural
    obtain ⟨result, lastState, lastTrace, attempt, finishedEq, readEq, rows, labels,
        point, excluded, offset⟩ :=
      related finished complete
    have parsed : residualEntry? block.suffix
        (fun p => cursor.lift (block.block.liftPoint block.suffix p)) lastState.point =
          some result :=
      (residualEntry?_eq_some_iff (cursor.origin.compose
        (block.block.protocolSuffix block.suffix)) lastState.point result).mpr point.symm
    have observedResult := supported.2.1
    change (match completed finished with
      | none => false
      | some result => decide (
          issuedLedger setup implementation block.block low control high who (result.view who) ∧
          block.block.wordAction who k (result.view who) = decodeEventAction setup.program event
            (cast (congrArg EventField.Action clean.binding.symm) (.success value)) ∧
          ∀ owner, owner ≠ who → issuedLedger setup implementation block.block low control high
            owner (result.view owner))) = true at observedResult
    have completedResult : completed finished = some result := by
      dsimp only [completed]
      rw [finishedEq]
      simp only [Option.bind_some]
      simpa only [cursorLift] using parsed
    rw [completedResult] at observedResult
    have tests := decide_eq_true_eq.mp observedResult
    have ledger : ∀ owner, issuedLedger setup implementation block.block low control high owner
        (result.view owner) := by
      intro owner
      by_cases same : owner = who
      · subst owner
        exact tests.1
      · exact tests.2.2 owner same
    refine ⟨phase, cursor, result, lastState, lastTrace, attempt, targetEq, cursorLift, finishedEq,
      supported.2.2.symm.trans readEq, rows, labels, point, excluded, ledger, offset, ?_⟩
    intro owner active index inside ty binding selected message emitted currentAttempt handle call
      value
    have nonempty : 0 < block.block.length := by omega
    have rank : (cursor.embedding.event index).val = low + index.val := by
      rw [cursor.compiled.rankEq, offset]
    have clock : low + instructionCount (block.block.prepend block.suffix) =
        instructionCount setup.program := by
      have count := cursor.compiled.countEq
      simpa only [eventCount_eq_instructionCount, offset] using count
    have position : instructionCount setup.program -
        ProtocolState.remaining setup.program cursor.current.point = low := by
      rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
      change instructionCount setup.program -
        instructionCount (block.block.prepend block.suffix) = low
      omega
    have committing : ProtocolState.atCommit setup.program cursor.current.point = true := by
      rw [cursor.point, cursor.origin.atCommit_lift]
      have entryCommit : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
          (segment : SourceProgram.CommitPrefix Γ O Δ P)
          (tail : SourceProgram Player L Δ P) (entry : SourceProgram.Config Player L Γ),
          0 < segment.length → ProtocolState.atCommit (segment.prepend tail)
            (ProtocolState.entry (segment.prepend tail) entry) = true := by
        intro Γ Δ O P segment
        cases segment with
        | nil => intro tail entry impossible; cases Nat.not_lt_zero _ impossible
        | commit => intro tail entry _; rfl
      exact entryCommit block.block block.suffix cursor.source nonempty
    have address := cursor.controls nonempty
    have generation : cursor.current.generation =
        control.execution.application.attempt.generation := congrArg (fun signal => signal.2.1)
          address
    have saved : instructionCount setup.program -
        ProtocolState.remaining setup.program cursor.current.saved =
          control.execution.application.attempt.phase := congrArg (fun signal => signal.2.2)
            address
    have within : (cursor.embedding.event index).val < instructionCount setup.program -
        ProtocolState.commitEnd setup.program cursor.current.saved := by
      rw [cursor.savedEnd nonempty]
      have endRank : instructionCount setup.program - instructionCount block.suffix =
          low + block.block.length := by
        rw [block.block.instructionCount_prepend] at clock
        omega
      rw [endRank, rank]
      exact Nat.add_lt_add_left inside low
    have retained : TracePrefix target.trace finished.trace :=
      (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary k target cut
        first).tracePrefix.trans
          (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary
            (block.block.length - k) cut finished last).tracePrefix
    have sourceRead := sourceBindingAt_of_issued_attempt setup implementation block.block
      block.suffix cursor.embedding cursor.source cursor.current.excluded result
        lastState.excluded attempt excluded owner active index inside ty binding selected control
        trace
          low high (ledger owner) message emitted currentAttempt handle call rank
            (by dsimp only [high]; omega) value cursor.current cursor.trace committing finished
              (by cases targetEq; exact retained)
                (by cases finishedEq; exact rows)
                control.execution.application.attempt generation saved (by omega) within
    have nativeInput := (nativeApplication).history_inputRecall nativeInitial
      implementation.horizon implementation.scheduler
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler trace) owner
    have member : message ∈ control.execution.network.inputs := by
      rw [← nativeInput] at emitted
      exact (List.mem_filter.mp emitted).1
    obtain ⟨_serial, _opening, _evidence, record, handleEq, _sender, recorded, sent,
        _action, _fresh, _namespace, _value⟩ :=
      issued_binding_record setup implementation control trace owner (cursor.embedding.event index)
        ty binding handle message member call
    have recalled : record ∈ control.execution.recall handle.1 := by
      simpa only [handleEq] using recorded
    refine ⟨sourceRead, ?_⟩
    have atMessage : sourceBindingAt setup message.payload.attempt (cursor.embedding.event index)
        owner ty binding finished.trace =
          PublicationResult.equivOption selected := by
      simpa only [currentAttempt] using sourceRead
    have meaning := sourceHandleMeaning_of_emission setup implementation finished control trace
      handle
      record recalled message sent (cursor.embedding.event index) call owner ty binding
        (PublicationResult.equivOption selected) atMessage
    cases selected <;> exact meaning

open Classical in
/-- The canonical source completion retains the entire actual issued ledger.
Its original chosen graph key extends the same physical emitted frontier. -/
private theorem canonical_source_issued_observation
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event) :
    let cut := entry.canonicalCut setup values implementation operational fullValues control trace
      who active event payload clean foreign
    match cut.completed.state.bind (fun current => residualEntry? entry.suffix
      (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point))
        current.point) with
    | none => False
    | some finished => ∀ owner, issuedLedger setup implementation entry.block
        control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + entry.block.length) owner
          (finished.view owner) := by
  classical
  intro cut
  obtain ⟨finished, last, lastTrace, attempt, historyEq, point, excluded, _generation,
      _live, agreement, _word, _labels⟩ := cut.blockResult
  change cut.completed = ⟨some last, lastTrace⟩ at historyEq
  have pulled : residualEntry? entry.suffix
      (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point)) last.point =
        some finished :=
    (residualEntry?_eq_some_iff (entry.cursor.origin.compose
      (entry.block.protocolSuffix entry.suffix)) last.point finished).mpr point.symm
  rw [historyEq, Option.bind_some, pulled]
  have saved := clean.excluded_eq setup implementation control
    (checkpointSelection setup implementation operational trace).val entry.phase entry.installed
  have entryExcluded : entry.cursor.current.excluded =
      control.execution.application.entry.excluded :=
    entry.cursor.excluded.trans (entry.excluded.symm.trans saved)
  have phaseLow : entry.phase.low = control.execution.application.attempt.phase := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons,
      Option.map_some, Option.getD_some]
  have phaseHigh : entry.phase.high =
      control.execution.application.attempt.phase + entry.block.length := by
    have bounds := entry.phase.nonempty
    have size := entry.size
    omega
  let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
    implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
      entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
        implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler trace)
  have retained : ∀ field value, frontier.store field = some value →
      cut.key.2.1 field = some value := by
    exact (Classical.choose_spec (Classical.choose_spec
      (entry.supported_completion setup values implementation operational fullValues control trace
        who event payload clean foreign))).2.2.2
  have frame := entry.callback_frame setup implementation operational control trace who event
  change entry.block.Attempt entry.cursor.source entry.cursor.current.excluded
    finished last.excluded at attempt
  change last.excluded = entry.cursor.current.excluded at excluded
  rw [entryExcluded] at attempt excluded
  apply (issuedLedger_iff_emitted_bindings setup implementation entry.block entry.suffix
    entry.cursor.embedding entry.cursor.refs control.execution.application.attempt.phase
      (fun index => (entry.cursor.compiled.rankEq index).trans (by rw [entry.offset, phaseLow]))
      entry.cursor.views.actionEq control trace entry.phase phaseLow phaseHigh cut.key.2.1
        entry.cursor.source finished last.excluded attempt excluded agreement).mpr
  intro message member current named inside candidate call owner domain binding
  have emitted := frame.emissions message member current named inside candidate call owner domain
    binding
  exact FieldRef.get?_preserved _ frontier.store cut.key.2.1 retained _ emitted

omit [Fintype Player] in
/-- At genuine saved entries, equal full focal entry information and equal
focal labeled coordinates determine full information at equally long ordinary
interior commitment prefixes. The public chronology and archive are derived
from the actual source intervals. -/
private theorem commit_window_information_of_coordinate
    (who : Player) (first second : ProtocolState setup.program)
    (excluded : Finset Player) (generation : Nat)
    (leftPrior : setup.proposalRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint first excluded generation)))
    (rightPrior : setup.proposalRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint second excluded generation)))
    (entryInformation : setup.proposalRecoveryModel.infoOf who leftPrior =
      setup.proposalRecoveryModel.infoOf who rightPrior)
    (committing : ProtocolState.atCommit setup.program first = true)
    (alive : who ∉ excluded)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix leftPrior left) (rightRetained : TracePrefix rightPrior right)
    (leftInside : left.length + ProtocolState.commitEnd setup.program first <
      leftPrior.length + ProtocolState.remaining setup.program first)
    (rightInside : right.length + ProtocolState.commitEnd setup.program second <
      rightPrior.length + ProtocolState.remaining setup.program second)
    (depth : left.length - leftPrior.length = right.length - rightPrior.length)
    (leftExcluded : (setup.commitRecoveryPublic leftState).1 = excluded)
    (rightExcluded : (setup.commitRecoveryPublic rightState).1 = excluded)
    (coordinate : (setup.proposalRecoveryJointRecall left).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right).map (fun joint => joint who)) :
    setup.proposalRecoveryModel.infoOf who left = setup.proposalRecoveryModel.infoOf who right := by
  have privateLeft : (setup.proposalRecoveryModel.infoOf who leftPrior).1.1.1 =
      some (ProtocolState.observe who setup.program first) := by
    change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who leftPrior).1.1.1 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.fst (setup.proposalRecoverySignals_control who leftPrior)
  have privateRight : (setup.proposalRecoveryModel.infoOf who rightPrior).1.1.1 =
      some (ProtocolState.observe who setup.program second) := by
    change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who rightPrior).1.1.1 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.fst (setup.proposalRecoverySignals_control who rightPrior)
  have entryView : ProtocolState.observe who setup.program first =
      ProtocolState.observe who setup.program second :=
    Option.some.inj (privateLeft.symm.trans
      ((congrArg (fun information => information.1.1.1) entryInformation).trans privateRight))
  have secondCommitting : ProtocolState.atCommit setup.program second = true := by
    rw [← ProtocolState.atCommit_observe setup.program second who, ← entryView,
      ProtocolState.atCommit_observe, committing]
  have remaining : ProtocolState.remaining setup.program first =
      ProtocolState.remaining setup.program second := by
    have firstRank := ProtocolView.position_add_remaining who setup.program first
    have secondRank := ProtocolView.position_add_remaining who setup.program second
    rw [entryView] at firstRank
    omega
  have clock : leftPrior.length = rightPrior.length := by
    have lengths := congrArg (fun information => information.1.2.length) entryInformation
    change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who leftPrior).1.2.length =
      (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who rightPrior).1.2.length at lengths
    rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at lengths
    simpa only [setup.source_signal_depth] using lengths
  have semanticEntry := congrArg (setup.proposalRecoveryEraseInfo who) entryInformation
  rw [setup.proposalRecoveryEraseInfo_observed, setup.proposalRecoveryEraseInfo_observed]
    at semanticEntry
  have rootPublic := setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq who
    (setup.proposalRecoveryEraseTrace leftPrior) (setup.proposalRecoveryEraseTrace rightPrior)
      (congrArg (setup.commitRecoveryErasedInformation who) semanticEntry)
  have rootNumeric := congrArg (List.map (setup.commitRecoveryPublicAddress who)) rootPublic
  rw [setup.commitRecovery_publicRecall_addresses,
    setup.commitRecovery_publicRecall_addresses] at rootNumeric
  have rootWord := List.reverse_injective (List.append_cancel_right rootNumeric)
  have leftAddresses := source_binding_prefix_addresses setup who first excluded generation
    (setup.proposalRecoveryEraseTrace leftPrior) committing alive
      (setup.proposalRecoveryEraseTrace left)
      (setup.proposalRecoveryEraseTrace_prefix leftRetained)
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using leftInside) leftExcluded
  have rightAddresses := source_binding_prefix_addresses setup who second excluded generation
    (setup.proposalRecoveryEraseTrace rightPrior) secondCommitting alive
      (setup.proposalRecoveryEraseTrace right)
      (setup.proposalRecoveryEraseTrace_prefix rightRetained)
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using rightInside) rightExcluded
  have addresses : setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace left) =
      setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace right) := by
    rw [leftAddresses, rightAddresses]
    simp only [setup.proposalRecoveryEraseTrace_length]
    rw [rootWord, remaining, depth]
  have leftSurvives : who ∉ (setup.commitRecoveryPublic leftState).1 := by
    rw [leftExcluded]
    exact alive
  have rightSurvives : who ∉ (setup.commitRecoveryPublic rightState).1 := by
    rw [rightExcluded]
    exact alive
  obtain ⟨leftCurrent, _leftReplay, leftStateEq, leftSaved, _leftEntry, _leftGeneration,
      _leftRest⟩ := setup.commitRecovery_noMiss_prefix_information who first excluded generation
    (setup.proposalRecoveryEraseTrace leftPrior) committing
      (setup.proposalRecoveryEraseTrace left)
      (setup.proposalRecoveryEraseTrace_prefix leftRetained)
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using leftInside) leftSurvives
  obtain ⟨rightCurrent, _rightReplay, rightStateEq, rightSaved, _rightEntry, _rightGeneration,
      _rightRest⟩ := setup.commitRecovery_noMiss_prefix_information who second excluded generation
    (setup.proposalRecoveryEraseTrace rightPrior) secondCommitting
      (setup.proposalRecoveryEraseTrace right)
      (setup.proposalRecoveryEraseTrace_prefix rightRetained)
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using rightInside) rightSurvives
  subst leftState
  subst rightState
  have leftExpansion := setup.commitRecovery_public_expansion who
    (setup.proposalRecoveryEraseTrace left)
  have rightExpansion := setup.commitRecovery_public_expansion who
    (setup.proposalRecoveryEraseTrace right)
  change leftCurrent.PublicExpansion who at leftExpansion
  change rightCurrent.PublicExpansion who at rightExpansion
  unfold CommitRecoveryState.PublicExpansion at leftExpansion rightExpansion
  rw [leftSaved] at leftExpansion
  rw [rightSaved] at rightExpansion
  have automatic := ProtocolState.automaticCommitBlock_observe_congr who setup.program
    first second entryView
  have publicImage := leftExpansion.symm.trans
    ((congrArg (ProtocolView.publicOnly who setup.program) automatic).trans rightExpansion)
  have numeric : (setup.attemptPublicRecall who
      (setup.proposalRecoveryEraseTrace left)).map (setup.commitRecoveryPublicAddress who) =
      (setup.attemptPublicRecall who
        (setup.proposalRecoveryEraseTrace right)).map (setup.commitRecoveryPublicAddress who) := by
    rw [setup.commitRecovery_publicRecall_addresses,
      setup.commitRecovery_publicRecall_addresses, addresses]
  have semanticPublic := setup.commitRecovery_publicRecall_eq_of_numeric who
    leftCurrent rightCurrent (setup.proposalRecoveryEraseTrace left)
      (setup.proposalRecoveryEraseTrace right) leftSurvives rightSurvives publicImage numeric
  have leftArchive := setup.proposalRecoveryArchive_eq_of_commit_window who
    (CommitRecoveryState.atPoint first excluded generation) leftPrior committing left
      leftRetained leftInside.le
  have rightArchive := setup.proposalRecoveryArchive_eq_of_commit_window who
    (CommitRecoveryState.atPoint second excluded generation) rightPrior secondCommitting right
      rightRetained rightInside.le
  have archive := leftArchive.trans
    ((congrArg (setup.proposalRecoveryArchive who) entryInformation).trans rightArchive.symm)
  have publicWord := setup.proposalRecoveryPublicRecall_eq_of_semantic_archive who left right
    semanticPublic archive
  exact setup.proposalRecovery_info_eq_of_observed_prefixes who
    (CommitRecoveryState.atPoint first excluded generation)
    (CommitRecoveryState.atPoint second excluded generation) leftPrior rightPrior clock
      (by simp only [CommitRecoveryState.atPoint, entryView]) entryInformation left right
        leftRetained rightRetained publicWord coordinate

open Classical in
/-- Positivity of an original annotation places both source coordinates in
the same ordinary maximal commitment interval. Goodness propagates through
that actual interval, and the retained cut has its literal static depth. -/
theorem positive_original_annotated_geometry
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    setup.proposalRecoveryForeignGood who target ∧
      setup.proposalRecoveryForeignGood who cut ∧
      setup.proposalRecoveryForeignGood who finished ∧
      cut.trace.length = target.trace.length +
        (event.val - control.execution.application.attempt.phase) ∧
      finished.trace.length = target.trace.length + block.block.length := by
  classical
  intro checkpoint block
  let low := control.execution.application.attempt.phase
  let k := event.val - low
  let ordinary := sourceUnflaggedStrategy setup values
  have information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  obtain ⟨entry, current, targetTrace, targetEq, targetGood, erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target word canonicalSupported prefixPositive
        event payload clean
  subst target
  obtain ⟨baseCursor, canonical, _offset, _source, _refs, _embedding, _lift, _views,
      _config, size⟩ := selected_binding_cursor setup implementation operational who control
        trace event entry true
  let cursor := PhaseProposalOrdinarySourceCursor.of_erasedHistory setup .concurrent
    implementation.runtime implementation.leaks implementation.plan control entry.phase
      block.block block.suffix baseCursor current targetTrace
        ((congrArg setup.proposalRecoveryErasedHistory canonical).trans
          ((congrArg setup.proposalRecoveryErasedHistory entry.canonicalHistory).symm.trans erased))
  have phaseLow : entry.phase.low = low := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [low, PhaseRuntimeState.attempt, phases, List.head?_cons,
      Option.map_some, Option.getD_some]
  have inside : k < block.block.length := by
    have bounds := (entry.phase.mem_events event).mp entry.inside
    change block.block.length = entry.phase.high - entry.phase.low at size
    dsimp only [k]
    omega
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape ⟨some current, targetTrace⟩ cut finished
      word canonicalSupported (control.execution.recall who)
        (control.execution.observe nativeApplication who) information event payload clean value
          positive
  have supported := pair.2.2.1
  obtain ⟨g, first, rest⟩ := (PMF.mem_support_bind_iff ..).mp supported
  obtain ⟨G, last, same⟩ := (PMF.mem_support_map_iff ..).mp rest
  have cutEq : g = cut := congrArg Prod.fst same
  have finishedEq : G = finished := congrArg Prod.snd same
  subst g
  subst G
  have completedSupport : finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom ordinary
      block.block.length ⟨some current, targetTrace⟩).support := by
    have joined : finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom ordinary
        (k + (block.block.length - k)) ⟨some current, targetTrace⟩).support := by
      rw [setup.proposalRecoveryModel.runBehavioralFrom_add]
      exact (PMF.mem_support_bind_iff ..).mpr ⟨cut, first, last⟩
    simpa only [Nat.add_sub_of_le inside.le] using joined
  have good := ordinary_source_supported_good setup values implementation who control entry.phase
    block.block block.suffix cursor targetGood finished completedSupport
  obtain ⟨middleContext, middleNames, before, after, beforeLength, afterLength, split⟩ :=
    block.block.exists_split k inside.le
  let startOf (segment : SourceProgram.CommitPrefix checkpoint.residual.context
      checkpoint.residual.names block.context block.pending)
      (c : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control entry.phase segment block.suffix) :
      setup.proposalRecoveryProtocol.History := ⟨some c.current, c.trace⟩
  have castStart {α : Type} {β : α → Type} (f : (x : α) → β x →
      setup.proposalRecoveryProtocol.History) {x y : α} (same : x = y) (item : β x) :
      f y (same ▸ item) = f x item := by
    cases same
    rfl
  let cutCursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan control entry.phase (before.append after)
        block.suffix := split.symm ▸ cursor
  have cutStart : (⟨some cutCursor.current, cutCursor.trace⟩ :
      setup.proposalRecoveryProtocol.History) = ⟨some current, targetTrace⟩ :=
    castStart startOf split.symm cursor
  have cutClock : cutCursor.trace.length = targetTrace.length :=
    congrArg (fun h : setup.proposalRecoveryProtocol.History => h.trace.length) cutStart
  have geometry := ordinary_source_pair_geometry setup values implementation control entry.phase
    before after block.suffix cutCursor
  rw [cutStart, beforeLength] at geometry
  have afterEq : block.block.length - k = after.length := by omega
  have originalPair : (cut, finished) ∈ ((setup.proposalRecoveryModel.runBehavioralFrom ordinary
      k ⟨some current, targetTrace⟩).bind fun g =>
        (setup.proposalRecoveryModel.runBehavioralFrom ordinary after.length g).map
          (Prod.mk g)).support :=
    (PMF.mem_support_bind_iff ..).mpr
      ⟨cut, first, (PMF.mem_support_map_iff ..).mpr
        ⟨finished, by
          change finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom ordinary
            (block.block.length - k) cut).support at last
          simpa only [afterEq] using last, rfl⟩⟩
  have cutGeometry := geometry (cut, finished) originalPair
  refine ⟨targetGood, source_good_prefix setup who cut.trace finished.trace cutGeometry.1 good.1,
    good.1, ?_, good.2⟩
  simpa only [cutClock, k, low] using cutGeometry.2

open Classical in
/-- Every addressed historical binding read survives the positive annotation's
closed entry fiber and its actual ordinary continuation, including canceled values. -/
private theorem positive_original_annotated_historical_read
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    ∀ (coordinate : CommitAttemptId) (owner : Player)
      (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
      (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
      (raw : L.Val ty),
      sourceBindingAt setup coordinate named owner ty binding
        (canonicalSource setup implementation operational ⟨some control, trace⟩).trace =
          some raw →
      sourceBindingAt setup coordinate named owner ty binding finished.trace = some raw := by
  classical
  intro coordinate owner named ty binding raw originalRead
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  obtain ⟨entry, current, targetTrace, targetEq, targetGood, _erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target word canonicalSupported prefixPositive
        event payload clean
  subst target
  have annotation := annotatedPrefixWeight_support setup values implementation operational
    sourceProfile nativeProfile who ⟨some control, trace⟩ tape ⟨some current, targetTrace⟩ word
      canonicalSupported
      prefixPositive
  have sameKey : setup.proposalRecoveryClosedKey who
      ⟨some entry.cursor.current, entry.cursor.trace⟩ =
        setup.proposalRecoveryClosedKey who ⟨some current, targetTrace⟩ := by
    exact (congrArg (setup.proposalRecoveryClosedKey who) entry.canonicalHistory).trans
      annotation.1.symm
  have entryGood : setup.proposalRecoveryForeignGood who
      ⟨some entry.cursor.current, entry.cursor.trace⟩ := by
    have bit := congrArg (fun key => key.2.2.2) sameKey
    simpa only [Setup.proposalRecoveryClosedKey, targetGood, decide_true,
      decide_eq_true_eq] using bit
  have entryRead : sourceBindingAt setup coordinate named owner ty binding entry.cursor.trace =
      some raw := by
    rw [← entry.canonicalHistory] at originalRead
    exact originalRead
  have targetRead : sourceBindingAt setup coordinate named owner ty binding targetTrace =
      some raw := by
    rw [← sourceBindingAt_closed_key setup operational.wellFormed who owner coordinate named
      ty binding entry.cursor.current current entry.cursor.trace targetTrace sameKey
        entryGood targetGood]
    exact entryRead
  have information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape ⟨some current, targetTrace⟩ cut finished word
      canonicalSupported
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        information event payload clean value positive
  obtain ⟨source, preceding, choices, offered, next, reached, kept, generation, saved,
      position, data⟩ := sourceBindingAt_origin setup coordinate named owner ty binding
        targetTrace raw targetRead
  have onward : TracePrefix targetTrace finished.trace := by
    have retained := pair.2.2.2.2.1.trans pair.2.2.2.2.2.1
    exact retained
  exact sourceBindingAt_of_origin setup coordinate named owner ty binding source preceding
    choices offered next reached generation saved position (.success raw, false) data
      finished.trace (kept.trans onward)

open Classical in
/-- A current signed callback reads its original complete publication result
from the positive annotation's issued ledger, including failure and pending packets. -/
private theorem positive_original_annotated_current_result
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (owner : Player) (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : record.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle)
    (current : message.payload.attempt = control.execution.application.attempt) :
    sourceBindingAt setup control.execution.application.attempt named owner ty binding
        finished.trace =
      PublicationResult.equivOption
        (control.execution.application.current.native.bindingResult handle ty) ∧
    sourceHandleMeaning setup implementation finished control handle =
      (PublicationResult.equivOption
        (control.execution.application.current.native.bindingResult handle ty)).map
          (fun raw => (⟨ty, raw⟩ : Raw L)) := by
  classical
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  obtain ⟨entry, _current, _targetTrace, _targetEq, _targetGood, _erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target word canonicalSupported prefixPositive
        event payload clean
  let startLaw := ((setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan))
  let actualTrace := sourceCutTrace setup implementation trace
  have rawTrace := (nativeMenu).toRawTrace startLaw implementation.horizon
    implementation.scheduler actualTrace
  obtain ⟨actualMessage, sent, _sender, packet⟩ := PhaseCount.recalled_submission_emitted
    implementation.runtime implementation.leaks startLaw implementation.horizon
      implementation.scheduler rawTrace owner record recorded material transmitted
  have messageEq : actualMessage = message := Option.some.inj (sent.symm.trans emitted)
  subst actualMessage
  obtain ⟨callback, callbackTrace, callbackKept, _acting, viewed, request⟩ :=
    phase_recorded_binding_request implementation.runtime implementation.leaks
      implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon (serviceGraph_revealRelaxedOrdered setup .concurrent)
        implementation.scheduler actualTrace owner record recorded material transmitted named
          handle (packet.symm.trans call)
  have emittedNamespace := phase_recalled_emission_attempt implementation.runtime
    implementation.leaks startLaw implementation.horizon implementation.scheduler rawTrace
      owner record recorded message emitted
  rw [viewed] at emittedNamespace
  change message.payload.attempt = callback.execution.application.attempt at emittedNamespace
  have sameAttempt : callback.execution.application.attempt =
      control.execution.application.attempt := emittedNamespace.symm.trans current
  have orderedInitial : ∀ state ∈ startLaw.support, state.Ordered := by
    intro state member
    obtain ⟨draw, _member, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered implementation.plan draw
  have ordered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history startLaw implementation.horizon implementation.scheduler
      orderedInitial ((nativeMenu).toRawTrace startLaw implementation.horizon
        implementation.scheduler callbackTrace)
  have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
    nativeMenu startLaw orderedInitial implementation.horizon implementation.scheduler callback
      control callbackTrace actualTrace callbackKept ordered sameAttempt
  obtain ⟨issuedPhase, installed, inside⟩ := request.2.1
  have phaseEq : issuedPhase = entry.phase := by
    apply Option.some.inj
    exact (Option.mem_def.mp installed).symm.trans
      ((congrArg (fun phases => phases.head?) (congrArg Prod.fst metadata)).trans entry.installed)
  have namedInside : named ∈ entry.phase.events := phaseEq ▸ inside
  have information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational
    fullValues sourceProfile nativeProfile who control trace tape target cut finished word
      canonicalSupported (control.execution.recall who)
        (control.execution.observe nativeApplication who) information event payload clean value
          positive
  obtain ⟨_read, _word, _unique, phase, cursor, result, last, lastTrace, attempt, targetEq,
      _lift, _finished, _history, _rows, _labels, _point, _excluded, _ledger, offset,
      currentValue⟩ := pair.2.2.2.2.2.2
  obtain ⟨_baseCursor, _canonical, _offset, _source, _refs, _embedding, _lift, _views,
      _config, size⟩ := selected_binding_cursor setup implementation operational who control
        trace event entry true
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  let block := SourceProgram.commitPhase checkpoint.residual.tail
  have low : entry.phase.low = control.execution.application.attempt.phase := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have bounds := (entry.phase.mem_events named).mp namedInside
  have indexBound : named.val - control.execution.application.attempt.phase <
      block.block.length := by
    change block.block.length = entry.phase.high - entry.phase.low at size
    omega
  let index : Fin (eventCount (block.block.prepend block.suffix)) :=
    ⟨named.val - control.execution.application.attempt.phase, by
      have count := block.block.eventCount_prepend block.suffix
      omega⟩
  have namedEq : cursor.embedding.event index = named := by
    apply Fin.ext
    have lower : control.execution.application.attempt.phase ≤ named.val := by
      rw [← low]
      exact bounds.1
    calc
      (cursor.embedding.event index).val = cursor.offset + index.val :=
        cursor.compiled.rankEq index
      _ = control.execution.application.attempt.phase + index.val :=
        congrArg (fun start => start + index.val) offset
      _ = named.val := Nat.add_sub_of_le lower
  have nativeInput := (nativeApplication).history_inputRecall nativeInitial
    implementation.horizon implementation.scheduler
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace) owner
  have emittedMember : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
  have member : message ∈ control.execution.network.inputs := by
    rw [← nativeInput] at emittedMember
    exact (List.mem_filter.mp emittedMember).1
  have ownerActive := issued_binding_owner_active setup implementation control trace owner named
    ty binding handle message member current call
  have cleanMask := clean.excluded_eq setup implementation control
    (checkpointSelection setup implementation operational trace).val entry.phase entry.installed
  have sourceActive : owner ∉ cursor.current.excluded := by
    rw [cursor.excluded, cleanMask]
    exact ownerActive
  simpa only [namedEq] using
    (currentValue owner sourceActive index indexBound ty
      (by simpa only [namedEq] using binding)
      (control.execution.application.current.native.bindingResult handle ty)
      message emittedMember current handle (by simpa only [namedEq] using call) rfl)

open Classical in
/-- An actually admitted handle retains its original typed value at the positive
source completion, through either its historical origin or the current issued ledger. -/
private theorem positive_original_annotated_admitted_value
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before)) (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (owner : Player) (ty : L.Ty) (named : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (handle : Handle (serviceGraph setup .concurrent)) (old : L.Val ty)
    (accepted : snapshot.accepted (.inr named) = some handle)
    (stored : (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner ty)).get? snapshot.config.store = some (.success old)) :
    ∃ (record : (nativeApplication).PlayerEntry)
      (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
      handle.1 = owner ∧ record ∈ control.execution.recall owner ∧
      record.emitted = some message ∧ message.payload.packet.call = .commitment named handle ∧
      control.execution.application.current.native.bindingResult handle ty = .success old ∧
      sourceHandleMeaning setup implementation finished control handle =
        some (⟨ty, old⟩ : Raw L) := by
  classical
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  obtain ⟨entry, _current, _targetTrace, _targetEq, _targetGood, _erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target word canonicalSupported prefixPositive
        event payload clean
  have foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at prefixPositive
    dsimp only at prefixPositive
    have selected := (mul_ne_zero_iff.mp prefixPositive).2
    split at selected
    · rename_i qualified
      exact qualified.1
    · simp only [ne_eq, not_true_eq_false] at selected
  let chosen := entry.canonicalCut setup values implementation operational fullValues control trace
    who active event payload clean foreign
  have initialEq : nativeInitial = ((setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan)) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have retainedCut : TracePrefix (sourceCutTrace setup implementation prior)
      (sourceCutTrace setup implementation trace) :=
    tracePrefix_initializer setup implementation initialEq retained
  obtain ⟨valid, preserved⟩ := accepted_snapshot_catalogue setup implementation control trace
    before prior retained snapshot selected owner ty ⟨.inr named, binding⟩ handle accepted
  obtain ⟨candidate, associated, _owned, opened⟩ :=
    valid.success_provenance ⟨.inr named, binding⟩ old stored
  have same : candidate = handle := Option.some.inj (associated.symm.trans accepted)
  subst candidate
  have catalogue := preserved.trans opened
  have oldMeaning : control.execution.application.current.native.bindingResult handle ty =
      .success old := by
    simp [State.bindingResult, catalogue, Raw.as?]
  obtain ⟨record, material, message, source, next, sourcePrior, joint, legal, moved,
      owned, recorded, transmitted, emitted, call, _receipt, _kept, generation, saved,
      position, _sourceActive, _survives, literal, _location, entryLocation⟩ :=
    source_admitted_binding_row setup values implementation operational control
      (sourceCutTrace setup implementation trace) who event chosen before
        (sourceCutTrace setup implementation prior) retainedCut snapshot selected owner ty named
          binding handle accepted
  refine ⟨record, message, owned, recorded, emitted, call, oldMeaning, ?_⟩
  rcases entryLocation with historical | current
  · have data : phaseRecoveryBindingData setup .concurrent named owner ty binding
        ((joint owner).map (·.semantic)) = (.success old, false) := by
      simpa only [oldMeaning] using literal
    have entryRead : sourceBindingAt setup message.payload.attempt named owner ty binding
        chosen.cursor.trace = some old :=
      sourceBindingAt_of_origin setup message.payload.attempt named owner ty binding source
        sourcePrior joint legal (some next) moved generation saved position (.success old, false)
          data chosen.cursor.trace historical
    change sourceBindingAt setup message.payload.attempt named owner ty binding
      entry.cursor.trace = some old at entryRead
    have canonicalRead : sourceBindingAt setup message.payload.attempt named owner ty binding
        (canonicalSource setup implementation operational ⟨some control, trace⟩).trace =
          some old := by
      rw [← entry.canonicalHistory]
      exact entryRead
    have finalRead := positive_original_annotated_historical_read setup values implementation
      operational fullValues sourceProfile nativeProfile who control trace active tape target cut
        finished word canonicalSupported event payload clean value positive message.payload.attempt
          owner named ty binding old canonicalRead
    have recalled : record ∈ control.execution.recall handle.1 := by
      simpa only [owned] using recorded
    exact sourceHandleMeaning_of_emission setup implementation finished control trace handle
      record recalled message emitted named call owner ty binding (some old) finalRead
  · have actual := positive_original_annotated_current_result setup values implementation
      operational fullValues sourceProfile nativeProfile who control trace active tape target cut
        finished word canonicalSupported event payload clean value positive owner record recorded
          material transmitted message emitted named ty binding handle call current
    rw [oldMeaning] at actual
    exact actual.2

open Classical in
/-- A successful addressed read from an earlier attempt already occurs before
the positive annotation's entry. Current ordinary rows cannot create it. -/
private theorem positive_original_annotated_historical_readback
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (coordinate : CommitAttemptId)
    (historical : coordinate ≠ control.execution.application.attempt)
    (owner : Player) (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (raw : L.Val ty)
    (read : sourceBindingAt setup coordinate named owner ty binding finished.trace = some raw) :
    sourceBindingAt setup coordinate named owner ty binding
      (canonicalSource setup implementation operational
        ⟨some control, trace⟩).trace = some raw := by
  classical
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  let block := SourceProgram.commitPhase checkpoint.residual.tail
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  obtain ⟨entry, _targetCurrent, _targetTrace, _targetEq, _targetGood, _erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target word canonicalSupported prefixPositive
        event payload clean
  have geometry := positive_original_annotated_geometry setup values implementation operational
    fullValues sourceProfile nativeProfile who control trace active tape target cut finished word
      canonicalSupported event payload clean value positive
  have information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape target cut finished word canonicalSupported
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        information event payload clean value positive
  obtain ⟨_read, _word, _unique, phase, cursor, result, last, lastTrace, attempt, targetEq,
      _lift, finishedEq, _history, rows, _labels, _point, _excluded, _ledger, offset,
      _currentValue⟩ := pair.2.2.2.2.2.2
  have retained : TracePrefix cursor.trace finished.trace := by
    have retained := pair.2.2.2.2.1.trans pair.2.2.2.2.2.1
    cases targetEq
    exact retained
  obtain ⟨source, sourcePrior, sourceJoint, sourceLegal, next, sourceMoved, sourceKept,
      generation, saved, position, data⟩ :=
    sourceBindingAt_origin setup coordinate named owner ty binding finished.trace raw read
  have length : finished.trace.length = cursor.trace.length + attempt.joints.length := by
    have count := congrArg List.length rows
    simp only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
      List.length_append, List.length_reverse] at count
    rw [finishedEq]
    simpa only [Nat.add_comm] using count
  by_cases earlier : sourcePrior.length + 1 ≤ cursor.trace.length
  · have beforeEntry : TracePrefix (sourcePrior.extend sourceJoint sourceLegal sourceMoved)
        cursor.trace :=
      (sourceKept.reachesWithin.ancestor_comparable retained.reachesWithin earlier).tracePrefix
    have entryRead := sourceBindingAt_of_origin setup coordinate named owner ty binding source
      sourcePrior sourceJoint sourceLegal next sourceMoved generation saved position
        (.success raw, false) data cursor.trace beforeEntry
    have sameKey : setup.proposalRecoveryClosedKey who ⟨some cursor.current, cursor.trace⟩ =
        setup.proposalRecoveryClosedKey who ⟨some entry.cursor.current, entry.cursor.trace⟩ := by
      rw [entry.canonicalHistory, ← targetEq]
      exact pair.1
    have cursorGood : setup.proposalRecoveryForeignGood who
        ⟨some cursor.current, cursor.trace⟩ := by
      cases targetEq
      exact geometry.1
    have entryGood : setup.proposalRecoveryForeignGood who
        ⟨some entry.cursor.current, entry.cursor.trace⟩ := by
      have bit := congrArg (fun key => key.2.2.2) sameKey
      simpa only [Setup.proposalRecoveryClosedKey, cursorGood, decide_true,
        decide_eq_true_eq] using bit.symm
    have transported := sourceBindingAt_closed_key setup operational.wellFormed who owner
      coordinate named ty binding cursor.current entry.cursor.current cursor.trace
      entry.cursor.trace
        sameKey cursorGood entryGood
    rw [← entry.canonicalHistory]
    exact transported.symm.trans entryRead
  · have sourceBefore : TracePrefix sourcePrior finished.trace :=
      (TracePrefix.extend .refl sourceJoint sourceLegal sourceMoved).trans sourceKept
    have originBound := sourceKept.length_le
    simp only [Trace.length] at originBound
    let slot := sourcePrior.length - cursor.trace.length
    have slotBound : slot < attempt.joints.length := by dsimp only [slot]; omega
    have positiveLength : 0 < attempt.joints.length := Nat.zero_lt_of_lt slotBound
    have nonempty : 0 < block.block.length := by
      simpa only [attempt.joints_length] using positiveLength
    have clock : cursor.offset + instructionCount (block.block.prepend block.suffix) =
        instructionCount setup.program := by
      simpa only [eventCount_eq_instructionCount] using cursor.compiled.countEq
    have atRank : instructionCount setup.program -
        ProtocolState.remaining setup.program cursor.current.point = cursor.offset := by
      rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
      change instructionCount setup.program -
        instructionCount (block.block.prepend block.suffix) = cursor.offset
      omega
    have committing : ProtocolState.atCommit setup.program cursor.current.point = true := by
      rw [cursor.point, cursor.origin.atCommit_lift]
      have entryCommit : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
          (segment : SourceProgram.CommitPrefix Γ O Δ P)
          (tail : SourceProgram Player L Δ P) (entry : SourceProgram.Config Player L Γ),
          0 < segment.length → ProtocolState.atCommit (segment.prepend tail)
            (ProtocolState.entry (segment.prepend tail) entry) = true := by
        intro Γ Δ O P segment
        cases segment with
        | nil => intro tail entry impossible; cases Nat.not_lt_zero _ impossible
        | commit => intro tail entry _; rfl
      exact entryCommit _ _ cursor.source nonempty
    have within : cursor.offset + slot < instructionCount setup.program -
        ProtocolState.commitEnd setup.program cursor.current.saved := by
      rw [cursor.savedEnd nonempty]
      change cursor.offset + slot < instructionCount setup.program -
        instructionCount block.suffix
      have endRank : instructionCount setup.program - instructionCount block.suffix =
          cursor.offset + block.block.length := by
        rw [block.block.instructionCount_prepend] at clock
        omega
      have slots : slot < block.block.length := by
        simpa only [attempt.joints_length] using slotBound
      rw [endRank]
      omega
    have instructions : setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace finished.trace) = attempt.joints.reverse ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace cursor.trace) := by
      cases finishedEq
      exact rows
    obtain ⟨actual, after, prior, joint, legal, moved, kept, depth, _word, actualSaved,
        actualGeneration, _position⟩ :=
      source_commit_chunk_at_rank setup cursor.current cursor.trace committing finished retained
        attempt.joints instructions slot slotBound (cursor.offset + slot) (by rw [atRank]) within
    have actualBefore : TracePrefix prior finished.trace :=
      (TracePrefix.extend .refl joint legal moved).trans kept
    have same := actualBefore.eq_of_same_length sourceBefore (by
      rw [depth]
      dsimp only [slot]
      omega)
    have states : actual = source := Option.some.inj (congrArg History.state same)
    have controls := cursor.controls nonempty
    have currentGeneration : cursor.current.generation =
        control.execution.application.attempt.generation :=
      congrArg (fun signal => signal.2.1) controls
    have currentSaved : instructionCount setup.program -
        ProtocolState.remaining setup.program cursor.current.saved =
          control.execution.application.attempt.phase :=
        congrArg (fun signal => signal.2.2) controls
    have phaseEq : coordinate.phase = control.execution.application.attempt.phase := by
      rw [states] at actualSaved
      rw [← saved, actualSaved]
      exact currentSaved
    have generationEq : coordinate.generation =
        control.execution.application.attempt.generation := by
      rw [states] at actualGeneration
      exact generation.symm.trans (actualGeneration.trans currentGeneration)
    exact (historical (congrArg₂ CommitAttemptId.mk phaseEq generationEq)).elim

open Classical in
/-- A meaningful historical signed packet reflects through its literal native
close and decoder to the original immutable catalogue value. -/
private theorem positive_original_annotated_historical_result
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (owner : Player) (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : record.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle)
    (historical : message.payload.attempt ≠ control.execution.application.attempt)
    (raw : L.Val ty)
    (read : sourceBindingAt setup message.payload.attempt named owner ty binding
      finished.trace = some raw) :
    control.execution.application.current.native.bindingResult handle ty = .success raw ∧
      PhaseService.BindingAccepted implementation.runtime implementation.leaks
        ⟨message.payload.attempt, named⟩ owner control.execution := by
  classical
  have canonicalRead := positive_original_annotated_historical_readback setup values implementation
    operational fullValues sourceProfile nativeProfile who control trace active tape target cut
      finished word canonicalSupported event payload clean value positive message.payload.attempt
        historical owner named ty binding raw read
  let startLaw := ((setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan))
  have initialEq : startLaw = nativeInitial := by
    simp only [startLaw, ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  let actualTrace := sourceCutTrace setup implementation trace
  let rawTrace := (nativeMenu).toRawTrace startLaw implementation.horizon
    implementation.scheduler actualTrace
  obtain ⟨actualMessage, sent, sender, packet⟩ := PhaseCount.recalled_submission_emitted
    implementation.runtime implementation.leaks startLaw implementation.horizon
      implementation.scheduler rawTrace owner record recorded material transmitted
  have messageEq : actualMessage = message := Option.some.inj (sent.symm.trans emitted)
  subst actualMessage
  obtain ⟨callback, callbackTrace, callbackKept, _acting, viewed, request⟩ :=
    phase_recorded_binding_request implementation.runtime implementation.leaks implementation.bounds
      implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
        (serviceGraph_revealRelaxedOrdered setup .concurrent) implementation.scheduler actualTrace
          owner record recorded material transmitted named handle (packet.symm.trans call)
  have emittedNamespace := phase_recalled_emission_attempt implementation.runtime
    implementation.leaks startLaw implementation.horizon implementation.scheduler rawTrace owner
      record recorded message emitted
  rw [viewed] at emittedNamespace
  change message.payload.attempt = callback.execution.application.attempt at emittedNamespace
  let nativeCallback : (nativeProtocol).Trace (some callback) := initialEq ▸ callbackTrace
  have nativeKept : TracePrefix nativeCallback trace := by
    have transported := tracePrefix_initializer setup implementation initialEq callbackKept
    have inverse : initialEq ▸ (initialEq.symm ▸ trace) = trace :=
      trace_initializer_inverse setup implementation initialEq trace
    exact inverse ▸ transported
  obtain ⟨phase, remaining, installed, commitment, namedInside⟩ :=
    phase_ready_binding_phase implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
          ((nativeMenu).toRawTrace startLaw implementation.horizon
            implementation.scheduler callbackTrace) owner named ty binding request.2.2.1
  obtain ⟨source, target, exitTrace, joint, legal, moved, callbackToExit, exitToFinal,
      originalNamespace, exited⟩ :=
    attempt_exit_of_prefix setup implementation callback nativeCallback trace nativeKept (by
      intro equal
      have same := Option.some.inj equal
      exact historical (emittedNamespace.trans same.symm))
  obtain ⟨before, sourceEq, beforeNamespace⟩ := Option.map_eq_some_iff.mp originalNamespace
  cases sourceEq
  obtain ⟨after, rfl, _recalled⟩ := (nativeApplication).transition_recall_prefix nativeInitial
    implementation.horizon implementation.scheduler before target joint moved
  have changed : after.execution.application.attempt ≠ before.execution.application.attempt := by
    simpa only [Option.map_some, beforeNamespace, ne_eq, Option.some.injEq] using exited
  let afterTrace := exitTrace.extend joint legal moved
  have orderedInitial : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _member, equal⟩ := PMF.support_map .. ▸ member
    cases equal
    exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
  have callbackOrdered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history nativeInitial implementation.horizon implementation.scheduler
      orderedInitial ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler nativeCallback)
  have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
    nativeMenu nativeInitial orderedInitial implementation.horizon implementation.scheduler
      callback before nativeCallback exitTrace callbackToExit callbackOrdered beforeNamespace.symm
  have phaseBefore : phase ∈ before.execution.application.phases.head? := by
    have phases : callback.execution.application.phases = before.execution.application.phases :=
      congrArg Prod.fst metadata
    rw [← phases]
    simp only [installed, List.head?_cons, Option.mem_def]
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp phaseBefore)
  have sourceMoved : some after ∈
      ((nativeApplication).transition startLaw implementation.horizon implementation.scheduler
        (some before) joint).support := by
    rw [initialEq]
    exact moved
  obtain ⟨current, _idle, normalized, finishedPhase, valid, _coverage, _mask, receipts,
      effect, stamp⟩ :=
    phase_closed_transition_receipt_snapshot implementation.runtime implementation.leaks
      implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
        implementation.scheduler before after
          ((nativeMenu).toRawTrace startLaw implementation.horizon implementation.scheduler
            (sourceCutTrace setup implementation exitTrace))
          joint sourceMoved phase phaseBefore changed
  have beforeAttempt : message.payload.attempt = before.execution.application.attempt :=
    emittedNamespace.trans beforeNamespace.symm
  obtain ⟨last, closed, starting, labeled, fuel, path, instructions, intervalLength,
      startKept, startErase, erased, labeledKept, _closedSelected, _labeledSelected,
      _closedMass⟩ :=
    sourceReplayFactualCommitInterval setup implementation operational before after control
      exitTrace afterTrace trace (by
        change TracePrefix exitTrace (exitTrace.extend joint legal moved)
        exact TracePrefix.extend («E» := nativeProtocol) (prefixTrace := exitTrace)
          (prior := exitTrace) .refl joint legal moved) exitToFinal
        phase rest phases current normalized finishedPhase commitment effect changed
  let first := (checkpointSelection setup implementation operational exitTrace).val.checkpoint
  let startPoint := first.residual.lift
    (ProtocolState.entry first.residual.tail first.source)
  let start := CommitRecoveryState.atPoint startPoint before.execution.application.entry.excluded
    before.execution.application.generation
  let original := canonicalSource setup implementation operational ⟨some control, trace⟩
  have geometry := source_checkpoint_binding_interval setup implementation
    (checkpointSelection setup implementation operational exitTrace).val operational.maximalPhases
      phase rest phases commitment
  have startLow : instructionCount setup.program -
      ProtocolState.remaining setup.program startPoint = phase.low := geometry.2.1
  have startHigh : instructionCount setup.program -
      ProtocolState.commitEnd setup.program startPoint = phase.high := geometry.2.2
  have phaseLow : phase.low = before.execution.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have bounds := (phase.mem_events named).mp namedInside
  have length : (first.commitInstructionWord (phase.drain current).native).length =
      phase.high - phase.low := by
    rw [source_commit_instruction_word_length]
    change ProtocolState.remaining setup.program startPoint -
      ProtocolState.commitEnd setup.program startPoint = phase.high - phase.low
    have bound := ProtocolState.remaining_le_instructionCount setup.program startPoint
    omega
  have instructionRows : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace labeled) =
      (first.commitInstructionWord (phase.drain current).native).reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace starting) := by
    rw [erased, startErase]
    exact instructions
  obtain ⟨rowBefore, rowAfter, row, rowJoint, rowLegal, rowMoved, rowKept, rowDepth,
      _rowWord, rowSaved, rowGeneration, rowPosition⟩ :=
    source_commit_chunk_at_rank setup start starting geometry.1 ⟨some last, labeled⟩ startKept
      (first.commitInstructionWord (phase.drain current).native) instructionRows
        (named.val - phase.low)
        (by rw [length]; omega) named.val
          (by simpa only [start, CommitRecoveryState.atPoint, startLow]
            using (Nat.add_sub_of_le bounds.1).symm)
          (by simpa only [start, CommitRecoveryState.atPoint, startHigh] using bounds.2)
  have kept : TracePrefix (row.extend rowJoint rowLegal rowMoved) original.trace :=
    rowKept.trans labeledKept
  have generationAt : rowBefore.generation = message.payload.attempt.generation := by
    rw [rowGeneration]
    change before.execution.application.generation = message.payload.attempt.generation
    exact congrArg CommitAttemptId.generation beforeAttempt.symm
  have savedAt : instructionCount setup.program -
      ProtocolState.remaining setup.program rowBefore.saved = message.payload.attempt.phase := by
    rw [rowSaved]
    change instructionCount setup.program - ProtocolState.remaining setup.program startPoint =
      message.payload.attempt.phase
    rw [first.saved_position]
    exact congrArg CommitAttemptId.phase beforeAttempt.symm
  let rowData := phaseRecoveryBindingData setup .concurrent named owner ty binding
    ((rowJoint owner).map (·.semantic))
  have reads (result : PublicationResult (L.Val ty) × Bool) (literal : rowData = result) :
      sourceBindingAt setup message.payload.attempt named owner ty binding original.trace =
        (match result with
        | (.success value, false) => some value
        | _ => none) := by
    have actual := sourceBindingAt_of_origin setup message.payload.attempt named owner ty binding
      rowBefore row rowJoint rowLegal (some rowAfter) rowMoved generationAt savedAt rowPosition
        result literal original.trace kept
    rcases result with ⟨publication, missing⟩
    cases publication <;> cases missing <;> exact actual
  have dataEq : rowData = (.success raw, false) := by
    rcases observed : rowData with ⟨publication, missing⟩
    have observedRead := (reads (publication, missing) observed).symm.trans canonicalRead
    cases publication with
    | failure => cases missing <;> cases observedRead
    | success value =>
      cases missing with
      | false =>
        have same : value = raw := Option.some.inj observedRead
        cases same
        rfl
      | true => cases observedRead
  have rowActive : owner ∉ rowBefore.excluded := by
    cases chosen : rowJoint owner with
    | none => simp [rowData, chosen, phaseRecoveryBindingData] at dataEq
    | some move =>
      have offered := rowLegal.2 owner
      rw [chosen] at offered
      exact offered.1.2
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  have foreign : ∀ actor, actor ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler actor ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at prefixPositive
    dsimp only at prefixPositive
    have selected := (mul_ne_zero_iff.mp prefixPositive).2
    split at selected
    · rename_i qualified
      exact qualified.1
    · simp only [ne_eq, not_true_eq_false] at selected
  have good : setup.proposalRecoveryForeignGood who original :=
    canonicalSource_foreignGood setup implementation operational who ⟨some control, trace⟩ foreign
  have closedKept : TracePrefix closed
      (setup.proposalRecoveryEraseTrace original.trace) := by
    have semantic := setup.proposalRecoveryEraseTrace_prefix labeledKept
    rw [erased] at semantic
    exact semantic
  have startLength := congrArg (fun path => path.length) startErase
  have endLength := congrArg (fun path => path.length) erased
  simp only [setup.proposalRecoveryEraseTrace_length] at startLength endLength
  change starting.length = first.trace.length at startLength
  change labeled.length = closed.length at endLength
  change labeled.length = starting.length +
    (first.commitInstructionWord (phase.drain current).native).length at intervalLength
  rw [startLength] at rowDepth
  obtain ⟨sourceBefore, sourceAfter, sourcePrior, sourceJoint, sourceLegal, sourceMoved,
      sourceKept, _depth, beforeInfo, _afterInfo, _own, sourceSaved, sourceGeneration, rawPhysical,
      transported, _successful, _failed⟩ :=
    sourceReplayPhysicalPairedRow setup first (phase.drain current).native ⟨some last, closed⟩
      path instructions who original original closedKept rfl good good rowBefore rowAfter row
        rowJoint rowLegal rowMoved kept named owner ty binding rowPosition.symm
          (by omega)
          (by change row.length < closed.length; omega)
  have rowMetadata := source_information_metadata setup who ⟨some sourceBefore, sourcePrior⟩
    ⟨some rowBefore, row⟩ beforeInfo
  have sourceActive : owner ∉ sourceBefore.excluded := by
    rw [rowMetadata.2.2.1]
    exact rowActive
  have physical := transported sourceActive
  change rowData = _ at physical
  rw [dataEq] at physical
  cases accepted : (phase.drain current).native.accepted (.inr named) with
  | none => simp [accepted] at physical
  | some candidate =>
    have candidateOwner : candidate.1 = owner := by
      obtain ⟨_ty, typed⟩ := valid.accepted_typed (.inr named) candidate accepted
      exact (EventField.binding.inj (typed.symm.trans binding)).1
    have result : (phase.drain current).native.bindingResult candidate ty = .success raw := by
      have literal := rawPhysical sourceActive
      simp only [accepted, Option.elim_some, Option.isNone_some] at literal
      have sourcePosition : instructionCount setup.program -
          ProtocolState.remaining setup.program sourceBefore.point = named.val := by
        rw [(ProtocolState.MetadataEq.controls setup.program sourceBefore.point rowBefore.point
          rowMetadata.1).1]
        exact rowPosition
      have sourceGenerationAt : sourceBefore.generation = message.payload.attempt.generation := by
        change sourceBefore.generation = before.execution.application.generation at sourceGeneration
        exact sourceGeneration.trans
          (congrArg CommitAttemptId.generation beforeAttempt.symm)
      have sourceSavedAt : instructionCount setup.program -
          ProtocolState.remaining setup.program sourceBefore.saved =
            message.payload.attempt.phase := by
        rw [sourceSaved]
        change instructionCount setup.program - ProtocolState.remaining setup.program startPoint = _
        rw [startLow, phaseLow]
        exact congrArg CommitAttemptId.phase beforeAttempt.symm
      have sourceReads (publication : PublicationResult (L.Val ty))
          (data : phaseRecoveryBindingData setup .concurrent named owner ty binding
            ((sourceJoint owner).map (·.semantic)) = (publication, false)) :
          sourceBindingAt setup message.payload.attempt named owner ty binding original.trace =
            PublicationResult.equivOption publication := by
        have actual := sourceBindingAt_of_origin setup message.payload.attempt named owner ty
          binding sourceBefore sourcePrior sourceJoint sourceLegal (some sourceAfter) sourceMoved
            sourceGenerationAt sourceSavedAt sourcePosition (publication, false) data
              original.trace sourceKept
        cases publication <;> exact actual
      have readBack := sourceReads ((phase.drain current).native.bindingResult candidate ty) literal
      cases resultEq : (phase.drain current).native.bindingResult candidate ty with
      | failure =>
        rw [resultEq] at readBack
        have impossible := readBack.symm.trans canonicalRead
        cases impossible
      | success old =>
        rw [resultEq] at readBack
        have same : old = raw := Option.some.inj (readBack.symm.trans canonicalRead)
        exact congrArg PublicationResult.success same
    have lower : before.execution.application.attempt.phase ≤ named.val := by
      rw [← phaseLow]
      exact bounds.1
    have acceptedAfter := receipts named candidate lower accepted
    rw [candidateOwner, ← beforeAttempt] at acceptedAfter
    obtain ⟨actual, authored, actualSender, actualCall, actualAttempt⟩ :=
      (stamp named candidate accepted).resolve_left (Nat.not_lt.mpr lower)
    have finalOutputs : ∀ actor, (nativeApplication).outputs (before.execution.recall actor) ⊆
        (nativeApplication).outputs (control.execution.recall actor) := by
      intro actor sent emitted
      have recallPrefix := (nativeApplication).reaches_recall_prefix nativeInitial
        implementation.horizon
        implementation.scheduler ((nativeMenu).reaches_raw nativeInitial implementation.horizon
          implementation.scheduler
            ((TracePrefix.extend .refl joint legal moved).trans exitToFinal).reachesWithin)
        before control rfl rfl actor
      obtain ⟨entry, member, output⟩ := List.mem_filterMap.mp emitted
      exact List.mem_filterMap.mpr ⟨entry, recallPrefix.subset member, output⟩
    have actualOutput := finalOutputs candidate.1 authored
    have messageOutput : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
    let finalRaw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace
    have inputRecall := (nativeApplication).history_inputRecall nativeInitial
      implementation.horizon implementation.scheduler finalRaw
    have messageInput : message ∈ control.execution.network.inputs := by
      rw [← inputRecall owner] at messageOutput
      exact (List.mem_filter.mp messageOutput).1
    have actualInput : actual ∈ control.execution.network.inputs := by
      rw [← inputRecall candidate.1] at actualOutput
      exact (List.mem_filter.mp actualOutput).1
    have cleanHistory := (PhaseCount.onePacketMenu_countClean implementation.runtime
      implementation.leaks implementation.bounds implementation.scheduler).history nativeInitial
        implementation.horizon (fun state _ => PhaseCount.countClean_initial implementation.runtime
          implementation.leaks state) trace
    have samePacket : message = actual := PhaseCount.Permits.eq_of_same_event
      ((PhaseCount.permits_eq_true_iff _ _).mp (cleanHistory.2 message messageInput))
      ((PhaseCount.permits_eq_true_iff _ _).mp (cleanHistory.2 actual actualInput))
      messageInput actualInput
      (fun left leftInput right rightInput same =>
        (nativeApplication).input_identifier_injective_history nativeInitial implementation.horizon
          implementation.scheduler control finalRaw left right leftInput rightInput same)
      (sender.trans (actualSender.trans candidateOwner).symm)
      (by simp only [PhaseCount.event?, call, actualCall, Payload.event?, Option.map_some,
        beforeAttempt, actualAttempt])
    have handleEq : handle = candidate := by
      have calls := (congrArg (fun signed => signed.payload.packet.call) samePacket)
      rw [call, actualCall] at calls
      exact (Payload.commitment.inj calls).2
    subst candidate
    have typedRead := valid.binding_read
      (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout (.binding owner ty))
      named rfl (finishedPhase namedInside)
    simp only [accepted, Option.elim_some, result] at typedRead
    have castSome {α β : Type} (same : α = β) (item : α) :
        cast (congrArg Option same) (some item) = some (cast same item) := by
      cases same
      rfl
    have stored : (phase.drain current).native.config.store (.inr named) =
        some (cast (congrArg EventField.Value binding.symm) (.success raw)) := by
      have pushed := congrArg
        (cast (congrArg (fun kind : EventField Player L => Option kind.Value) binding.symm))
          typedRead
      have rawEq : (phase.drain current).native.config.store (.inr named) =
          cast (congrArg Option (congrArg EventField.Value binding.symm))
            (some (.success raw)) := by
        simpa only [FieldRef.get?, cast_cast, cast_eq] using pushed
      exact rawEq.trans (castSome (congrArg EventField.Value binding.symm) (.success raw))
    have settled : after.execution.application =
        PhaseRuntimeState.settle (phase :: rest) before.execution.application.generation
          before.execution.application.entry current before.execution.application.retired := by
      simpa only [PhaseRuntimeState.normalize, phases] using normalized
    have retainedValue := completed_binding_retained setup phase rest
      before.execution.application.generation before.execution.application.entry current
        before.execution.application.retired finishedPhase (.inr named) handle _ accepted stored
    have retain (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
        (selected : snapshot = after.execution.application.current.native ∨
          snapshot = after.execution.application.entry.native ∨
          ∃ retired ∈ after.execution.application.retired, snapshot = retired.state)
        (accepted : snapshot.accepted (.inr named) = some handle)
        (stored : (⟨.inr named, binding⟩ :
          FieldRef (serviceGraph setup .concurrent).layout (.binding owner ty)).get?
            snapshot.config.store = some (.success raw)) :
        control.execution.application.current.native.bindingResult handle ty = .success raw := by
      obtain ⟨_record, _message, _owned, _recorded, _emitted, _call, result, _meaning⟩ :=
        positive_original_annotated_admitted_value setup values implementation operational
          fullValues sourceProfile nativeProfile who control trace active tape target cut finished
            word canonicalSupported event payload clean value positive after afterTrace exitToFinal
              snapshot selected owner ty named binding handle raw accepted stored
      exact result
    have acceptedFinal : PhaseService.BindingAccepted implementation.runtime implementation.leaks
        ⟨message.payload.attempt, named⟩ owner control.execution := by
      obtain ⟨acceptedMessage, acceptedInput, acceptedSender, acceptedAttempt, acceptedEvent,
        received⟩ := acceptedAfter
      have afterRecall := (nativeApplication).history_inputRecall nativeInitial
        implementation.horizon implementation.scheduler
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
            afterTrace) owner
      have output : acceptedMessage ∈ (nativeApplication).outputs
          (after.execution.recall owner) := by
        rw [← afterRecall]
        exact List.mem_filter.mpr ⟨acceptedInput,
          by simpa only [decide_eq_true_eq] using acceptedSender⟩
      have path := (nativeMenu).reaches_raw nativeInitial implementation.horizon
        implementation.scheduler exitToFinal.reachesWithin
      have recalled := (nativeApplication).reaches_recall_prefix nativeInitial
        implementation.horizon implementation.scheduler path after control rfl rfl owner
      obtain ⟨entry, entered, emitted⟩ := List.mem_filterMap.mp output
      have finalOutput : acceptedMessage ∈ (nativeApplication).outputs
          (control.execution.recall owner) :=
        List.mem_filterMap.mpr ⟨entry, recalled.subset entered, emitted⟩
      rw [← inputRecall owner] at finalOutput
      have keptReceipts := (nativeApplication).reaches_receipts_prefix nativeInitial
        implementation.horizon implementation.scheduler path after control rfl rfl
      exact ⟨acceptedMessage, (List.mem_filter.mp finalOutput).1, acceptedSender,
        acceptedAttempt, acceptedEvent, keptReceipts.subset received⟩
    refine ⟨?_, acceptedFinal⟩
    rcases retainedValue with ⟨retired, member, image⟩ | ⟨acceptedSaved, storedSaved⟩
    · apply retain (phase.drain current).native
        (Or.inr (Or.inr ⟨retired, by rw [settled]; exact member, image.symm⟩)) accepted typedRead
    · apply retain after.execution.application.entry.native (Or.inr (Or.inl rfl))
      · simpa only [settled] using acceptedSaved
      · have savedStore : after.execution.application.entry.native.config.store (.inr named) =
            some (cast (congrArg EventField.Value binding.symm) (.success raw)) := by
          simpa only [settled] using storedSaved
        change cast (congrArg Option (congrArg EventField.Value binding))
          (after.execution.application.entry.native.config.store (.inr named)) =
            some (.success raw)
        rw [savedStore, castSome (congrArg EventField.Value binding)]
        exact congrArg some
          ((cast_cast (congrArg EventField.Value binding.symm)
            (congrArg EventField.Value binding) (.success raw)).trans (cast_eq _ _))

open Classical in
/-- Every successful source read named by an actual emitted binding recovers
the original native value, in both historical and current namespaces. -/
private theorem positive_original_annotated_recorded_result
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (owner : Player) (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : record.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle)
    (raw : L.Val ty)
    (read : sourceBindingAt setup message.payload.attempt named owner ty binding
      finished.trace = some raw) :
    control.execution.application.current.native.bindingResult handle ty = .success raw := by
  by_cases historical : message.payload.attempt ≠ control.execution.application.attempt
  · exact (positive_original_annotated_historical_result setup values implementation operational
      fullValues sourceProfile nativeProfile who control trace active tape target cut finished word
        canonicalSupported event payload clean value positive owner record recorded material
          transmitted message emitted named ty binding handle call historical raw read).1
  · have current := not_ne_iff.mp historical
    have actual := positive_original_annotated_current_result setup values implementation
      operational fullValues sourceProfile nativeProfile who control trace active tape target cut
        finished word canonicalSupported event payload clean value positive owner record recorded
          material transmitted message emitted named ty binding handle call current
    rw [current] at read
    exact PublicationResult.equivOption.injective (actual.1.symm.trans read)

open Classical in
/-- The positive source completion retains the entire original correlated
input tuple and the actual native initializer's encoded inputs. -/
private theorem positive_original_annotated_initial_inputs
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    :
    ∃ theta : State L setup.context,
      theta ∈ setup.initialLaw.support ∧
      control.execution.application.current.native.config.inputs = encodeInputs theta ∧
      ∃ final : CommitRecoveryState setup.program,
        finished.state = some final ∧ ProtocolState.base setup.program final.point = theta := by
  classical
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  obtain ⟨entry, current, targetTrace, targetEq, _targetGood, erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target word canonicalSupported prefixPositive
        event payload clean
  have foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at prefixPositive
    dsimp only at prefixPositive
    have selected := (mul_ne_zero_iff.mp prefixPositive).2
    split at selected
    · rename_i qualified
      exact qualified.1
    · simp only [ne_eq, not_true_eq_false] at selected
  let chosen := entry.canonicalCut setup values implementation operational fullValues control trace
    who active event payload clean foreign
  cases targetEq
  obtain ⟨matched, endpoint, cutBase, _cutSaved⟩ :=
    setup.commitRecovery_base_of_prefix entry.cursor.current
      (setup.proposalRecoveryEraseTrace entry.cursor.trace)
      (source_initial_base_supported setup entry.cursor.current entry.cursor.trace).2
      (setup.proposalRecoveryEraseTrace chosen.trace)
      (setup.proposalRecoveryEraseTrace_prefix chosen.past)
  have matchedEq : matched = chosen.current := (Option.some.inj endpoint).symm
  subst matched
  have entryBase : ProtocolState.base setup.program entry.cursor.current.point = chosen.theta :=
    cutBase.symm.trans chosen.base_eq_theta
  have erasedState : entry.cursor.current.eraseHistory = current.eraseHistory :=
    Option.some.inj (congrArg Prod.fst (congrArg Prod.fst erased))
  have baseEq := congrArg
    (fun state : CommitRecoveryState setup.program => ProtocolState.base setup.program state.point)
      erasedState
  simp only [CommitRecoveryState.eraseHistory, ProtocolState.base_withHistory] at baseEq
  have targetBase : ProtocolState.base setup.program current.point = chosen.theta :=
    baseEq.symm.trans entryBase
  have information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape ⟨some current, targetTrace⟩ cut finished
      word canonicalSupported (control.execution.recall who)
        (control.execution.observe nativeApplication who) information event payload clean value
          positive
  have retained : TracePrefix targetTrace finished.trace :=
    pair.2.2.2.2.1.trans pair.2.2.2.2.2.1
  obtain ⟨final, finalState, finalBase, _finalSaved⟩ :=
    setup.commitRecovery_base_of_prefix current
      (setup.proposalRecoveryEraseTrace targetTrace)
      (source_initial_base_supported setup current targetTrace).2
      (setup.proposalRecoveryEraseTrace finished.trace)
      (setup.proposalRecoveryEraseTrace_prefix retained)
  have originalBase : ProtocolState.base setup.program final.point = chosen.theta :=
    finalBase.trans targetBase
  exact ⟨chosen.theta, chosen.thetaSupported, chosen.originalInputs, final, finalState,
    originalBase⟩

open Classical in
/-- Initial binding meanings use the entire original correlated input tuple,
as fixed by the erased entry and preserved through the actual source continuation. -/
theorem positive_original_annotated_initial_value
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (input : (serviceGraph setup .concurrent).InputId) (owner : Player) (ty : L.Ty)
    (binding : (serviceGraph setup .concurrent).inputLayout input = .binding owner ty)
    (raw : Raw L)
    (meaning : sourceHandleMeaning setup implementation finished control
      (owner, .initial input) = some raw) :
    control.execution.application.current.native.candidates.lookup (owner, .initial input) =
      .openable raw := by
  classical
  obtain ⟨theta, drawn, inputs, final, finalState, originalBase⟩ :=
    positive_original_annotated_initial_inputs setup values implementation operational fullValues
      sourceProfile nativeProfile who control trace active tape target cut finished word
        canonicalSupported event payload clean value positive
  unfold sourceHandleMeaning at meaning
  change (finished.state.bind fun current =>
    match (State.initial
      (encodeInputs (ProtocolState.base setup.program current.point))).candidates.lookup
        (owner, .initial input) with
    | .openable value => some value
    | .fresh | .unopenable => none) = some raw at meaning
  rw [finalState] at meaning
  change (match (State.initial
      (encodeInputs (ProtocolState.base setup.program final.point))).candidates.lookup
        (owner, .initial input) with
    | .openable value => some value
    | .fresh | .unopenable => none) = some raw at meaning
  rw [originalBase] at meaning
  have initialOpen : (State.initial (encodeInputs theta)).candidates.lookup
      (owner, .initial input) = .openable raw := by
    generalize found : (State.initial (encodeInputs theta)).candidates.lookup
      (owner, .initial input) = candidate at meaning
    cases candidate with
    | fresh => cases meaning
    | unopenable => cases meaning
    | openable actual =>
      have same : actual = raw := Option.some.inj meaning
      exact congrArg CommitmentCandidate.openable same
  exact (sourceReplayReferenceInitialCatalogue setup implementation operational control trace
    theta drawn inputs input owner ty binding).trans
      initialOpen

open Classical in
/-- An actual historical preparation without an accepting receipt has no source
meaning in a positive original annotation. -/
theorem positive_original_annotated_unaccepted_meaning
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (owner : Player) (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : record.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle)
    (historical : message.payload.attempt ≠ control.execution.application.attempt)
    (handleOwner : handle.1 = owner)
    (unaccepted : ¬ PhaseService.BindingAccepted implementation.runtime implementation.leaks
      ⟨message.payload.attempt, named⟩ owner control.execution) :
    sourceHandleMeaning setup implementation finished control handle = none := by
  classical
  by_contra nonempty
  obtain ⟨raw, meaning⟩ := Option.ne_none_iff_exists'.mp nonempty
  have recalled : record ∈ control.execution.recall handle.1 := by
    rw [handleOwner]
    exact recorded
  have literal := sourceHandleMeaning_of_emission setup implementation finished control trace
    handle record recalled message emitted named call owner ty binding
      (sourceBindingAt setup message.payload.attempt named owner ty binding finished.trace) rfl
  rw [meaning] at literal
  obtain ⟨recovered, read, _rawEq⟩ := Option.map_eq_some_iff.mp literal.symm
  exact unaccepted (positive_original_annotated_historical_result setup values implementation
    operational fullValues sourceProfile nativeProfile who control trace active tape target cut
      finished word canonicalSupported event payload clean value positive owner record recorded
        material transmitted message emitted named ty binding handle call historical recovered
          read).2

open Classical in
/-- A prepared handle with a source meaning in the completed annotation has
that exact immutable original native value, including pending and canceled origins. -/
private theorem positive_original_annotated_prepared_value
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (handle : Handle (serviceGraph setup .concurrent)) (serial : Nat)
    (prepared : handle.2 = .prepared serial) (raw : Raw L)
    (meaning : sourceHandleMeaning setup implementation finished control handle = some raw) :
    control.execution.application.current.native.candidates.lookup handle = .openable raw := by
  classical
  unfold sourceHandleMeaning at meaning
  rw [prepared] at meaning
  obtain ⟨record, recorded, located⟩ := List.exists_of_findSome?_eq_some meaning
  obtain ⟨message, emitted, selected⟩ := Option.bind_eq_some_iff.mp located
  have output : message ∈ (nativeApplication).outputs (control.execution.recall handle.1) :=
    List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
  have inputRecall := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace) handle.1
  have member : message ∈ control.execution.network.inputs := by
    rw [← inputRecall] at output
    exact (List.mem_filter.mp output).1
  cases packet : message.payload.packet.call with
  | malformed malformed =>
    simp only [packet] at selected
    cases selected
  | opening named candidate opened =>
    simp only [packet] at selected
    cases selected
  | commitment named candidate =>
    simp only [packet] at selected
    by_cases same : candidate = handle
    · subst candidate
      simp only [↓reduceIte] at selected
      split at selected
      · rename_i owner ty binding
        obtain ⟨recovered, read, rawEq⟩ := Option.map_eq_some_iff.mp selected
        obtain ⟨actualSerial, opening, evidence, authored, _handleEq, _sender, authoredMember,
            authoredEmitted, authoredAction, _fresh, _namespace, _result⟩ :=
          issued_binding_record setup implementation control trace owner named ty binding
            handle message member packet
        let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
          ⟨⟨.commitment named (owner, .prepared actualSerial), opening⟩, evidence⟩
        have transmitted : authored.action.transmission = some material :=
          congrArg (fun action : (nativeApplication).Action => action.transmission) authoredAction
        have result := positive_original_annotated_recorded_result setup values implementation
          operational fullValues sourceProfile nativeProfile who control trace active tape target
            cut finished word canonicalSupported event payload clean value positive owner authored
              authoredMember material transmitted message authoredEmitted named ty binding handle
                packet recovered read
        have opened := (State.bindingResult_eq_success_iff
          control.execution.application.current.native handle ty recovered).mp result
        exact opened.trans (congrArg CommitmentCandidate.openable rawEq)
      · cases selected
    · simp only [ite_eq_right same] at selected
      cases selected

omit [Fintype Player] in
/-- A retained source prefix reads the initial segment of the actual labeled
joint word in chronological order. -/
private theorem source_joint_recall_prefix
    {first last : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace first)
    (trace : setup.proposalRecoveryProtocol.Trace last)
    (retained : TracePrefix prior trace) :
    (setup.proposalRecoveryJointRecall trace).reverse.take prior.length =
      (setup.proposalRecoveryJointRecall prior).reverse := by
  have length {state : setup.proposalRecoveryProtocol.State}
      (history : setup.proposalRecoveryProtocol.Trace state) :
      (setup.proposalRecoveryJointRecall history).length = history.length := by
    induction history with
    | start => rfl
    | extend history joint legal moved ih =>
      simpa only [Setup.proposalRecoveryJointRecall, List.length_cons, Trace.length] using
        congrArg Nat.succ ih
  induction retained with
  | refl => exact List.take_of_length_le (by rw [List.length_reverse, length])
  | @extend state next previous earlier joint legal moved ih =>
    change ((joint :: setup.proposalRecoveryJointRecall previous).reverse).take prior.length = _
    rw [List.reverse_cons, List.take_append_of_le_length (by
      rw [List.length_reverse, length]
      exact earlier.length_le)]
    exact ih

omit [Fintype Player] in
/-- Equal earlier owned binding reads give equal literal labeled coordinates
at retained equally deep prefixes of ordinary commitment attempts. -/
private theorem ordinary_commit_coordinate_prefix
    (who : Player) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (leftSource rightSource : SourceProgram.Config Player L Γ)
    (excluded : Finset Player)
    (leftFinished rightFinished : SourceProgram.Config Player L Δ)
    (leftAfter rightAfter : Finset Player)
    (leftAttempt : block.Attempt leftSource excluded leftFinished leftAfter)
    (rightAttempt : block.Attempt rightSource excluded rightFinished rightAfter)
    (leftMask : leftAfter = excluded) (rightMask : rightAfter = excluded)
    (k : Nat)
    (earlier : ∀ position < k, block.wordAction who position (leftFinished.view who) =
      block.wordAction who position (rightFinished.view who))
    {leftRootState rightRootState leftState rightState leftEndState rightEndState :
      setup.proposalRecoveryProtocol.State}
    (leftRoot : setup.proposalRecoveryProtocol.Trace leftRootState)
    (rightRoot : setup.proposalRecoveryProtocol.Trace rightRootState)
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (leftEnd : setup.proposalRecoveryProtocol.Trace leftEndState)
    (rightEnd : setup.proposalRecoveryProtocol.Trace rightEndState)
    (entryCoordinate : (setup.proposalRecoveryJointRecall leftRoot).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall rightRoot).map (fun joint => joint who))
    (leftLabels : setup.proposalRecoveryJointRecall leftEnd =
      leftAttempt.joints.reverse.map
        (fun joint owner => (joint owner).map ProposalRecoveryMove.ordinary) ++
          setup.proposalRecoveryJointRecall leftRoot)
    (rightLabels : setup.proposalRecoveryJointRecall rightEnd =
      rightAttempt.joints.reverse.map
        (fun joint owner => (joint owner).map ProposalRecoveryMove.ordinary) ++
          setup.proposalRecoveryJointRecall rightRoot)
    (leftRetained : TracePrefix left leftEnd) (rightRetained : TracePrefix right rightEnd)
    (leftDepth : left.length = leftRoot.length + k)
    (rightDepth : right.length = rightRoot.length + k) :
    (setup.proposalRecoveryJointRecall left).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right).map (fun joint => joint who) := by
  have length {state : setup.proposalRecoveryProtocol.State}
      (history : setup.proposalRecoveryProtocol.Trace state) :
      (setup.proposalRecoveryJointRecall history).length = history.length := by
    induction history with
    | start => rfl
    | extend history joint legal moved ih =>
      simpa only [Setup.proposalRecoveryJointRecall, List.length_cons, Trace.length] using
        congrArg Nat.succ ih
  have rows : (leftAttempt.joints.map (fun joint => joint who)).take k =
      (rightAttempt.joints.map (fun joint => joint who)).take k := by
    rw [commitAttempt_wordAction block suffix leftSource excluded leftFinished leftAfter
      leftAttempt leftMask, commitAttempt_wordAction block suffix rightSource excluded
      rightFinished rightAfter rightAttempt rightMask]
    simp only [List.map_map, ← List.map_take, Function.comp_def]
    apply List.map_congr_left
    intro position member
    have bounded : position < k := by
      have taken : position ∈ List.range (min k block.length) := by
        simpa only [List.take_range] using member
      have bound := List.mem_range.mp taken
      omega
    rw [earlier position bounded]
  have leftWord := source_joint_recall_prefix setup left leftEnd leftRetained
  have rightWord := source_joint_recall_prefix setup right rightEnd rightRetained
  have leftChronology : (setup.proposalRecoveryJointRecall left).reverse =
      (setup.proposalRecoveryJointRecall leftRoot).reverse ++
        (leftAttempt.joints.map
          (fun joint owner => (joint owner).map ProposalRecoveryMove.ordinary)).take k := by
    rw [← leftWord, leftLabels, List.reverse_append, ← List.map_reverse,
      List.reverse_reverse, leftDepth, ← length leftRoot, ← List.length_reverse]
    exact List.take_length_add_append k
  have rightChronology : (setup.proposalRecoveryJointRecall right).reverse =
      (setup.proposalRecoveryJointRecall rightRoot).reverse ++
        (rightAttempt.joints.map
          (fun joint owner => (joint owner).map ProposalRecoveryMove.ordinary)).take k := by
    rw [← rightWord, rightLabels, List.reverse_append, ← List.map_reverse,
      List.reverse_reverse, rightDepth, ← length rightRoot, ← List.length_reverse]
    exact List.take_length_add_append k
  apply List.reverse_injective
  rw [← List.map_reverse, ← List.map_reverse, leftChronology, rightChronology,
    List.map_append, List.map_append]
  congr 1
  · simpa only [List.map_reverse] using congrArg List.reverse entryCoordinate
  · have labeled := congrArg (List.map (Option.map ProposalRecoveryMove.ordinary)) rows
    simpa only [← List.map_take, List.map_map, Function.comp_def] using labeled

open Classical in
/-- A positive original annotated atom fixes the earlier focal reads to those
of the actual canonical source completion, in the original maximal block. -/
private theorem positive_original_annotated_owned_prefix
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    ∃ (foreign : ∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner ⟨some control, trace⟩)
      (entry : NativeBindingEntry setup implementation operational control trace who event),
      let canonical := entry.canonicalCut setup values implementation operational fullValues
        control trace who active event payload clean foreign
      match finished.state.bind (fun current => residualEntry? entry.suffix
          (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point))
            current.point),
        canonical.completed.state.bind (fun current => residualEntry? entry.suffix
          (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point)) current.point)
      with
      | some actual, some reference =>
          (∀ owner, issuedLedger setup implementation entry.block
            control.execution.application.attempt.phase control
            (control.execution.application.attempt.phase + entry.block.length) owner
              (actual.view owner)) ∧
          (∀ position < event.val - control.execution.application.attempt.phase,
            entry.block.wordAction who position (actual.view who) =
              entry.block.wordAction who position (reference.view who)) ∧
          entry.block.wordAction who (event.val - control.execution.application.attempt.phase)
            (actual.view who) = decodeEventAction setup.program event
              (cast (congrArg EventField.Action clean.binding.symm) (.success value))
      | _, _ => False := by
  classical
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  have foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at prefixPositive
    dsimp only at prefixPositive
    have selected := (mul_ne_zero_iff.mp prefixPositive).2
    split at selected
    · rename_i qualified
      exact qualified.1
    · simp only [ne_eq, not_true_eq_false] at selected
  obtain ⟨entry, _current, _targetTrace, _targetEq, _targetGood, _erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target word canonicalSupported prefixPositive
        event payload clean
  have information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape target cut finished word canonicalSupported
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        information event payload clean value positive
  have observation : bindingCompletedObservation setup implementation
      (checkpointSelection setup implementation operational trace).val.checkpoint control who
        event payload clean.binding value finished = true := by
    have observed := pair.2.2.2.1
    dsimp only at observed
    unfold bindingCompletedObservation residualBindingObservation
    dsimp only
    split at observed
    · cases observed
    · rename_i result parsed
      rw [parsed]
      have tests := decide_eq_true_eq.mp observed
      apply decide_eq_true
      refine ⟨?_, tests.2.1⟩
      intro owner
      by_cases own : owner = who
      · subst owner
        exact tests.1
      · exact tests.2.2 owner own
  have original := selected_binding_observation setup implementation operational control trace
    who event payload clean.binding entry value
  rw [original.2] at observation
  dsimp only at observation
  have reference := canonical_source_issued_observation setup values implementation operational
    fullValues control trace who active event payload clean foreign entry
  dsimp only at reference
  refine ⟨foreign, entry, ?_⟩
  dsimp only
  split at observation
  · simp only [Bool.false_eq_true] at observation
  · rename_i actual actualParsed
    rw [actualParsed]
    have tests := decide_eq_true_eq.mp observation
    split at reference
    · exact reference.elim
    · rename_i referenceConfig referenceParsed
      rw [referenceParsed]
      have phaseLow : entry.phase.low = control.execution.application.attempt.phase := by
        obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
        simp only [PhaseRuntimeState.attempt, phases, List.head?_cons,
          Option.map_some, Option.getD_some]
      have phaseHigh : entry.phase.high =
          control.execution.application.attempt.phase + entry.block.length := by
        have bounds := entry.phase.nonempty
        have size := entry.size
        omega
      have request : control.execution.application.SeedRequest who
          ⟨control.execution.application.attempt, event⟩ :=
        (entry.canonicalCut setup values implementation operational fullValues control trace
          who active event payload clean foreign).request
      have ledger := issuedLedger_iff_prefix_at_request setup implementation entry.block
        entry.suffix entry.cursor.embedding control.execution.application.attempt.phase
          (fun index => (entry.cursor.compiled.rankEq index).trans (by rw [entry.offset, phaseLow]))
          entry.cursor.views.actionEq trace entry.phase entry.installed phaseLow phaseHigh who
            event payload clean.binding request
              (by have bounds := (entry.phase.mem_events event).mp entry.inside; omega)
              clean.unsent (referenceConfig.view who) (actual.view who) (reference who)
      exact ⟨tests.1, ledger.mp (tests.1 who), tests.2⟩

omit [Fintype Player] in
/-- The commitment information comparison is invariant under the literal
saved-entry identities supplied by actual source histories. -/
private theorem commit_window_information_of_entries
    (who : Player) (first second : CommitRecoveryState setup.program)
    (excluded : Finset Player) (generation : Nat)
    (firstEntry : first = CommitRecoveryState.atPoint first.point excluded generation)
    (secondEntry : second = CommitRecoveryState.atPoint second.point excluded generation)
    (leftPrior : setup.proposalRecoveryProtocol.Trace (some first))
    (rightPrior : setup.proposalRecoveryProtocol.Trace (some second))
    (entryInformation : setup.proposalRecoveryModel.infoOf who leftPrior =
      setup.proposalRecoveryModel.infoOf who rightPrior)
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (alive : who ∉ excluded)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix leftPrior left) (rightRetained : TracePrefix rightPrior right)
    (leftInside : left.length + ProtocolState.commitEnd setup.program first.point <
      leftPrior.length + ProtocolState.remaining setup.program first.point)
    (rightInside : right.length + ProtocolState.commitEnd setup.program second.point <
      rightPrior.length + ProtocolState.remaining setup.program second.point)
    (depth : left.length - leftPrior.length = right.length - rightPrior.length)
    (leftExcluded : (setup.commitRecoveryPublic leftState).1 = excluded)
    (rightExcluded : (setup.commitRecoveryPublic rightState).1 = excluded)
    (coordinate : (setup.proposalRecoveryJointRecall left).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right).map (fun joint => joint who)) :
    setup.proposalRecoveryModel.infoOf who left = setup.proposalRecoveryModel.infoOf who right := by
  have castHistory {first last : setup.proposalRecoveryProtocol.State} (same : first = last)
      (trace : setup.proposalRecoveryProtocol.Trace first) :
      (⟨last, same ▸ trace⟩ : setup.proposalRecoveryProtocol.History) = ⟨first, trace⟩ := by
    cases same
    rfl
  have castPrefix {first last state : setup.proposalRecoveryProtocol.State}
      (same : first = last) (prior : setup.proposalRecoveryProtocol.Trace first)
      (trace : setup.proposalRecoveryProtocol.Trace state) (retained : TracePrefix prior trace) :
      TracePrefix (same ▸ prior) trace := by
    cases same
    exact retained
  let firstPrior : setup.proposalRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint first.point excluded generation)) :=
    congrArg some firstEntry ▸ leftPrior
  let secondPrior : setup.proposalRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint second.point excluded generation)) :=
    congrArg some secondEntry ▸ rightPrior
  have firstHistory := castHistory (congrArg some firstEntry) leftPrior
  have secondHistory := castHistory (congrArg some secondEntry) rightPrior
  have firstClock : firstPrior.length = leftPrior.length :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History => history.trace.length)
      firstHistory
  have secondClock : secondPrior.length = rightPrior.length :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History => history.trace.length)
      secondHistory
  have information : setup.proposalRecoveryModel.infoOf who firstPrior =
      setup.proposalRecoveryModel.infoOf who secondPrior :=
    (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      setup.proposalRecoveryModel.infoOf who history.trace) firstHistory).trans
        (entryInformation.trans (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
          setup.proposalRecoveryModel.infoOf who history.trace) secondHistory).symm)
  exact commit_window_information_of_coordinate setup who first.point second.point excluded
    generation firstPrior secondPrior information committing alive left right
      (castPrefix (congrArg some firstEntry) leftPrior left leftRetained)
      (castPrefix (congrArg some secondEntry) rightPrior right rightRetained)
      (by simpa only [firstClock] using leftInside)
      (by simpa only [secondClock] using rightInside)
      (by simpa only [firstClock, secondClock] using depth)
      leftExcluded rightExcluded coordinate

open Classical in
/-- Every positive original annotated summand reaches the full focal
information of its actual canonical source cut. -/
private theorem positive_original_annotated_information
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    ∃ (foreign : ∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner ⟨some control, trace⟩)
      (entry : NativeBindingEntry setup implementation operational control trace who event),
      setup.proposalRecoveryModel.infoOf who cut.trace =
        setup.proposalRecoveryModel.infoOf who
          (entry.canonicalCut setup values implementation operational fullValues control trace
            who active event payload clean foreign).trace ∧
      sourceCommitFuel setup cut = entry.block.length -
        (event.val - control.execution.application.attempt.phase) ∧
      (((setup.proposalRecoveryJointRecall finished.trace).reverse[cut.trace.length]?).map
        (fun joint => (joint who).map ProposalRecoveryMove.semantic)) =
          some (CommitRecoveryMove.lift (decodeEventAction setup.program event
            (cast (congrArg EventField.Action clean.binding.symm) (.success value)))) := by
  classical
  obtain ⟨foreign, entry, owned⟩ := positive_original_annotated_owned_prefix setup values
    implementation operational fullValues sourceProfile nativeProfile who control trace active
      tape target cut finished word canonicalSupported event payload clean value positive
  let canonical := entry.canonicalCut setup values implementation operational fullValues
    control trace who active event payload clean foreign
  have information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape target cut finished word canonicalSupported
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        information event payload clean value positive
  obtain ⟨current, targetTrace, targetEq, _targetGood, erased⟩ :=
    closed_key_entry_erased_history setup implementation operational who control trace event
      entry target foreign pair.1
  subst target
  let cursor := PhaseProposalOrdinarySourceCursor.of_erasedHistory setup .concurrent
    implementation.runtime implementation.leaks implementation.plan entry.entry entry.phase
      entry.block entry.suffix entry.cursor current targetTrace erased
  let k := event.val - control.execution.application.attempt.phase
  have phaseLow : entry.phase.low = control.execution.application.attempt.phase := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons,
      Option.map_some, Option.getD_some]
  have inside : k < entry.block.length := by
    have bounds := (entry.phase.mem_events event).mp entry.inside
    have size := entry.size
    dsimp only [k]
    omega
  have selected := selected_binding_observation setup implementation operational control trace
    who event payload clean.binding entry value
  have support := pair.2.2.1
  obtain ⟨g, first, rest⟩ := (PMF.mem_support_bind_iff ..).mp support
  obtain ⟨G, last, same⟩ := (PMF.mem_support_map_iff ..).mp rest
  have cutEq : g = cut := congrArg Prod.fst same
  have finishedEq : G = finished := congrArg Prod.snd same
  subst g
  subst G
  have completedSupport : finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) entry.block.length
        ⟨some current, targetTrace⟩).support := by
    have joined := (PMF.mem_support_bind_iff ..).mpr ⟨cut, first, last⟩
    rw [← setup.proposalRecoveryModel.runBehavioralFrom_add] at joined
    rw [selected.1] at joined
    change finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) (k + (entry.block.length - k))
        ⟨some current, targetTrace⟩).support at joined
    simpa only [show k + (entry.block.length - k) = entry.block.length by omega] using joined
  obtain ⟨actual, finalState, finalTrace, actualAttempt, finalEq, actualPoint, actualMask,
      _actualEntry, _actualGeneration, _actualWord, actualLabels, _actualProper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values entry.block entry.suffix
      cursor.lift cursor.origin cursor.source current targetTrace cursor.point
        (cursor.excluded.trans cursor.entryExcluded.symm) finished completedSupport
  obtain ⟨reference, referenceState, referenceTrace, referenceAttempt, referenceEq,
      referencePoint, referenceMask, _referenceGeneration, _referenceLive,
      _referenceAgreement, _referenceWord, referenceLabels⟩ := canonical.blockResult
  change canonical.completed = ⟨some referenceState, referenceTrace⟩ at referenceEq
  change entry.block.Attempt entry.cursor.source entry.cursor.current.excluded reference
    referenceState.excluded at referenceAttempt
  change referenceState.excluded = entry.cursor.current.excluded at referenceMask
  change setup.proposalRecoveryJointRecall referenceTrace =
    referenceAttempt.joints.reverse.map
      (fun joint owner => (joint owner).map ProposalRecoveryMove.ordinary) ++
        setup.proposalRecoveryJointRecall entry.cursor.trace at referenceLabels
  have actualParsed : finished.state.bind (fun state => residualEntry? entry.suffix
      (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point)) state.point) =
        some actual := by
    rw [finalEq, Option.bind_some]
    exact (residualEntry?_eq_some_iff (entry.cursor.origin.compose
      (entry.block.protocolSuffix entry.suffix)) finalState.point actual).mpr actualPoint.symm
  have referenceParsed : canonical.completed.state.bind (fun state => residualEntry? entry.suffix
      (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point)) state.point) =
        some reference := by
    rw [referenceEq, Option.bind_some]
    exact (residualEntry?_eq_some_iff (entry.cursor.origin.compose
      (entry.block.protocolSuffix entry.suffix)) referenceState.point reference).mpr
        referencePoint.symm
  dsimp only at owned
  rw [actualParsed, referenceParsed] at owned
  have states : entry.cursor.current.eraseHistory = current.eraseHistory :=
    Option.some.inj (congrArg Prod.fst (congrArg Prod.fst erased))
  have masks : entry.cursor.current.excluded = current.excluded := congrArg (·.excluded) states
  have generations : entry.cursor.current.generation = current.generation :=
    congrArg (·.generation) states
  have entryInformation : setup.proposalRecoveryModel.infoOf who targetTrace =
      setup.proposalRecoveryModel.infoOf who entry.cursor.trace := by
    have key := pair.1.trans
      (congrArg (setup.proposalRecoveryClosedKey who) entry.canonicalHistory.symm)
    exact congrArg (fun key => key.2.1) key
  have geometry := positive_original_annotated_geometry setup values implementation operational
    fullValues sourceProfile nativeProfile who control trace active tape
      ⟨some current, targetTrace⟩ cut finished word canonicalSupported event payload clean value
        positive
  have leftDepth : cut.trace.length = targetTrace.length + k := geometry.2.2.2.1
  have rightDepth : canonical.trace.length = entry.cursor.trace.length + k := by
    have clock := canonical.clock
    change canonical.trace.length = entry.cursor.trace.length + (event.val - entry.phase.low)
      at clock
    simpa only [phaseLow, k] using clock
  have castJoints {before after : Finset Player} (same : before = after)
      (attempt : entry.block.Attempt entry.cursor.source before reference referenceState.excluded) :
      (same ▸ attempt).joints = attempt.joints := by
    cases same
    rfl
  have coordinate := ordinary_commit_coordinate_prefix setup who entry.block entry.suffix
    cursor.source entry.cursor.source current.excluded actual reference finalState.excluded
      referenceState.excluded actualAttempt (masks ▸ referenceAttempt) actualMask
      (by simpa only [masks] using referenceMask) k owned.2.1 targetTrace entry.cursor.trace
      cut.trace canonical.trace finalTrace referenceTrace
      (setup.proposalRecovery_coordinate_eq_of_info_eq who targetTrace entry.cursor.trace
        entryInformation) actualLabels
      (by simpa only [castJoints masks referenceAttempt] using referenceLabels)
      (Eq.mp (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
        TracePrefix cut.trace history.trace) finalEq) pair.2.2.2.2.2.1)
      (Eq.mp (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
        TracePrefix canonical.trace history.trace) referenceEq) canonical.future)
      leftDepth rightDepth
  have rootState := Option.some.inj (congrArg History.state entry.cursorHistory)
  have saved : entry.cursor.current.saved = entry.cursor.current.point := by
    rw [rootState]
    rfl
  have rootCommitting : ProtocolState.atCommit setup.program entry.cursor.current.point = true := by
    rw [← saved]
    exact entry.cursor.savedCommit (by omega)
  have committing : ProtocolState.atCommit setup.program current.point = true := by
    have points := congrArg (fun state => ProtocolState.atCommit setup.program state.point) states
    change ProtocolState.atCommit setup.program
        (ProtocolState.withHistory setup.program entry.cursor.current.point (fun _ => [])) =
      ProtocolState.atCommit setup.program
        (ProtocolState.withHistory setup.program current.point (fun _ => [])) at points
    rw [(ProtocolState.withHistory_control setup.program entry.cursor.current.point
      (fun _ => [])).2.1, (ProtocolState.withHistory_control setup.program current.point
        (fun _ => [])).2.1] at points
    exact points.symm.trans rootCommitting
  have rank : ProtocolState.remaining setup.program current.point =
      ProtocolState.remaining setup.program current.saved := by
    have points := congrArg (fun state => ProtocolState.remaining setup.program state.point) states
    have savedRanks := congrArg
      (fun state => ProtocolState.remaining setup.program state.saved) states
    simp only [CommitRecoveryState.eraseHistory, ProtocolState.remaining_withHistory]
      at points savedRanks
    rw [← points, ← savedRanks, saved]
  have firstEntry := source_commit_entry_eq_atPoint setup current targetTrace committing rank
  have secondEntry := source_commit_entry_eq_atPoint setup entry.cursor.current entry.cursor.trace
    rootCommitting (by rw [saved])
  have secondEntryShared : entry.cursor.current = CommitRecoveryState.atPoint
      entry.cursor.current.point current.excluded current.generation := by
    simpa only [masks, generations] using secondEntry
  have leftWindow : entry.block.length + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point := by
    change entry.block.length + ProtocolState.commitEnd setup.program cursor.current.point ≤
      ProtocolState.remaining setup.program cursor.current.point
    rw [cursor.point, cursor.origin.commitEnd_lift, cursor.origin.remaining_lift]
    exact entry.block.length_le_commit_window entry.suffix cursor.source
  have rightWindow : entry.block.length +
      ProtocolState.commitEnd setup.program entry.cursor.current.point ≤
        ProtocolState.remaining setup.program entry.cursor.current.point := by
    rw [entry.cursor.point, entry.cursor.origin.commitEnd_lift,
      entry.cursor.origin.remaining_lift]
    exact entry.block.length_le_commit_window entry.suffix entry.cursor.source
  have leftExcluded : (setup.commitRecoveryPublic cut.state).1 = current.excluded := by
    have lower := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix pair.2.2.2.2.1).reachesWithin
    have upper := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix pair.2.2.2.2.2.1).reachesWithin
    change current.excluded ⊆ (setup.commitRecoveryPublic cut.state).1 at lower
    rw [finalEq] at upper
    change (setup.commitRecoveryPublic cut.state).1 ⊆ finalState.excluded at upper
    exact Finset.Subset.antisymm (by simpa only [actualMask] using upper) lower
  have rightExcluded : canonical.current.excluded = current.excluded := by
    have lower := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix canonical.past).reachesWithin
    have upper := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix canonical.future).reachesWithin
    change entry.cursor.current.excluded ⊆ canonical.current.excluded at lower
    rw [referenceEq] at upper
    change canonical.current.excluded ⊆ referenceState.excluded at upper
    exact (Finset.Subset.antisymm (by simpa only [referenceMask] using upper) lower).trans masks
  have alive : who ∉ current.excluded := fun member =>
    canonical.survives (rightExcluded.symm ▸ member)
  have common := commit_window_information_of_entries setup who current entry.cursor.current
    current.excluded current.generation firstEntry secondEntryShared targetTrace entry.cursor.trace
      entryInformation committing alive cut.trace canonical.trace pair.2.2.2.2.1 canonical.past
      (by omega) (by omega) (by omega) leftExcluded rightExcluded coordinate
  have savedAtPoint : current.saved = current.point := congrArg CommitRecoveryState.saved firstEntry
  have distance : ProtocolState.remaining setup.program current.point =
      entry.block.length + ProtocolState.commitEnd setup.program current.point := by
    calc
      ProtocolState.remaining setup.program current.point =
          instructionCount (entry.block.prepend entry.suffix) := by
        change ProtocolState.remaining setup.program cursor.current.point =
          instructionCount (entry.block.prepend entry.suffix)
        rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
      _ = entry.block.length + instructionCount entry.suffix :=
        entry.block.instructionCount_prepend entry.suffix
      _ = entry.block.length + ProtocolState.commitEnd setup.program current.point := by
        have endpoint : ProtocolState.commitEnd setup.program current.point =
            instructionCount entry.suffix := by
          rw [← savedAtPoint]
          exact cursor.savedEnd (by omega)
        exact congrArg (Nat.add entry.block.length) endpoint.symm
  obtain ⟨cutState, cutStateEq, _cutCommitting, cutEnd, cutRank⟩ :=
    setup.commitRecovery_prefix_inside_commit current
      (setup.proposalRecoveryEraseTrace targetTrace) committing
      (setup.proposalRecoveryEraseTrace cut.trace)
      (setup.proposalRecoveryEraseTrace_prefix pair.2.2.2.2.1)
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using
        (show cut.trace.length + ProtocolState.commitEnd setup.program current.point <
          targetTrace.length + ProtocolState.remaining setup.program current.point by omega))
  simp only [setup.proposalRecoveryEraseTrace_length] at cutRank
  have fuel : sourceCommitFuel setup cut = entry.block.length - k := by
    unfold sourceCommitFuel
    rw [cutStateEq]
    change ProtocolState.remaining setup.program cutState.point -
      ProtocolState.commitEnd setup.program cutState.point = entry.block.length - k
    rw [cutEnd]
    omega
  have recallLength : (setup.proposalRecoveryJointRecall targetTrace).length =
      targetTrace.length := by
    have semantic := congrArg List.length
      (setup.proposalRecoveryJointRecall_semantic targetTrace)
    simpa only [List.length_map, setup.recoveryJointRecall_length,
      setup.proposalRecoveryEraseTrace_length] using semantic
  have nextRow :
      (((setup.proposalRecoveryJointRecall finished.trace).reverse)[cut.trace.length]?).map
      (fun joint => (joint who).map ProposalRecoveryMove.semantic) =
      some (CommitRecoveryMove.lift (decodeEventAction setup.program event
        (cast (congrArg EventField.Action clean.binding.symm) (.success value)))) := by
    rw [finalEq, actualLabels, List.reverse_append, ← List.map_reverse,
      List.reverse_reverse, leftDepth, List.getElem?_append_right (by
        rw [List.length_reverse, recallLength]
        omega)]
    rw [List.length_reverse, recallLength, Nat.add_sub_cancel_left,
      commitAttempt_wordAction entry.block entry.suffix cursor.source current.excluded
        actual finalState.excluded actualAttempt actualMask]
    simp only [List.getElem?_map, List.getElem?_range, inside, ↓reduceIte,
      Option.map_some, Option.map_map, Function.comp_def, alive,
      ProposalRecoveryMove.ordinary_semantic, Option.map_id']
    change some (CommitRecoveryMove.lift (entry.block.wordAction who
      (event.val - control.execution.application.attempt.phase) (actual.view who))) = _
    rw [owned.2.2]
  exact ⟨foreign, entry, common, fuel, nextRow⟩

open Classical in
/-- An actual supported ordinary continuation with a prescribed next binding
also supports forcing its encoded focal choice at that same information. -/
private theorem ordinary_encoded_forced_support
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (cut finished : setup.proposalRecoveryProtocol.History)
    (law : PMF (L.Val payload))
    (encode : L.Val payload → setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who cut.trace))
    (ordinary : sourceUnflaggedStrategy setup values who
      (setup.proposalRecoveryModel.infoOf who cut.trace) = law.map encode)
    (encoded : ∀ value, phaseRecoveryBindingData setup .concurrent event who payload binding
      ((encode value).val.map ProposalRecoveryMove.semantic) = (.success value, false))
    (value : L.Val payload)
    (fuelPositive : 0 < sourceCommitFuel setup cut)
    (progress : cut.trace.length < finished.trace.length)
    (supported : finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) (sourceCommitFuel setup cut) cut).support)
    (selected :
      (((setup.proposalRecoveryJointRecall finished.trace).reverse)[cut.trace.length]?).map
      (fun joint => (joint who).map ProposalRecoveryMove.semantic) =
        some (CommitRecoveryMove.lift (decodeEventAction setup.program event
          (cast (congrArg EventField.Action binding.symm) (.success value))))) :
    finished ∈ (sourceForcedBlock setup values who cut (encode value)).support := by
  classical
  let profile := sourceUnflaggedStrategy setup values
  let forced := Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
    profile who ((profile who).commit (setup.proposalRecoveryModel.infoOf who cut.trace)
      (encode value))
  have running : ¬ setup.proposalRecoveryProtocol.terminal cut.state := by
    intro stopped
    have frozen := supported
    rw [setup.proposalRecoveryModel.runBehavioralFrom_of_terminal _ _ stopped] at frozen
    have same : finished = cut := (PMF.mem_support_pure_iff ..).mp frozen
    subst finished
    omega
  have fuel : sourceCommitFuel setup cut = (sourceCommitFuel setup cut - 1) + 1 := by omega
  have support := supported
  rw [fuel, setup.proposalRecoveryModel.runBehavioralFrom_succ_localStep] at support
  obtain ⟨middle, first, tail⟩ := (PMF.mem_support_bind_iff ..).mp support
  obtain ⟨choices, drawn, localSupport⟩ := (PMF.mem_support_bind_iff ..).mp first
  have marginals := (independentProduct_support_iff _ _).mp drawn
  have localOriginal := localSupport
  rw [InformationModel.localStep, dite_eq_right running,
    PMF.mem_support_bindOnSupport_iff] at localSupport
  obtain ⟨next, moved, pureSupport⟩ := localSupport
  have middleEq := (PMF.mem_support_pure_iff ..).mp pureSupport
  subst middle
  have retained := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin profile
    (sourceCommitFuel setup cut - 1) _ finished tail).tracePrefix
  have chronology := source_joint_recall_prefix setup _ finished.trace retained
  have row := congrArg (fun entries : List (Player → Option (ProposalRecoveryMove Player L)) =>
    entries[cut.trace.length]?) chronology
  have recallLength : (setup.proposalRecoveryJointRecall cut.trace).length = cut.trace.length := by
    have semantic := congrArg List.length (setup.proposalRecoveryJointRecall_semantic cut.trace)
    simpa only [List.length_map, setup.recoveryJointRecall_length,
      setup.proposalRecoveryEraseTrace_length] using semantic
  simp only [History.extend, Setup.proposalRecoveryJointRecall, Trace.length,
    List.getElem?_take_of_succ, List.reverse_cons,
    List.getElem?_append_right (by rw [List.length_reverse, recallLength]),
    List.length_reverse, recallLength, Nat.sub_self, List.getElem?_cons_zero] at row
  rw [row, Option.map_some] at selected
  have semanticChoice := Option.some.inj selected
  have ownSupport := marginals who
  rw [ordinary] at ownSupport
  obtain ⟨sampled, _sampledSupport, sampleEq⟩ := (PMF.mem_support_map_iff ..).mp ownSupport
  have own : choices who = encode value := by
    have semantic : (encode sampled).val.map ProposalRecoveryMove.semantic =
        CommitRecoveryMove.lift (decodeEventAction setup.program event
          (cast (congrArg EventField.Action binding.symm) (.success value))) :=
      (congrArg (fun choice => choice.val.map ProposalRecoveryMove.semantic) sampleEq).trans
        semanticChoice
    have data := encoded sampled
    cases decoded : decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm) (.success value)) with
    | none =>
      rw [semantic, decoded] at data
      simp only [CommitRecoveryMove.lift, Option.map_none, phaseRecoveryBindingData,
        Option.elim_none, Bool.false_eq_true, ↓reduceIte, Option.bind_none,
        Option.map_none, Option.getD_none, Prod.mk.injEq, reduceCtorEq, false_and] at data
    | some action =>
      have back := encodeEventAction?_decodeEventAction_eq_some setup.program event
        (cast (congrArg EventField.Action binding.symm) (.success value)) action decoded
      have observed : phaseRecoveryBindingData setup .concurrent event who payload binding
          ((encode sampled).val.map ProposalRecoveryMove.semantic) = (.success value, false) := by
        rw [semantic, decoded]
        simp only [CommitRecoveryMove.lift, Option.map_some, phaseRecoveryBindingData,
          Option.elim_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some, back,
          Option.map_some, Option.getD_some, cast_cast, cast_eq]
      have same : sampled = value :=
        PublicationResult.success.inj (congrArg Prod.fst (data.symm.trans observed))
      exact sampleEq.symm.trans (congrArg encode same)
  have forcedDrawn : choices ∈ (independentProduct fun owner => forced owner
      (setup.proposalRecoveryModel.infoOf owner cut.trace)).support := by
    apply (independentProduct_support_iff _ _).mpr
    intro owner
    by_cases focal : owner = who
    · subst owner
      simpa only [forced, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
        PMF.mem_support_pure_iff] using own
    · simpa only [forced, Profile.update_of_ne _ _ focal] using marginals owner
  have forcedStep : cut.extend _ moved ∈
      (setup.proposalRecoveryModel.runBehavioralFrom forced 1 cut).support := by
    rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_localStep]
    apply (PMF.mem_support_bind_iff ..).mpr
    refine ⟨_, (PMF.mem_support_bind_iff ..).mpr ⟨choices, forcedDrawn, localOriginal⟩, ?_⟩
    exact (PMF.mem_support_pure_iff ..).mpr rfl
  exact (PMF.mem_support_bind_iff ..).mpr ⟨_, forcedStep, tail⟩

open Classical in
/-- The full common source site of a positive original annotated summand is
the site of the actual qualified binding package. -/
theorem positive_original_annotated_site
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = site.1)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        event payload clean.binding)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 := by
  obtain ⟨foreign, entry, common⟩ := positive_original_annotated_information setup values
    implementation operational fullValues sourceProfile nativeProfile who control trace active
      tape target cut finished word canonicalSupported event payload clean value positive
  have nativeInformation : ((nativeMenu).information
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).infoOf who
        (sourceCutTrace setup implementation trace) = site.1 := by
    change ((nativeMenu).signals
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).infoOf who
        (sourceCutTrace setup implementation trace) = site.1
    rw [(nativeMenu).info]
    have direct := information
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = site.1 at direct
    rw [(nativeMenu).info] at direct
    exact direct
  exact common.1.trans (source.actualCut control (sourceCutTrace setup implementation trace)
    (entry.canonicalCut setup values implementation operational fullValues control trace
      who active event payload clean foreign) nativeInformation)

open Classical in
/-- The actual original annotated atom supports the qualified package's
encoded proper choice at its full common source information. -/
private theorem positive_original_annotated_encoded_support
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = site.1)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        event payload clean.binding)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    ∃ same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1,
      finished ∈ (sourceForcedBlock setup values who cut
        (same.symm ▸ source.encode value)).support := by
  classical
  obtain ⟨foreign, entry, common, fuel, selectedRow⟩ := positive_original_annotated_information
    setup values implementation operational fullValues sourceProfile nativeProfile who control
      trace active tape target cut finished word canonicalSupported event payload clean value
        positive
  have nativeInformation : ((nativeMenu).information
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).infoOf who
        (sourceCutTrace setup implementation trace) = site.1 := by
    change ((nativeMenu).signals
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).infoOf who
        (sourceCutTrace setup implementation trace) = site.1
    rw [(nativeMenu).info]
    have direct := information
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = site.1 at direct
    rw [(nativeMenu).info] at direct
    exact direct
  have same := common.trans (source.actualCut control (sourceCutTrace setup implementation trace)
    (entry.canonicalCut setup values implementation operational fullValues control trace
      who active event payload clean foreign) nativeInformation)
  let encode : L.Val payload → setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who cut.trace) :=
    fun value => same.symm ▸ source.encode value
  let law := (values who (setup.proposalRecoveryQuery who source.site.1)).map
    (fun sampled => phaseRecoveryDomainValue setup .concurrent event who payload clean.binding
      sampled.val.val)
  have castVal {first last : setup.proposalRecoveryModel.InfoState who} (equal : first = last)
      (choice : setup.proposalRecoveryModel.Choice who first) :
      (equal ▸ choice).val = choice.val := by
    cases equal
    rfl
  have castPolicy {first last : setup.proposalRecoveryModel.InfoState who} (equal : first = last)
      (policy : setup.proposalRecoveryModel.BehavioralPolicy who) :
      (policy first).map (fun choice => equal ▸ choice) = policy last := by
    cases equal
    exact PMF.map_id _
  have ordinary : sourceUnflaggedStrategy setup values who
      (setup.proposalRecoveryModel.infoOf who cut.trace) = law.map encode := by
    have moved := congrArg (fun distribution : PMF
        (setup.proposalRecoveryModel.Choice who source.site.1) =>
      distribution.map (fun choice => same.symm ▸ choice)) source.ordinary
    rw [castPolicy same.symm (sourceUnflaggedStrategy setup values who), PMF.map_comp] at moved
    simpa only [law, encode, PMF.map_comp, Function.comp_def] using moved
  have encoded : ∀ value, phaseRecoveryBindingData setup .concurrent event who payload
      clean.binding ((encode value).val.map ProposalRecoveryMove.semantic) =
        (.success value, false) := by
    intro value
    simpa only [encode, castVal] using source.encoded value
  have nativeObserved : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape target cut finished word canonicalSupported
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        nativeObserved event payload clean value positive
  obtain ⟨g, _first, rest⟩ := (PMF.mem_support_bind_iff ..).mp pair.2.2.1
  obtain ⟨G, tail, pairEq⟩ := (PMF.mem_support_map_iff ..).mp rest
  have cutEq : g = cut := congrArg Prod.fst pairEq
  have finishedEq : G = finished := congrArg Prod.snd pairEq
  subst g
  subst G
  have length := (selected_binding_observation setup implementation operational control trace
    who event payload clean.binding entry value).1
  have inside : event.val - control.execution.application.attempt.phase < entry.block.length := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    have low : control.execution.application.attempt.phase = entry.phase.low := by
      simp only [PhaseRuntimeState.attempt, phases, List.head?_cons,
        Option.map_some, Option.getD_some]
    have bounds := (entry.phase.mem_events event).mp entry.inside
    have size := entry.size
    omega
  have geometry := positive_original_annotated_geometry setup values implementation operational
    fullValues sourceProfile nativeProfile who control trace active tape target cut finished word
      canonicalSupported event payload clean value positive
  have progress : cut.trace.length < finished.trace.length := by
    have cutClock := geometry.2.2.2.1
    have finishedClock := geometry.2.2.2.2
    rw [length] at finishedClock
    omega
  have remaining : finished ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) (sourceCommitFuel setup cut) cut).support := by
    simpa only [length, fuel] using tail
  exact ⟨same, ordinary_encoded_forced_support setup values who event payload clean.binding
    cut finished law encode ordinary encoded value (by omega) progress remaining selectedRow⟩

open Classical in
/-- A positive original summand has the actual qualified source information,
positive encoded continuation, good retained source interval and literal static
depths. Its supported structural word is unique at this original native history. -/
theorem positive_original_annotated_coverage
    (operational : implementation.Operational)
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = site.1)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        event payload clean.binding)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    ∃ same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1,
      setup.proposalRecoveryClosedKey who target = setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational ⟨some control, trace⟩) ∧
      setup.proposalRecoveryForeignGood who target ∧
      setup.proposalRecoveryForeignGood who cut ∧
      setup.proposalRecoveryForeignGood who finished ∧
      0 < setup.proposalRecoveryModel.historyReachWeight sourceProfile cut ∧
      TracePrefix target.trace cut.trace ∧ TracePrefix cut.trace finished.trace ∧
      cut.trace.length = target.trace.length +
        (event.val - control.execution.application.attempt.phase) ∧
      finished.trace.length = target.trace.length +
        (SourceProgram.commitPhase checkpoint.residual.tail).block.length ∧
      0 < sourceForcedBlock setup values who cut (same.symm ▸ source.encode value) finished ∧
      (word, true) ∈ (ordinaryForeignJoint setup values implementation operational who
        ⟨some control, trace⟩ target).support ∧
      ∀ other, (other, true) ∈ (ordinaryForeignJoint setup values implementation operational who
        ⟨some control, trace⟩ target).support →
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event
          payload target other value (cut, finished) ≠ 0 → other = word := by
  intro checkpoint
  have canonicalPositive := prescribed_source_history_positive setup values scale sourceBad
    scalePositive scaleBelow sourceBadPositive sourceBadBelow fullValues sourceProfile
      sourcePrescribed (canonicalSource setup implementation operational ⟨some control, trace⟩)
  have canonicalSupported := ne_of_gt canonicalPositive
  obtain ⟨same, encodedSupport⟩ := positive_original_annotated_encoded_support setup values
    implementation operational fullValues sourceProfile nativeProfile who site control trace active
      information tape target cut finished word canonicalSupported event payload clean source value
        positive
  have geometry := positive_original_annotated_geometry setup values implementation operational
    fullValues sourceProfile nativeProfile who control trace active tape target cut finished word
      canonicalSupported event payload clean value positive
  have nativeObserved : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
  have pair := positive_original_annotated_pair setup values implementation operational fullValues
    sourceProfile nativeProfile who control trace tape target cut finished word canonicalSupported
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        nativeObserved event payload clean value positive
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
  have annotation := annotatedPrefixWeight_support setup values implementation operational
    sourceProfile nativeProfile who ⟨some control, trace⟩ tape target word canonicalSupported
      prefixPositive
  obtain ⟨_read, _wordEq, unique, _structural⟩ := pair.2.2.2.2.2.2
  exact ⟨same, pair.1, geometry.1, geometry.2.1, geometry.2.2.1,
    prescribed_source_history_positive setup values scale sourceBad scalePositive scaleBelow
      sourceBadPositive sourceBadBelow fullValues sourceProfile sourcePrescribed cut,
    pair.2.2.2.2.1, pair.2.2.2.2.2.1, geometry.2.2.2.1, geometry.2.2.2.2,
    pos_iff_ne_zero.mpr ((PMF.mem_support_iff ..).mp encodedSupport), annotation.2.2, unique⟩

open Classical in
/-- Permanent acceptance of an immutable signed coordinate is fixed by the
retained mechanical input, even after automatic close or rollback. -/
theorem bindingAccepted_iff_of_mechanicalProjection
    (who : Player) (first second : (nativeApplication).Control)
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second))
    (coordinate : CommitAttemptEvent (serviceGraph setup .concurrent)) (owner : Player) :
    PhaseService.BindingAccepted implementation.runtime implementation.leaks coordinate owner
        first.execution ↔
      PhaseService.BindingAccepted implementation.runtime implementation.leaks coordinate owner
        second.execution := by
  have projection := same
  simp only [mechanicalProjection, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at projection
  obtain ⟨_remaining, _actor, _application, network, receipts, _focal, _fresh,
    _environment, _own⟩ := projection
  have inputs := congrArg (fun view : MessageNetwork.PublicView Player
    (CommitAttemptPacket (serviceGraph setup .concurrent)) => view.inputs) network
  change first.execution.network.inputs = second.execution.network.inputs at inputs
  simp only [PhaseService.BindingAccepted, inputs, receipts]

omit [Fintype Player] in
/-- The closed source key preserves every historical signed binding value,
including values from canceled commitment visits. -/
theorem sourceHandleMeaning_eq_of_closed_key
    (wellFormed : setup.WellFormed) (who : Player)
    (first second : CommitRecoveryState setup.program)
    (firstTrace : setup.proposalRecoveryProtocol.Trace (some first))
    (secondTrace : setup.proposalRecoveryProtocol.Trace (some second))
    (same : setup.proposalRecoveryClosedKey who ⟨some first, firstTrace⟩ =
      setup.proposalRecoveryClosedKey who ⟨some second, secondTrace⟩)
    (firstGood : setup.proposalRecoveryForeignGood who ⟨some first, firstTrace⟩)
    (secondGood : setup.proposalRecoveryForeignGood who ⟨some second, secondTrace⟩)
    (reference : (nativeApplication).Control)
    (handle : Handle (serviceGraph setup .concurrent)) :
    sourceHandleMeaning setup implementation ⟨some first, firstTrace⟩ reference handle =
      sourceHandleMeaning setup implementation ⟨some second, secondTrace⟩ reference handle := by
  classical
  have base : ProtocolState.base setup.program first.point =
      ProtocolState.base setup.program second.point := by
    have baseKey := congrArg Prod.fst same
    exact Option.some.inj baseKey
  have reads (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
      (owner : Player) (payload : L.Ty)
      (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload) :=
    sourceBindingAt_closed_key setup wellFormed who owner attempt event payload binding
      first second firstTrace secondTrace same firstGood secondGood
  cases slot : handle.2 with
  | «initial» _serial =>
    simp only [sourceHandleMeaning, slot, Option.bind_some, base]
  | prepared _serial =>
    simp only [sourceHandleMeaning, slot, reads]

open Classical in
/-- Equal retained public inputs identify the source meaning of every signed
handle, independently of the raw aliases in the two owner recalls. -/
private theorem sourceHandleMeaning_eq_of_mechanicalProjection
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (first second : (nativeApplication).Control)
    (firstTrace : (nativeProtocol).Trace (some first))
    (secondTrace : (nativeProtocol).Trace (some second))
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second))
    (handle : Handle (serviceGraph setup .concurrent)) :
    sourceHandleMeaning setup implementation target first handle =
      sourceHandleMeaning setup implementation target second handle := by
  classical
  have outputs := (mechanicalProjection_foreign_input setup implementation who handle.1
    first second firstTrace secondTrace same).2.1
  let locate := fun message : Message Player
      (CommitAttemptPacket (serviceGraph setup .concurrent)) =>
    match message.payload.packet.call with
    | .commitment event candidate =>
        if candidate = handle then
          match binding : (serviceGraph setup .concurrent).outputLayout event with
          | .binding owner payload =>
              (sourceBindingAt setup message.payload.attempt event owner payload binding
                target.trace).map fun value => (⟨payload, value⟩ : Raw L)
          | _ => none
        else none
    | _ => none
  have normalize (records : List (nativeApplication).PlayerEntry) :
      records.findSome? (fun record => record.emitted.bind locate) =
        ((nativeApplication).outputs records).findSome? locate := by
    unfold ReactiveApplication.outputs
    induction records with
    | nil => rfl
    | cons record records ih =>
      simp only [List.findSome?_cons, List.filterMap_cons]
      cases emitted : record.emitted with
      | none =>
        simpa only [emitted, Option.bind_none, Option.orElse_none] using ih
      | some message =>
        cases found : locate message with
        | none =>
          simpa only [emitted, Option.bind_some, List.findSome?_cons, found] using ih
        | some raw =>
          simp only [Option.bind_some, List.findSome?_cons, found]
  cases slot : handle.2 with
  | «initial» _serial => simp only [sourceHandleMeaning, slot]
  | prepared _serial =>
    simp only [sourceHandleMeaning, slot]
    change (first.execution.recall handle.1).findSome?
        (fun record => record.emitted.bind locate) =
      (second.execution.recall handle.1).findSome?
        (fun record => record.emitted.bind locate)
    rw [normalize, normalize, outputs]

open Classical in
/-- A common signed call and retained public input select the same auxiliary
handle on both native histories. -/
theorem sourceReplayLostSlot_eq_of_signed_call
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (first second : (nativeApplication).Control)
    (firstTrace : (nativeProtocol).Trace (some first))
    (secondTrace : (nativeProtocol).Trace (some second))
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second))
    (firstAction secondAction : (nativeApplication).Action)
    (packet : firstAction.transmission.map (fun material => material.call.packet) =
      secondAction.transmission.map (fun material => material.call.packet)) :
    sourceReplayLostSlot setup implementation target first firstAction =
      sourceReplayLostSlot setup implementation target second secondAction := by
  classical
  have meaning := sourceHandleMeaning_eq_of_mechanicalProjection setup implementation who target
    first second firstTrace secondTrace same
  cases sentFirst : firstAction.transmission with
  | none =>
    cases sentSecond : secondAction.transmission with
    | none => simp only [sourceReplayLostSlot, sentFirst, sentSecond, Option.bind_none]
    | some material =>
      simp only [sentFirst, sentSecond, Option.map_none, Option.map_some,
        reduceCtorEq] at packet
  | some material =>
    cases sentSecond : secondAction.transmission with
    | none =>
      simp only [sentFirst, sentSecond, Option.map_none, Option.map_some,
        reduceCtorEq] at packet
    | some other =>
      have calls := Option.some.inj (by
        simpa only [sentFirst, sentSecond, Option.map_some] using packet)
      simp only [sourceReplayLostSlot, sentFirst, sentSecond, Option.bind_some, calls, meaning]

/-- Every actual history with the retained mechanical word has a literal
callback readback, with one coordinate at every original raw transition. -/
theorem sourceRawReplayReadback_of_mechanicalWord
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (original actual : (nativeProtocol).History)
    (same : mechanicalWord setup implementation who original.trace =
      mechanicalWord setup implementation who actual.trace) :
    ∃ script : List (RawReplayChoice setup implementation),
      sourceRawReplayReadback setup implementation who target reference original actual =
        some script ∧ script.length = original.trace.length := by
  classical
  rcases original with ⟨state, trace⟩
  induction trace generalizing actual with
  | start =>
    refine ⟨[], ?_, rfl⟩
    simp only [sourceRawReplayReadback]
  | @extend before after prior joint legal moved ih =>
    rcases actual with ⟨actualState, actualTrace⟩
    cases actualTrace with
    | start =>
      have length := congrArg List.length same
      simp only [mechanicalWord_length, Trace.length] at length
      omega
    | @extend otherBefore otherAfter other otherJoint otherLegal otherMoved =>
      have length := congrArg List.length same
      simp only [mechanicalWord_length, Trace.length] at length
      have prefixLength : (mechanicalWord setup implementation who prior).length =
          (mechanicalWord setup implementation who other).length := by
        simp only [mechanicalWord_length]
        omega
      simp only [mechanicalWord] at same
      obtain ⟨samePrior, _sameAfter⟩ := List.append_inj same prefixLength
      obtain ⟨script, read, count⟩ := ih ⟨otherBefore, other⟩ samePrior
      have last := congrArg List.getLast? samePrior
      rw [mechanicalWord_last, mechanicalWord_last] at last
      have projection := congrArg Subtype.val (Option.some.inj last)
      cases before with
      | none =>
        refine ⟨(none, none) :: script, ?_, congrArg Nat.succ count⟩
        simp only [sourceRawReplayReadback, History.prior, read, Option.bind_some,
          ReactiveApplication.actor, Option.bind_none]
      | some before =>
        cases acting : before.actor with
        | none =>
          refine ⟨(none, none) :: script, ?_, congrArg Nat.succ count⟩
          simp only [sourceRawReplayReadback, History.prior, read, Option.bind_some,
            ReactiveApplication.actor, acting]
        | some owner =>
          by_cases focal : owner = who
          · refine ⟨(none, none) :: script, ?_, congrArg Nat.succ count⟩
            simp only [sourceRawReplayReadback, History.prior, read, Option.bind_some,
              ReactiveApplication.actor, acting, focal, ↓reduceIte]
          · cases otherBefore with
            | none =>
              simp only [mechanicalProjection, Option.map_some, Option.map_none,
                reduceCtorEq] at projection
            | some current =>
              simp only [mechanicalProjection, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at projection
              have actualActing : current.actor = some owner := projection.2.1.symm.trans acting
              obtain ⟨action, selected⟩ : ∃ action : (nativeApplication).Action,
                  otherJoint owner = some action := by
                have offered := otherLegal.2 owner
                cases chosen : otherJoint owner with
                | none =>
                  rw [chosen] at offered
                  exact (offered (by exact actualActing)).elim
                | some action => exact ⟨action, rfl⟩
              have ending : actualState = some (⟨current.remaining, none,
                  current.execution.respond nativeApplication owner action⟩ :
                    (nativeApplication).Control) := by
                have reached := otherMoved
                change actualState ∈ ((nativeApplication).transition nativeInitial
                  implementation.horizon implementation.scheduler (some current)
                    otherJoint).support at reached
                simpa only [ReactiveApplication.transition, actualActing, selected,
                  Option.getD_some, PMF.mem_support_pure_iff] using reached
              have latest := sourceReplayLastAction_respond setup implementation owner current
                action ⟨actualState, other.extend otherJoint otherLegal otherMoved⟩ ending
              let tag := (sourceReplayLostSlot setup implementation target reference
                ((joint owner).getD ⟨none⟩)).bind fun handle =>
                  (action.transmission.bind PhaseProposal.bindingPreparation).map
                    (fun raw => (handle, raw))
              refine ⟨(tag, some action) :: script, ?_, congrArg Nat.succ count⟩
              simp only [sourceRawReplayReadback, History.prior, read, Option.bind_some,
                ReactiveApplication.actor, acting, focal, ↓reduceIte, latest,
                Option.map_some]
              rfl

/-- Every actual prescribed callback of a positive native history lies in its
literal response law and in the alias kernel at that same complete input. -/
private theorem sourceReplay_prescribed_callback_support
    (rates : PhaseProposalRates)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (positive : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight
        (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan nativeInitial
            implementation.horizon implementation.scheduler values rates) ⟨some control, trace⟩ ≠ 0)
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (after : (nativeProtocol).State) (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (retained : TracePrefix (prior.extend joint legal moved) trace)
    (owner : Player) (acting : before.actor = some owner)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (before.execution.recall owner)
        (before.execution.observe nativeApplication owner))
    (selected : joint owner = some response.val) :
    response ∈ (phaseProposalReferenceResponses setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values rates owner
        (before.execution.recall owner)
          (before.execution.observe nativeApplication owner)).support ∧
    ∀ tag, (tag, some response.val) ∈
      (sourceReplayAliases setup implementation rates.aliases owner before.execution tag
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (before.execution.recall owner)
            (before.execution.observe nativeApplication owner) response)).support := by
  classical
  let profile := phaseProposalReferenceStrategy setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan nativeInitial
      implementation.horizon implementation.scheduler values rates
  let model := (nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler
  have realPositive := ENNReal.toReal_pos positive
    (model.historyReachWeight_ne_top profile ⟨some control, trace⟩)
  have atStep : (model.infoOf owner prior, response.val) ∈
      model.ownPlay owner (prior.extend joint legal moved) := by
    rw [InfoSignals.ownPlay_extend, selected]
    exact List.mem_cons_self
  have atFinal := (model.ownPlay_isSuffix_of_reachesWithin owner
    retained.reachesWithin).subset atStep
  have supported := model.ownPlay_supported_of_historyReach_pos profile owner trace
    realPositive atFinal
  have information : model.infoOf owner prior =
      some (before.execution.recall owner, before.execution.observe nativeApplication owner) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf owner prior = _
    have observed := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler owner prior
    simpa only [ReactiveApplication.observe, acting, ↓reduceIte] using observed
  rw [information] at supported
  dsimp only [profile] at supported
  rw [phaseProposalReferenceStrategy_map_val] at supported
  obtain ⟨action, physical, same⟩ := (PMF.mem_support_map_iff ..).mp supported
  have actionEq : action = response.val := Option.some.inj same
  rw [actionEq] at physical
  unfold phaseProposalReferencePolicy at physical
  obtain ⟨chosen, chosenSupport, same⟩ := (PMF.mem_support_map_iff ..).mp physical
  have chosenEq : chosen = response := Subtype.ext same
  subst chosen
  refine ⟨chosenSupport, ?_⟩
  unfold phaseProposalReferenceResponses PhaseProposal.splitResponseLaw at chosenSupport
  obtain ⟨selectedClass, _classSupport, aliasSupport⟩ :=
    (PMF.mem_support_bind_iff ..).mp chosenSupport
  have classEq := PMF.splitKernel_supported _ _ _ _ _ _ _ _ aliasSupport
  intro tag
  unfold sourceReplayAliases
  apply (PMF.mem_support_map_iff ..).mpr
  refine ⟨response, ?_, rfl⟩
  rw [← classEq] at aliasSupport
  exact aliasSupport

/-- A positive actual proper callback uses a value in its same-input source
draw. Totalization of unrelated private menus introduces no extra value here. -/
private theorem sourceReplay_prescribed_value_support
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates)
    (waitPositive : 0 < rates.waiting.val) (waitBelow : rates.waiting.val < 1)
    (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent owner)
    (queried : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) = some key)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (supported : response ∈ (phaseProposalReferenceResponses setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)).support)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : response.val.transmission = some material)
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L))
    (serial : Nat)
    (packet : material.call.packet = .commitment event (owner, .prepared serial)) :
    value ∈ ((values owner key).map (fun sampled => phaseRecoveryDomainValue setup .concurrent
      event owner payload binding sampled.val.val)).support := by
  have atom := (foreign_binding_response_atom setup values implementation operational fullValues
    rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution
      trace event payload binding request key queried response material transmitted value
        prepared serial packet).2
  change _ ≠ 0 at supported ⊢
  rw [atom] at supported
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp supported).1).2

/-- A silent or opening callback has no binding preparation coordinate, so
its actual signed packet already determines its alias class. -/
private theorem sourceReplay_nonbinding_alias_supported
    (scale : Set.Icc (0 : ℝ) 1) (positive : 0 < scale.val)
    (owner : Player) (execution : (nativeApplication).Execution)
    (response canonical : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (origin : canonical.val = ⟨none⟩ ∨
      ∃ (event : (serviceGraph setup .concurrent).EventId)
        (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L),
        canonical.val = PhaseCount.phaseOpeningResponse implementation.runtime
          implementation.leaks event handle raw)
    (packets : response.val.transmission.map (fun material =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) material).payload) =
      canonical.val.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner) material).payload)) :
    (none, some response.val) ∈ (sourceReplayAliases setup implementation scale owner execution
      none (PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) canonical)).support := by
  have projected := congrArg
    (fun wire : Option (CommitAttemptPacket (serviceGraph setup .concurrent)) =>
    wire.map fun packet => packet.packet.call) packets
  have calls : response.val.transmission.map (fun material => material.call.packet) =
      canonical.val.transmission.map (fun material => material.call.packet) := by
    simp only [Option.map_map] at projected
    have projectCall : (fun material : WitnessedSubmission (serviceGraph setup .concurrent) =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner)
            material).payload.packet.call) = (fun material => material.call.packet) := by
      funext material
      exact PhaseCount.maskPacket_call _ _
    change response.val.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner)
            material).payload.packet.call) =
      canonical.val.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner)
            material).payload.packet.call) at projected
    have left := congrArg (fun project => response.val.transmission.map project) projectCall
    have right := congrArg (fun project => canonical.val.transmission.map project) projectCall
    exact left.symm.trans (projected.trans right)
  have preparations : response.val.transmission.bind PhaseProposal.bindingPreparation =
      canonical.val.transmission.bind PhaseProposal.bindingPreparation := by
    rcases origin with silent | ⟨event, handle, raw, opened⟩
    · rw [silent] at calls ⊢
      change response.val.transmission.map (fun material => material.call.packet) = none at calls
      have absent : response.val.transmission = none := Option.map_eq_none_iff.mp calls
      rw [absent]
    · rw [opened] at calls ⊢
      change response.val.transmission.map (fun material => material.call.packet) =
        some (.opening event handle raw) at calls
      obtain ⟨material, sent, call⟩ := Option.map_eq_some_iff.mp calls
      rw [sent]
      simp only [Option.bind_some, PhaseProposal.bindingPreparation, call,
        PhaseCount.phaseOpeningResponse, disclosureSubmission]
  have classes : PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) response =
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) canonical := by
    apply Subtype.ext
    exact Prod.ext preparations packets
  unfold sourceReplayAliases
  apply (PMF.mem_support_map_iff ..).mpr
  refine ⟨response, ?_, rfl⟩
  exact PMF.splitKernel_fullFiber _ _ _ scale.val scale.property.1 scale.property.2
    positive _ response classes

/-- The same actual signed packet and typed preparation select the binding
alias at the literal callback input. Private evidence may differ. -/
private theorem sourceReplay_binding_alias_supported
    (scale : Set.Icc (0 : ℝ) 1) (positive : 0 < scale.val)
    (owner : Player) (execution : (nativeApplication).Execution)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (serial : Nat) (value : L.Val payload)
    (response canonical : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (canonicalEq : canonical.val = phaseBindingResponse implementation.runtime
      implementation.leaks owner event payload (.success value) serial)
    (prepared : response.val.transmission.bind PhaseProposal.bindingPreparation =
      some (⟨payload, value⟩ : Raw L))
    (packets : response.val.transmission.map (fun material =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) material).payload) =
      canonical.val.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner) material).payload))
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L)) :
    (tag, some response.val) ∈ (sourceReplayAliases setup implementation scale owner execution
      tag (PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) canonical)).support := by
  have classes : PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) response =
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) canonical := by
    apply Subtype.ext
    apply Prod.ext
    · change response.val.transmission.bind PhaseProposal.bindingPreparation =
        canonical.val.transmission.bind PhaseProposal.bindingPreparation
      rw [prepared, canonicalEq]
      simp only [phaseBindingResponse, Option.bind_some, PhaseProposal.bindingPreparation,
        binding, Raw.as?_mk, Option.map_some]
    · exact packets
  unfold sourceReplayAliases
  apply (PMF.mem_support_map_iff ..).mpr
  refine ⟨response, ?_, rfl⟩
  exact PMF.splitKernel_fullFiber _ _ _ scale.val scale.property.1 scale.property.2
    positive _ response classes

/-- A positive actual binding callback lies in the literal lost-value draw
followed by aliases at that same physical input. -/
private theorem sourceReplay_lost_binding_supported
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates)
    (waitPositive : 0 < rates.waiting.val) (waitBelow : rates.waiting.val < 1)
    (slotPositive : 0 < rates.slots.val) (aliasPositive : 0 < rates.aliases.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent owner)
    (queried : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) = some key)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (supported : response ∈ (phaseProposalReferenceResponses setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)).support)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : response.val.transmission = some material)
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L))
    (serial : Nat)
    (packet : material.call.packet = .commitment event (owner, .prepared serial))
    (canonical : ∀ _value : L.Val payload,
      PhaseProposal.Response implementation.runtime implementation.leaks implementation.bounds
        owner (execution.recall owner) (execution.observe nativeApplication owner))
    (canonicalEq : ∀ value, (canonical value).val = phaseBindingResponse implementation.runtime
      implementation.leaks owner event payload (.success value) serial)
    (packets : response.val.transmission.map (fun material =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) material).payload) =
      (canonical value).val.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner) material).payload)) :
    (some ((owner, .prepared serial), (⟨payload, value⟩ : Raw L)), some response.val) ∈
      (((values owner key).map (fun sampled => phaseRecoveryDomainValue setup .concurrent
        event owner payload binding sampled.val.val)).bind fun drawn =>
          sourceReplayAliases setup implementation rates.aliases owner execution
            (some ((owner, .prepared serial), (⟨payload, drawn⟩ : Raw L)))
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) (canonical drawn))).support := by
  have drawn := sourceReplay_prescribed_value_support setup values implementation operational
    fullValues rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner
      execution trace event payload binding request key queried response supported material
        transmitted value prepared serial packet
  apply (PMF.mem_support_bind_iff ..).mpr
  refine ⟨value, drawn, ?_⟩
  apply sourceReplay_binding_alias_supported setup implementation rates.aliases aliasPositive
    owner execution event payload binding serial value response (canonical value)
      (canonicalEq value) _ packets
  rw [transmitted]
  exact prepared

/-- A literal binding callback leaves its exact fresh preparation record in
every later own recall, before or after inclusion of its emitted packet. -/
private theorem sourceReplay_retained_binding_record
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (retained : TracePrefix (prior.extend joint legal moved) trace)
    (owner : Player) (acting : before.actor = some owner)
    (event : (serviceGraph setup .concurrent).EventId) (serial : Nat)
    (opening : Option (Raw L)) (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (selected : joint owner =
      some ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩) :
    ∃ record ∈ control.execution.recall owner,
      record.action = ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      record.beforeView.application.1.candidates (.prepared serial) = .fresh := by
  have offered := legal.2 owner
  rw [selected] at offered
  have initialEq : ((setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan)) = nativeInitial := by
    rw [PMF.map_comp]
    rfl
  have originalTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace (some before) := by
    rw [initialEq]
    exact prior
  have fresh := PhaseCount.onePacket_binding_fresh implementation.runtime implementation.leaks
    implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler originalTrace owner event serial
        opening evidence offered.2
  let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
  let action : (nativeApplication).Action := ⟨some material⟩
  let message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)) :=
    ⟨(owner, before.execution.network.nextSerial owner),
      (nativeApplication).packet ((nativeApplication).submit before.execution.application owner
        material) owner (before.execution.network.known owner) material⟩
  let record : (nativeApplication).PlayerEntry :=
    ⟨before.execution.observe nativeApplication owner, action, some message⟩
  have ending : after = { before with
      actor := none
      execution := before.execution.respond nativeApplication owner action } := by
    change some after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) joint).support at moved
    simpa only [ReactiveApplication.transition, acting, selected, Option.getD_some,
      PMF.mem_support_pure_iff, Option.some.injEq] using moved
  have immediate : record ∈ after.execution.recall owner := by
    rw [ending]
    simpa only [ReactiveApplication.Execution.respond, action, ↓reduceIte, record,
      message, material, MessageNetwork.submit] using
        (List.mem_append_right (before.execution.recall owner) (List.mem_singleton_self record))
  have recalled := (nativeApplication).reaches_recall_prefix nativeInitial implementation.horizon
    implementation.scheduler ((nativeMenu).reaches_raw nativeInitial implementation.horizon
      implementation.scheduler retained.reachesWithin) after control rfl rfl owner
  exact ⟨record, recalled.subset immediate, rfl, fresh⟩

/-- The immutable successful result of a recorded fresh binding determines
its literal typed preparation, before any private evidence aliases are erased. -/
private theorem sourceReplay_recorded_preparation
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (serial : Nat) (opening : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (declared : record.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : record.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (value : L.Val payload)
    (result : control.execution.application.current.native.bindingResult
      (owner, .prepared serial) payload = .success value) :
    record.action.transmission.bind PhaseProposal.bindingPreparation =
      some (⟨payload, value⟩ : Raw L) := by
  have physical := phase_recorded_material_binding_result implementation.runtime
    implementation.leaks (nativeMenu) nativeInitial implementation.horizon
      implementation.scheduler control trace owner event payload serial opening evidence
        record recorded declared fresh
  have typed := physical.symm.trans result
  have recovered : opening.bind (fun raw => raw.as? payload) = some value := by
    cases drawn : opening.bind (fun raw => raw.as? payload) with
    | none =>
      simp only [drawn, Option.elim_none] at typed
      cases typed
    | some actual =>
      simp only [drawn, Option.elim_some] at typed
      exact congrArg some (PublicationResult.success.inj typed)
  rw [declared]
  simp only [PhaseProposal.bindingPreparation, binding, Option.bind_some]
  change ((opening.bind fun raw => raw.as? payload).map
    fun raw => (⟨payload, raw⟩ : Raw L)) = some (⟨payload, value⟩ : Raw L)
  rw [recovered]
  rfl

/-- A source-valued handle in a positive original annotation fixes the typed
material of its actual callback, including origins still pending or canceled. -/
private theorem positive_original_annotated_callback_preparation
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target cut finished : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (value : L.Val payload)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word *
        (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value (cut, finished) ≠ 0)
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (retained : TracePrefix (prior.extend joint legal moved) trace)
    (owner : Player) (acting : before.actor = some owner)
    (bindingEvent : (serviceGraph setup .concurrent).EventId) (bindingPayload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout bindingEvent =
      .binding owner bindingPayload)
    (serial : Nat) (opening : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (selected : joint owner =
      some ⟨some ⟨⟨.commitment bindingEvent (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (recovered : L.Val bindingPayload)
    (meaning : sourceHandleMeaning setup implementation finished control
      (owner, .prepared serial) = some (⟨bindingPayload, recovered⟩ : Raw L)) :
    (⟨some ⟨⟨.commitment bindingEvent (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (nativeApplication).Action).transmission.bind PhaseProposal.bindingPreparation =
        some (⟨bindingPayload, recovered⟩ : Raw L) := by
  have registered := positive_original_annotated_prepared_value setup values implementation
    operational fullValues sourceProfile nativeProfile who control trace active tape target cut
      finished word canonicalSupported event payload clean value positive
        (owner, .prepared serial) serial rfl (⟨bindingPayload, recovered⟩ : Raw L) meaning
  have result := (State.bindingResult_eq_success_iff control.execution.application.current.native
    (owner, .prepared serial) bindingPayload recovered).mpr registered
  obtain ⟨record, recorded, declared, fresh⟩ := sourceReplay_retained_binding_record setup
    implementation control trace before after prior joint legal moved retained owner acting
      bindingEvent serial opening evidence selected
  have preparation := sourceReplay_recorded_preparation setup implementation control trace owner
    bindingEvent bindingPayload binding serial opening evidence record recorded declared fresh
      recovered result
  simpa only [declared] using preparation

/-- Replaying a literal supported callback extends an already identical
actual prefix by its own joint and successor, including its raw evidence. -/
private theorem sourceRawReplay_callback_of_actual
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference before : (nativeApplication).Control)
    (after : (nativeProtocol).State)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (owner : Player) (acting : before.actor = some owner)
    (script : List (RawReplayChoice setup implementation))
    (choice : RawReplayChoice setup implementation)
    (actualBefore : (nativeApplication).Control)
    (actualPrior : (nativeProtocol).Trace (some actualBefore))
    (replayed : sourceRawReplay setup implementation who target reference
      ⟨some before, prior⟩ script = some ⟨some actualBefore, actualPrior⟩)
    (actualActing : actualBefore.actor = some owner)
    (actualAfter : (nativeProtocol).State)
    (actualJoint : Player → Option (nativeApplication).Action)
    (actualLegal : (nativeProtocol).Legal (some actualBefore) actualJoint)
    (actualMoved : actualAfter ∈
      ((nativeProtocol).step (some actualBefore) ⟨actualJoint, actualLegal⟩).support)
    (action : (nativeApplication).Action)
    (actualSelected : actualJoint owner = some action)
    (selected : (if owner = who then joint owner else choice.2) = some action) :
    sourceRawReplay setup implementation who target reference
      ⟨after, prior.extend joint legal moved⟩ (choice :: script) =
        some ⟨actualAfter, actualPrior.extend actualJoint actualLegal actualMoved⟩ := by
  classical
  have jointEq : actualJoint = fun player => if player = owner then some action else none := by
    funext player
    by_cases same : player = owner
    · subst player
      simpa only [↓reduceIte] using actualSelected
    · have offered := actualLegal.2 player
      cases chosen : actualJoint player with
      | none => simp only [same, ↓reduceIte]
      | some chosenAction =>
        rw [chosen] at offered
        have impossible : owner = player := by
          simpa only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
            Option.bind_some, actualActing, Option.some.injEq] using offered.1
        exact (same impossible.symm).elim
  have ending : actualAfter = some { actualBefore with
      actor := none
      execution := actualBefore.execution.respond nativeApplication owner action } := by
    change actualAfter ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some actualBefore) actualJoint).support at actualMoved
    simpa only [ReactiveApplication.transition, actualActing, actualSelected, Option.getD_some,
      PMF.mem_support_pure_iff] using actualMoved
  subst actualJoint
  cases ending
  simp only [sourceRawReplay, replayed, Option.bind_some, acting, selected]
  exact sourceReplayAppend_supported setup implementation ⟨some actualBefore, actualPrior⟩
    _ _ actualLegal actualMoved

def SourceRawReplayLaw.coversOriginalAnnotations
    (operational : implementation.Operational)
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (event : (serviceGraph setup .concurrent).EventId)
    (g : setup.proposalRecoveryProtocol.History)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (scale : Set.Icc (0 : ℝ) 1)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩
        reference ⟨some reference, referenceTrace⟩) : Prop :=
      ∀ (nativeBad : Set.Icc (0 : ℝ) 1),
        0 < scale.val → scale.val < 1 → 0 < nativeBad.val → nativeBad.val < 1 →
        (∀ owner key, FullSupport (values owner key)) →
        ∀ (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
          (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control)),
          control.actor = some who →
          ((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).infoOf who trace =
              ((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).infoOf who referenceTrace →
          ∀ (tape : ReservedEpoch.Tape Player implementation.tapeLength)
            (entry : setup.proposalRecoveryProtocol.History)
            (word : SourceProgram.History Player L),
            setup.proposalRecoveryModel.historyReachWeight sourceProfile
              (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0 →
            ∀ (payload : L.Ty)
              (_clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
                (control.execution.observe nativeApplication who) event payload)
              (value : L.Val payload),
              annotatedPrefixWeight setup values implementation operational sourceProfile
                (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan nativeInitial
                    implementation.horizon implementation.scheduler values
                      ⟨nativeBad, scale, scale, scale⟩)
                who ⟨some control, trace⟩ tape entry word *
                  (if bindingAdmissionBit setup implementation who event
                    ⟨some control, trace⟩ tape then 1 else 0) *
                  sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
                    event payload entry word value (g, ⟨some targetCurrent, targetTrace⟩) ≠ 0 →
              mechanicalWord setup implementation who trace =
                mechanicalWord setup implementation who referenceTrace →
              ∃ script ∈ law.choices.support,
                sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
                  reference ⟨some reference, referenceTrace⟩ script =
                    some ⟨some control, trace⟩

/- The source alignment is consumed once, at each actual initialized prefix.
All foreign laws are normalized at that prefix's actual raw input. -/
theorem sourceRawReplay_law
    (operational : implementation.Operational)
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference
      (sourceCutTrace setup implementation referenceTrace) who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (alignment : SourceReplayAlignment (setup := setup) (values := values)
      (implementation := implementation) operational who reference
      referenceTrace event cut g sourceChoice targetCurrent targetTrace)
    (good : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some reference, referenceTrace⟩)
    (scale : Set.Icc (0 : ℝ) 1) :
    ∃ law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩
        reference ⟨some reference, referenceTrace⟩,
      SourceRawReplayLaw.coversOriginalAnnotations setup values implementation operational who
        reference referenceTrace event g targetCurrent targetTrace scale law := by
  classical
  let target : setup.proposalRecoveryProtocol.History := ⟨some targetCurrent, targetTrace⟩
  let fiber (endpoint : (nativeProtocol).History) : Prop :=
    ∃ (nativeBad : Set.Icc (0 : ℝ) 1)
      (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
      (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
      (tape : ReservedEpoch.Tape Player implementation.tapeLength)
      (entry : setup.proposalRecoveryProtocol.History)
      (word : SourceProgram.History Player L) (payload : L.Ty)
      (_clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
        (control.execution.observe nativeApplication who) event payload)
      (value : L.Val payload),
      endpoint = ⟨some control, trace⟩ ∧
      0 < scale.val ∧ scale.val < 1 ∧ 0 < nativeBad.val ∧ nativeBad.val < 1 ∧
      (∀ owner key, FullSupport (values owner key)) ∧ control.actor = some who ∧
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace =
          ((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).infoOf who referenceTrace ∧
      setup.proposalRecoveryModel.historyReachWeight sourceProfile
        (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0 ∧
      annotatedPrefixWeight setup values implementation operational sourceProfile
        (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan nativeInitial
            implementation.horizon implementation.scheduler values ⟨nativeBad, scale, scale, scale⟩)
        who ⟨some control, trace⟩ tape entry word *
          (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
            then 1 else 0) *
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload entry word value (g, target) ≠ 0 ∧
      mechanicalWord setup implementation who trace =
        mechanicalWord setup implementation who referenceTrace
  let covered (original : (nativeProtocol).History)
      (law : PMF (List (RawReplayChoice setup implementation))) : Prop :=
    ∀ endpoint, fiber endpoint → ∀ actual : (nativeProtocol).History,
      TracePrefix actual.trace endpoint.trace →
      mechanicalWord setup implementation who actual.trace =
        mechanicalWord setup implementation who original.trace →
      ∃ script ∈ law.support,
        sourceRawReplay setup implementation who target reference original script = some actual
  let stepCovered (original next : (nativeProtocol).History)
      (script : List (RawReplayChoice setup implementation))
      (law : PMF (List (RawReplayChoice setup implementation))) : Prop :=
    ∀ endpoint, fiber endpoint → ∀ actual : (nativeProtocol).History,
      TracePrefix actual.trace endpoint.trace →
      mechanicalWord setup implementation who actual.trace =
        mechanicalWord setup implementation who next.trace →
      sourceRawReplay setup implementation who target reference original script =
        some actual.prior →
      ∃ nextScript ∈ law.support,
        sourceRawReplay setup implementation who target reference next nextScript = some actual
  let valid := fun (original : (nativeProtocol).History)
      (script : List (RawReplayChoice setup implementation)) =>
    SourceReplayLostRestricted setup implementation target reference who
        (rawReplayLost setup implementation script) ∧
    (∀ (control : (nativeApplication).Control), original.state = some control →
      ∀ handle raw, rawReplayLost setup implementation script handle = some raw →
        control.execution.application.current.native.candidates.lookup handle ≠ .fresh) ∧
    ∃ actual : (nativeProtocol).History,
      sourceRawReplay setup implementation who target reference original script = some actual ∧
      RawReplayState setup implementation who target reference
        (rawReplayLost setup implementation script) original actual ∧
      mechanicalWord setup implementation who actual.trace =
        mechanicalWord setup implementation who original.trace ∧
      SourceReplayPrepared setup implementation who actual.state
  have neverNone (state : (nativeProtocol).State)
      (joint : Player → Option (nativeApplication).Action) :
      none ∉ ((nativeApplication).transition nativeInitial implementation.horizon
        implementation.scheduler state joint).support := by
    cases state with
    | none => simp [ReactiveApplication.transition]
    | some control =>
      cases active : control.actor with
      | some owner => simp [ReactiveApplication.transition, active]
      | none =>
        cases remaining : control.remaining with
        | zero => simp [ReactiveApplication.transition, active, remaining]
        | succ remaining =>
          simp [ReactiveApplication.transition, active, remaining]
  have uninitialized : ∀ {state : (nativeProtocol).State}
      (trace : (nativeProtocol).Trace state), state = none →
      HEq trace (Trace.start : (nativeProtocol).Trace (nativeProtocol).init) := by
    intro state trace stateEq
    cases trace with
    | start => rfl
    | @extend before after prior joint legal moved =>
      cases stateEq
      exact (neverNone before joint moved).elim
  have idleJoint {state : (nativeProtocol).State}
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal state joint)
      (idle : (nativeApplication).actor state = none) : joint = fun _ => none := by
    funext owner
    have offered := legal.2 owner
    cases chosen : joint owner with
    | none => rfl
    | some action =>
      rw [chosen] at offered
      have impossible : (none : Option Player) = some owner := by
        simpa only [ReactiveApplication.ResponseMenu.protocol, idle] using offered.1
      cases impossible
  have projectionOfWord {first second : (nativeProtocol).State}
      (left : (nativeProtocol).Trace first) (right : (nativeProtocol).Trace second)
      (words : mechanicalWord setup implementation who left =
        mechanicalWord setup implementation who right) :
      mechanicalProjection setup implementation who first =
        mechanicalProjection setup implementation who second := by
    have last := congrArg List.getLast? words
    rw [mechanicalWord_last, mechanicalWord_last] at last
    exact congrArg Subtype.val (Option.some.inj last)
  have idleHistory (before : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before)) (idle : before.actor = none)
      (first second : (nativeProtocol).State)
      (firstJoint secondJoint : Player → Option (nativeApplication).Action)
      (firstLegal : (nativeProtocol).Legal (some before) firstJoint)
      (secondLegal : (nativeProtocol).Legal (some before) secondJoint)
      (firstMoved : first ∈ ((nativeProtocol).step (some before)
        ⟨firstJoint, firstLegal⟩).support)
      (secondMoved : second ∈ ((nativeProtocol).step (some before)
        ⟨secondJoint, secondLegal⟩).support)
      (same : mechanicalProjection setup implementation who first =
        mechanicalProjection setup implementation who second) :
      (⟨first, prior.extend firstJoint firstLegal firstMoved⟩ : (nativeProtocol).History) =
        ⟨second, prior.extend secondJoint secondLegal secondMoved⟩ := by
    have firstJointEq := idleJoint firstJoint firstLegal idle
    have secondJointEq := idleJoint secondJoint secondLegal idle
    subst firstJoint
    subst secondJoint
    cases first with
    | none => exact (neverNone _ _ firstMoved).elim
    | some first =>
      cases second with
      | none => exact (neverNone _ _ secondMoved).elim
      | some second =>
        have states := sourceReplay_environment_step_unique setup implementation operational who
          before first second idle _ _ firstMoved secondMoved same
        subst second
        rfl
  have produce : ∀ {state : (nativeProtocol).State}
      (trace : (nativeProtocol).Trace state), TracePrefix trace referenceTrace →
      ∃ law : PMF (List (RawReplayChoice setup implementation)),
        (∀ script ∈ law.support, valid ⟨state, trace⟩ script ∧
          SourceReplayScriptMass (setup := setup) (values := values) (implementation :=
            implementation)
            scale who target reference ⟨state, trace⟩ script (law script)) ∧
        covered ⟨state, trace⟩ law := by
    intro state trace
    induction trace with
    | start =>
      intro retained
      refine ⟨PMF.pure [], ?_, ?_⟩
      · intro script supported
        cases (PMF.mem_support_pure_iff ..).mp supported
        refine ⟨⟨?_, ?_, (nativeProtocol).initHistory, rfl, trivial, rfl, trivial⟩, ?_⟩
        · intro handle raw drawn
          cases drawn
        · intro control impossible
          cases impossible
        · simp only [PMF.pure_apply_self]
          exact SourceReplayScriptMass.start
      · intro endpoint _positive actual _retained words
        rcases actual with ⟨actualState, actualTrace⟩
        cases actualTrace with
        | start => exact ⟨[], (PMF.mem_support_pure_iff ..).mpr rfl, rfl⟩
        | extend actualPrior actualJoint actualLegal actualMoved =>
          have lengths := congrArg List.length words
          simp only [mechanicalWord_length, Trace.length] at lengths
          omega
    | @extend before after prior joint legal moved ih =>
      intro onward
      have kept : TracePrefix prior referenceTrace :=
        (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved).trans
          onward
      obtain ⟨previous, previousValid, previousCovered⟩ := ih kept
      have advance (script : List (RawReplayChoice setup implementation))
          (supported : script ∈ previous.support) :
          ∃ law : PMF (List (RawReplayChoice setup implementation)),
            (∀ next ∈ law.support,
              valid ⟨after, prior.extend joint legal moved⟩ next ∧ next.tail = script ∧
              SourceReplayScriptMass (setup := setup) (values := values)
                (implementation := implementation) scale who target reference
                  ⟨after, prior.extend joint legal moved⟩ next (previous script * law next)) ∧
            stepCovered ⟨before, prior⟩ ⟨after, prior.extend joint legal moved⟩ script law := by
        obtain ⟨previousState, previousMass⟩ := previousValid script supported
        obtain ⟨restricted, introduced, actualHistory, replayed, related, word, prepared⟩ :=
          previousState
        have splitActual (actual : (nativeProtocol).History)
            (words : mechanicalWord setup implementation who actual.trace =
              mechanicalWord setup implementation who (prior.extend joint legal moved))
            (earlier : sourceRawReplay setup implementation who target reference
              ⟨before, prior⟩ script = some actual.prior) :
            ∃ (actualJoint : Player → Option (nativeApplication).Action)
              (actualLegal : (nativeProtocol).Legal actualHistory.state actualJoint)
              (actualAfter : (nativeProtocol).State)
              (actualMoved : actualAfter ∈
                ((nativeProtocol).step actualHistory.state ⟨actualJoint, actualLegal⟩).support),
              actual = actualHistory.extend actualLegal actualMoved := by
          rcases actual with ⟨actualState, actualTrace⟩
          cases actualTrace with
          | start =>
            have lengths := congrArg List.length words
            simp only [mechanicalWord_length, Trace.length] at lengths
            omega
          | extend actualPrior actualJoint actualLegal actualMoved =>
            have previousEq : (⟨_, actualPrior⟩ : (nativeProtocol).History) = actualHistory :=
              Option.some.inj (earlier.symm.trans replayed)
            cases previousEq
            exact ⟨actualJoint, actualLegal, _, actualMoved, rfl⟩
        cases before with
        | none =>
          have priorEq : prior = (Trace.start : (nativeProtocol).Trace none) :=
            eq_of_heq (uninitialized prior rfl)
          cases priorEq
          cases script with
          | cons choice rest =>
            simp only [sourceRawReplay] at replayed
            cases replayed
          | nil =>
            have initialMoved := moved
            change after ∈ ((nativeInitial).map fun state => some
              (⟨implementation.horizon, none,
                ReactiveApplication.Execution.initial nativeApplication state⟩ :
                (nativeApplication).Control)).support at initialMoved
            obtain ⟨initialStateDraw, initialSupported, afterEq⟩ :=
              (PMF.mem_support_map_iff ..).mp initialMoved
            change initialStateDraw ∈ (setup.initialLaw.map fun theta =>
              PhaseRuntimeState.initial implementation.plan (encodeInputs theta)).support
              at initialSupported
            obtain ⟨theta, _thetaSupported, initialEq⟩ :=
              (PMF.mem_support_map_iff ..).mp initialSupported
            cases initialEq
            cases afterEq
            let original : (nativeApplication).Control := ⟨implementation.horizon, none,
              ReactiveApplication.Execution.initial nativeApplication
                (PhaseRuntimeState.initial implementation.plan (encodeInputs theta))⟩
            have native := (phaseApplication_invariant implementation.runtime implementation.leaks
              (encodeInputs theta)).tracePrefix (nativeMenu) nativeInitial implementation.horizon
                implementation.scheduler original reference (Trace.start.extend joint legal moved)
                  referenceTrace onward
                  (PhaseRuntimeState.initial_invariant implementation.plan (encodeInputs theta)).1
            have inputsEq : encodeInputs theta = encodeInputs cut.theta :=
              native.active.reachable.inputs_eq.symm.trans cut.originalInputs
            have initialAssigned := alignment.initialized (rawReplayLost setup implementation [])
              restricted
            rw [← inputsEq] at initialAssigned
            have image := alignment.images (rawReplayLost setup implementation []) restricted
              original (Trace.start.extend joint legal moved) onward
            obtain ⟨actual, replay, actualState, actualWord⟩ := sourceRawReplay_initialize
              setup implementation who reference targetCurrent targetTrace _ joint legal moved
            have actualRelated : RawReplayState setup implementation who target reference
                (rawReplayLost setup implementation [(none, none)])
                ⟨some original, Trace.start.extend joint legal moved⟩ actual := by
              unfold RawReplayState
              rw [actualState]
              refine ⟨rfl, rfl, ?_, rfl, ?_⟩
              · change ReactiveApplication.Execution.initial nativeApplication
                    (PhaseRuntimeState.initial implementation.plan
                      (encodeInputs (ProtocolState.base setup.program targetCurrent.point))) =
                  sourceReplayExecution setup implementation target reference
                    (rawReplayLost setup implementation []) (fun _ => []) original.execution
                dsimp only [sourceReplayExecution, original,
                  ReactiveApplication.Execution.initial]
                rw [initialAssigned]
              · have observed := image.focalView (fun _ => []) rfl
                dsimp only [sourceReplayExecution, original,
                  ReactiveApplication.Execution.initial] at observed
                rw [initialAssigned] at observed
                exact observed
            have actualWordEq : mechanicalWord setup implementation who actual.trace =
                mechanicalWord setup implementation who (Trace.start.extend joint legal moved) := by
              rw [actualWord]
              change _ = [_, _]
              apply congrArg (fun last : Set.range (mechanicalProjection setup implementation
                  who) =>
                [⟨mechanicalProjection setup implementation who none, none, rfl⟩, last])
              apply Subtype.ext
              simpa only [actualState] using RawReplayState.mechanicalProjection setup
                implementation who target reference (rawReplayLost setup implementation [(none,
                  none)])
                  ⟨some original, Trace.start.extend joint legal moved⟩ actual actualRelated
            refine ⟨PMF.pure [(none, none)], ?_, ?_⟩
            · intro next nextSupported
              cases (PMF.mem_support_pure_iff ..).mp nextSupported
              refine ⟨⟨restricted, ?_, actual, replay, actualRelated, actualWordEq, ?_⟩, rfl, ?_⟩
              · intro control stateEq handle raw drawn
                cases drawn
              · rw [actualState]
                intro owner foreign record member
                simp only [ReactiveApplication.Execution.initial,
                  ReactiveApplication.recallOwnPlay, ReactiveApplication.ownPlayFrom,
                  List.not_mem_nil] at member
              · simp only [PMF.pure_apply_self, mul_one]
                exact SourceReplayScriptMass.deterministic (Or.inl rfl) previousMass
            · intro endpoint positiveEndpoint wanted wantedKept wantedWord previousReplay
              have initialized : actualHistory = (nativeProtocol).initHistory :=
                Option.some.inj replayed.symm
              subst actualHistory
              obtain ⟨actualJoint, actualLegal, actualAfter, actualMoved, wantedEq⟩ :=
                splitActual wanted wantedWord previousReplay
              cases wantedEq
              have jointEq := idleJoint actualJoint actualLegal rfl
              subst actualJoint
              change actualAfter ∈ ((nativeInitial).map fun state => some
                (⟨implementation.horizon, none,
                  ReactiveApplication.Execution.initial nativeApplication state⟩ :
                    (nativeApplication).Control)).support at actualMoved
              obtain ⟨actualNative, actualDraw, actualEq⟩ :=
                (PMF.mem_support_map_iff ..).mp actualMoved
              change actualNative ∈ (setup.initialLaw.map fun theta =>
                PhaseRuntimeState.initial implementation.plan (encodeInputs theta)).support
                  at actualDraw
              obtain ⟨actualTheta, _actualDrawn, nativeEq⟩ :=
                (PMF.mem_support_map_iff ..).mp actualDraw
              cases nativeEq
              cases actualEq
              rcases positiveEndpoint with ⟨nativeBad, sourceProfile, control, trace, tape,
                entry, annotatedWord, payload, clean, value, rfl, _scalePositive, _scaleBelow,
                _badPositive, _badBelow, fullValues, active, _information, canonicalSupported,
                positive, _wholeWord⟩
              obtain ⟨theta, _drawn, inputs, final, finalState, originalBase⟩ :=
                positive_original_annotated_initial_inputs setup values implementation operational
                  fullValues sourceProfile _ who control trace active tape entry g target
                    annotatedWord canonicalSupported event payload clean value positive
              have finalEq : final = targetCurrent := Option.some.inj finalState.symm
              subst final
              let initializedControl : (nativeApplication).Control :=
                ⟨implementation.horizon, none, ReactiveApplication.Execution.initial
                  nativeApplication (PhaseRuntimeState.initial implementation.plan
                    (encodeInputs actualTheta))⟩
              have native := (phaseApplication_invariant implementation.runtime implementation.leaks
                (encodeInputs actualTheta)).tracePrefix (nativeMenu) nativeInitial
                  implementation.horizon implementation.scheduler initializedControl control
                    _ trace wantedKept
                    (PhaseRuntimeState.initial_invariant implementation.plan
                      (encodeInputs actualTheta)).1
              have inputsEq : encodeInputs actualTheta =
                  encodeInputs (ProtocolState.base setup.program targetCurrent.point) :=
                native.active.reachable.inputs_eq.symm.trans
                  (inputs.trans (congrArg encodeInputs originalBase.symm))
              refine ⟨[(none, none)], (PMF.mem_support_pure_iff ..).mpr rfl, ?_⟩
              simp only [sourceRawReplay, Option.bind_some]
              rw [finalState]
              dsimp only
              rw [← inputsEq]
              exact sourceReplayAppend_supported setup implementation (nativeProtocol).initHistory
                _ _ actualLegal actualMoved
        | some before =>
          cases after with
          | none => exact (neverNone (some before) joint moved).elim
          | some after =>
            rcases actualHistory with ⟨actualState, actual⟩
            cases actualState with
            | none => cases related
            | some actualControl =>
              obtain ⟨remaining, actor, execution, recalled, _observed⟩ := related
              let recalls := actualControl.execution.recall
              have assigned : actualControl = { before with
                  execution := sourceReplayExecution setup implementation target reference
                    (rawReplayLost setup implementation script) recalls before.execution } := by
                cases actualControl
                cases before
                simp only [ReactiveApplication.Control.mk.injEq] at remaining actor ⊢
                exact ⟨remaining, actor, execution⟩
              have introducedBefore := introduced before rfl
              have image := alignment.images (rawReplayLost setup implementation script)
                restricted before prior kept
              have nextImage := alignment.images (rawReplayLost setup implementation script)
                restricted after (prior.extend joint legal moved) onward
              have carry (handle : Handle (serviceGraph setup .concurrent))
                  (fixed : before.execution.application.current.native.candidates.lookup handle ≠
                    .fresh) :
                  after.execution.application.current.native.candidates.lookup handle ≠ .fresh := by
                let stable := phaseApplication_preservesFixedCandidates implementation.runtime
                  implementation.leaks
                have invariant : (nativeApplication).Invariant (fun state =>
                    state.current.native.candidates.lookup handle =
                      before.execution.application.current.native.candidates.lookup handle) := by
                  constructor
                  · intro state owner material known
                    exact (stable.submit state owner material handle
                      (by rw [known]; exact fixed)).trans known
                  · intro state message next known handled
                    exact (stable.handle state message next handled handle
                      (by rw [known]; exact fixed)).trans known
                  · intro state command next known reached
                    exact (stable.environment state command next reached handle
                      (by rw [known]; exact fixed)).trans known
                rw [invariant.tracePrefix (nativeMenu) nativeInitial implementation.horizon
                  implementation.scheduler before after prior (prior.extend joint legal moved)
                    (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal
                      moved) rfl]
                exact fixed
              cases acting : before.actor with
              | none =>
                obtain ⟨history, replay, ending, _retained, nextRelated, nextWord⟩ :=
                  sourceRawReplay_environment_extend setup implementation who target reference
                    referenceTrace before after prior joint legal moved acting script recalls
                      actualControl assigned actual replayed image nextImage recalled word
                refine ⟨PMF.pure ((none, none) :: script), ?_, ?_⟩
                · intro next nextSupported
                  cases (PMF.mem_support_pure_iff ..).mp nextSupported
                  refine ⟨⟨restricted, ?_, history, replay, nextRelated, nextWord, ?_⟩, rfl, ?_⟩
                  · intro control stateEq handle raw drawn
                    cases Option.some.inj stateEq
                    exact carry handle (introducedBefore handle raw drawn)
                  · rw [ending]
                    exact prepared
                  · simp only [PMF.pure_apply_self, mul_one]
                    exact SourceReplayScriptMass.deterministic (Or.inl acting) previousMass
                · intro endpoint _positiveEndpoint wanted _wantedKept wantedWord previousReplay
                  obtain ⟨actualJoint, actualLegal, actualAfter, actualMoved, wantedEq⟩ :=
                    splitActual wanted wantedWord previousReplay
                  cases wantedEq
                  obtain ⟨previousHistory, historyReplay, historyPrior⟩ :=
                    sourceRawReplay_step_prior setup implementation who target reference prior
                      joint legal moved (none, none) script history replay
                  have previousEq : previousHistory = ⟨some actualControl, actual⟩ :=
                    Option.some.inj (historyReplay.symm.trans replayed)
                  have historyBefore : sourceRawReplay setup implementation who target reference
                      ⟨some before, prior⟩ script = some history.prior :=
                    replayed.trans (congrArg some (historyPrior.trans previousEq).symm)
                  obtain ⟨producedJoint, producedLegal, producedAfter, producedMoved, historyEq⟩ :=
                    splitActual history nextWord historyBefore
                  cases historyEq
                  have histories := idleHistory actualControl actual (actor.trans acting)
                    producedAfter actualAfter producedJoint actualJoint producedLegal actualLegal
                      producedMoved actualMoved
                      (projectionOfWord _ _ (nextWord.trans wantedWord.symm))
                  exact ⟨(none, none) :: script, (PMF.mem_support_pure_iff ..).mpr rfl,
                    replay.trans (congrArg some histories)⟩
              | some owner =>
                by_cases focal : owner = who
                · subst owner
                  obtain ⟨history, replay, _retained, nextRelated, nextWord⟩ :=
                    sourceRawReplay_focal_extend setup implementation who target reference
                      referenceTrace before after prior joint legal moved onward acting script
                        recalls actualControl assigned actual replayed image nextImage recalled word
                  have offered := legal.2 who
                  obtain ⟨action, selected, member⟩ : ∃ action : (nativeApplication).Action,
                      joint who = some action ∧ action ∈ (nativeMenu).actions who
                        (before.execution.recall who)
                          (before.execution.observe nativeApplication who) := by
                    cases chosen : joint who with
                    | none =>
                      rw [chosen] at offered
                      exact (offered (by exact acting)).elim
                    | some action => exact ⟨action, rfl, (chosen ▸ offered).2⟩
                  let response : PhaseProposal.Response implementation.runtime implementation.leaks
                      implementation.bounds who (actualControl.execution.recall who)
                        (actualControl.execution.observe nativeApplication who) :=
                    ⟨action, by
                      change action ∈ PhaseCount.onePacketActions implementation.runtime
                        implementation.leaks implementation.bounds who
                          (before.execution.recall who)
                            (before.execution.observe nativeApplication who) at member
                      simpa only [recalled, _observed] using member⟩
                  obtain ⟨copied, copiedReplay, copiedState, _prefix, _suffix⟩ :=
                    sourceRawReplay_callback_extend setup implementation who target reference
                      before (some after) prior joint legal moved who acting script (none, none)
                        actualControl actual replayed (actor.trans acting) response (by
                          simpa only [↓reduceIte] using selected)
                  have copiedEq : history = copied :=
                    Option.some.inj (replay.symm.trans copiedReplay)
                  have preparedNext : SourceReplayPrepared setup implementation who
                      history.state := by
                    rw [copiedEq, copiedState]
                    exact sourceReplayPrepared_respond setup implementation who actualControl who
                      response.val prepared (fun impossible => (impossible rfl).elim)
                  refine ⟨PMF.pure ((none, none) :: script), ?_, ?_⟩
                  · intro next nextSupported
                    cases (PMF.mem_support_pure_iff ..).mp nextSupported
                    refine ⟨⟨restricted, ?_, history, replay, nextRelated, nextWord, preparedNext⟩,
                      rfl, ?_⟩
                    · intro control stateEq handle raw drawn
                      cases Option.some.inj stateEq
                      exact carry handle (introducedBefore handle raw drawn)
                    · simp only [PMF.pure_apply_self, mul_one]
                      exact SourceReplayScriptMass.deterministic (Or.inr acting) previousMass
                  · intro endpoint _positiveEndpoint wanted _wantedKept wantedWord previousReplay
                    obtain ⟨actualJoint, actualLegal, actualAfter, actualMoved, wantedEq⟩ :=
                      splitActual wanted wantedWord previousReplay
                    cases wantedEq
                    cases actualAfter with
                    | none => exact (neverNone _ _ actualMoved).elim
                    | some actualAfter =>
                      have actualActor : actualControl.actor = some who := actor.trans acting
                      obtain ⟨actualAction, actualSelected, _actualMember⟩ :
                          ∃ chosen : (nativeApplication).Action,
                            actualJoint who = some chosen ∧ chosen ∈ (nativeMenu).actions who
                              (actualControl.execution.recall who)
                                (actualControl.execution.observe nativeApplication who) := by
                        have offered := actualLegal.2 who
                        cases chosen : actualJoint who with
                        | none =>
                          rw [chosen] at offered
                          exact (offered (by exact actualActor)).elim
                        | some chosenAction => exact ⟨chosenAction, rfl, (chosen ▸ offered).2⟩
                      have plays := mechanicalWord_ownPlay setup implementation who actualAfter
                        after (actual.extend actualJoint actualLegal actualMoved)
                          (prior.extend joint legal moved) wantedWord
                      rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend,
                        actualSelected, selected] at plays
                      have actionEq : actualAction = action :=
                        congrArg Prod.snd (List.cons.inj plays).1
                      refine ⟨(none, none) :: script,
                        (PMF.mem_support_pure_iff ..).mpr rfl, ?_⟩
                      apply sourceRawReplay_callback_of_actual setup implementation who target
                        reference before (some after) prior joint legal moved who acting script
                          (none, none) actualControl actual replayed actualActor (some actualAfter)
                            actualJoint actualLegal actualMoved actualAction actualSelected
                      simp only [↓reduceIte, selected]
                      exact congrArg some actionEq.symm
                · obtain ⟨kernel, kernelAtoms, kernelDescription, produced⟩ :=
                    sourceRawReplay_foreign_law (setup
                  := setup) (values := values)
                    (implementation := implementation) operational who reference before after
                      referenceTrace event cut g
                      sourceChoice targetCurrent targetTrace alignment prior joint legal moved
                        onward
                        owner focal acting (good owner focal) script restricted introducedBefore
                          recalls actualControl assigned actual replayed recalled word scale
                  refine ⟨kernel.map (fun choice => choice :: script), ?_, ?_⟩
                  · intro next nextSupported
                    obtain ⟨choice, choiceSupported, nextEq⟩ :=
                      (PMF.mem_support_map_iff ..).mp nextSupported
                    cases nextEq
                    obtain ⟨restrictedNext, introducedNext, history, replay, _retained,
                      nextRelated, nextWord⟩ := produced choice choiceSupported
                    obtain ⟨_slot, response, selectedResponse, clean, _atom⟩ :=
                      kernelAtoms choice choiceSupported
                    obtain ⟨copied, copiedReplay, copiedState, _prefix, _suffix⟩ :=
                      sourceRawReplay_callback_extend setup implementation who target reference
                        before (some after) prior joint legal moved owner acting script choice
                          actualControl actual replayed (actor.trans acting) response (by
                            simpa only [focal, ↓reduceIte] using selectedResponse)
                    have copiedEq : history = copied :=
                      Option.some.inj (replay.symm.trans copiedReplay)
                    have preparedNext : SourceReplayPrepared setup implementation who
                        history.state := by
                      rw [copiedEq, copiedState]
                      exact sourceReplayPrepared_respond setup implementation who actualControl
                        owner response.val prepared (fun _ => clean)
                    refine ⟨⟨restrictedNext, ?_, history, replay, nextRelated, nextWord,
                      preparedNext⟩, rfl, ?_⟩
                    · intro control stateEq
                      cases Option.some.inj stateEq
                      exact introducedNext
                    · have atom : (kernel.map (fun chosen => chosen :: script))
                          (choice :: script) = kernel choice := by
                        apply pmf_map_apply_of_injective
                        intro first second same
                        exact (List.cons.inj same).1
                      rw [atom]
                      exact SourceReplayScriptMass.foreign owner focal acting actualControl actual
                        replayed ⟨remaining, actor, execution, recalled, _observed⟩ kernel
                          kernelAtoms
                          kernelDescription choice choiceSupported previousMass
                  · intro endpoint positiveEndpoint wanted wantedKept wantedWord previousReplay
                    obtain ⟨actualJoint, actualLegal, actualAfter, actualMoved, wantedEq⟩ :=
                      splitActual wanted wantedWord previousReplay
                    cases wantedEq
                    cases actualAfter with
                    | none => exact (neverNone _ _ actualMoved).elim
                    | some actualAfter =>
                      have actualActor : actualControl.actor = some owner := actor.trans acting
                      obtain ⟨actualAction, actualSelected, actualMember⟩ :
                          ∃ chosen : (nativeApplication).Action,
                            actualJoint owner = some chosen ∧ chosen ∈ (nativeMenu).actions owner
                              (actualControl.execution.recall owner)
                                (actualControl.execution.observe nativeApplication owner) := by
                        have offered := actualLegal.2 owner
                        cases chosen : actualJoint owner with
                        | none =>
                          rw [chosen] at offered
                          exact (offered (by exact actualActor)).elim
                        | some chosenAction => exact ⟨chosenAction, rfl, (chosen ▸ offered).2⟩
                      let actualResponse : PhaseProposal.Response implementation.runtime
                          implementation.leaks implementation.bounds owner
                            (actualControl.execution.recall owner)
                              (actualControl.execution.observe nativeApplication owner) :=
                        ⟨actualAction, actualMember⟩
                      have actualEnding : actualAfter = { actualControl with
                          actor := none
                          execution := actualControl.execution.respond nativeApplication owner
                            actualAction } := by
                        change some actualAfter ∈ ((nativeApplication).transition nativeInitial
                          implementation.horizon implementation.scheduler (some actualControl)
                            actualJoint).support at actualMoved
                        simpa only [ReactiveApplication.transition, actualActor, actualSelected,
                          Option.getD_some, PMF.mem_support_pure_iff, Option.some.injEq]
                            using actualMoved
                      let packetOf := fun response : PhaseProposal.Response implementation.runtime
                          implementation.leaks implementation.bounds owner
                            (actualControl.execution.recall owner)
                              (actualControl.execution.observe nativeApplication owner) =>
                        response.val.transmission.map fun material =>
                          (PhaseCount.localEnvelope implementation.runtime implementation.leaks
                            owner (actualControl.execution.recall owner)
                              (actualControl.execution.observe nativeApplication owner)
                                material).payload
                      have canonicalPackets (choice : RawReplayChoice setup implementation)
                          (member : choice ∈ kernel.support)
                          (response : PhaseProposal.Response implementation.runtime
                            implementation.leaks implementation.bounds owner
                              (actualControl.execution.recall owner)
                                (actualControl.execution.observe nativeApplication owner))
                          (chosen : choice.2 = some response.val) :
                          packetOf actualResponse = packetOf response := by
                        obtain ⟨_restricted, _introduced, history, replay, _kept,
                          _related, nextWord⟩ := produced choice member
                        obtain ⟨copied, copiedReplay, copiedState, _kept, _word⟩ :=
                          sourceRawReplay_callback_extend setup implementation who target reference
                            before (some after) prior joint legal moved owner acting script choice
                              actualControl actual replayed actualActor response (by
                                simpa only [focal, ↓reduceIte] using chosen)
                        have copiedEq : history = copied :=
                          Option.some.inj (replay.symm.trans copiedReplay)
                        have nextM := projectionOfWord history.trace
                          (actual.extend actualJoint actualLegal actualMoved)
                            (nextWord.trans wantedWord.symm)
                        rw [copiedEq, copiedState, actualEnding] at nextM
                        exact mechanicalProjection_response_packet setup implementation who owner
                          actualControl actualControl actual actual actualAction response.val rfl
                            nextM.symm
                      have canonicalMember (tag : Option
                          (Handle (serviceGraph setup .concurrent) × Raw L))
                          (response : PhaseProposal.Response implementation.runtime
                            implementation.leaks implementation.bounds owner
                              (actualControl.execution.recall owner)
                                (actualControl.execution.observe nativeApplication owner))
                          (scalePositive : 0 < scale.val) :
                          (tag, some response.val) ∈ (sourceReplayAliases setup implementation
                            scale owner actualControl.execution tag
                              (PhaseProposal.projectResponse implementation.runtime
                                implementation.leaks implementation.bounds owner
                                  (actualControl.execution.recall owner)
                                    (actualControl.execution.observe nativeApplication owner)
                                      response)).support := by
                        unfold sourceReplayAliases
                        apply (PMF.mem_support_map_iff ..).mpr
                        exact ⟨response, PMF.splitKernel_fullFiber _ _ _ scale.val
                          scale.property.1 scale.property.2 scalePositive _ response rfl, rfl⟩
                      have bindingMaterial (bindingEvent : (serviceGraph setup .concurrent).EventId)
                          (bindingPayload : L.Ty) (serial : Nat) (value : L.Val bindingPayload)
                          (response : PhaseProposal.Response implementation.runtime
                            implementation.leaks implementation.bounds owner
                              (actualControl.execution.recall owner)
                                (actualControl.execution.observe nativeApplication owner))
                          (declared : response.val = phaseBindingResponse implementation.runtime
                            implementation.leaks owner bindingEvent bindingPayload (.success value)
                              serial)
                          (packets : packetOf actualResponse = packetOf response) :
                          ∃ (opening : Option (Raw L))
                            (evidence : EvidenceRequest (serviceGraph setup .concurrent)),
                            actualAction = ⟨some ⟨⟨.commitment bindingEvent
                              (owner, .prepared serial), opening⟩, evidence⟩⟩ := by
                        dsimp only [packetOf] at packets
                        rw [declared] at packets
                        obtain ⟨material, transmitted, envelope⟩ :=
                          Option.map_eq_some_iff.mp packets
                        have call := congrArg
                          (fun packet : CommitAttemptPacket (serviceGraph setup .concurrent) =>
                            packet.packet.call) envelope
                        change (PhaseCount.maskPacket _ _).call =
                          (PhaseCount.maskPacket _ _).call at call
                        rw [PhaseCount.maskPacket_call, PhaseCount.maskPacket_call] at call
                        rcases material with ⟨⟨actualPacket, opening⟩, evidence⟩
                        cases call
                        refine ⟨opening, evidence, ?_⟩
                        change actualAction.transmission = _ at transmitted
                        cases actualAction
                        cases transmitted
                        rfl
                      rcases positiveEndpoint with ⟨nativeBad, sourceProfile, control, trace, tape,
                        entry, annotatedWord, payload, clean, value, endpointEq, scalePositive,
                        scaleBelow, badPositive, badBelow, fullValues, active, _information,
                        canonicalSupported, positive, wholeWord⟩
                      subst endpoint
                      let rates : PhaseProposalRates := ⟨nativeBad, scale, scale, scale⟩
                      let nativeProfile := phaseProposalReferenceStrategy setup .concurrent
                        implementation.runtime implementation.leaks implementation.bounds
                          implementation.plan nativeInitial implementation.horizon
                            implementation.scheduler values rates
                      have prefixPositive :=
                        (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
                      have nativePositive : ((nativeMenu).information nativeInitial
                          implementation.horizon implementation.scheduler).historyReachWeight
                            nativeProfile ⟨some control, trace⟩ ≠ 0 := by
                        unfold annotatedPrefixWeight at prefixPositive
                        exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp prefixPositive).1).1
                      have supported := (sourceReplay_prescribed_callback_support setup values
                        implementation rates control trace nativePositive actualControl actual
                          (some actualAfter) actualJoint actualLegal actualMoved wantedKept owner
                            actualActor actualResponse actualSelected).1
                      have sourceMeaning := sourceHandleMeaning_eq_of_mechanicalProjection setup
                        implementation who target reference control referenceTrace trace
                          (projectionOfWord _ _ wholeWord.symm)
                      have supportedChoice : ∃ choice ∈ kernel.support,
                          choice.2 = some actualAction := by
                        rcases kernelDescription with ⟨canonical, kernelEq, origin⟩ |
                          ⟨bindingEvent, bindingPayload, binding, key, serial, canonical, query,
                            missing, declared, kernelEq⟩
                        · have member : (none, some canonical.val) ∈ kernel.support := by
                            rw [kernelEq]
                            exact canonicalMember none canonical scalePositive
                          have packets := canonicalPackets _ member canonical rfl
                          have actualAlias : (none, some actualAction) ∈ kernel.support := by
                            rw [kernelEq]
                            rcases origin with nonbinding | bindingOrigin
                            · exact sourceReplay_nonbinding_alias_supported setup implementation
                                scale scalePositive owner actualControl.execution actualResponse
                                  canonical (Or.inl nonbinding) packets
                            · rcases bindingOrigin with openingOrigin | bindingOrigin
                              · exact sourceReplay_nonbinding_alias_supported setup implementation
                                  scale scalePositive owner actualControl.execution actualResponse
                                    canonical (Or.inr openingOrigin) packets
                              · obtain ⟨bindingEvent, bindingPayload, serial, recovered, binding,
                                  meaning, declared⟩ := bindingOrigin
                                obtain ⟨opening, evidence, actionEq⟩ := bindingMaterial bindingEvent
                                  bindingPayload serial recovered canonical declared packets
                                have preparation := positive_original_annotated_callback_preparation
                                  setup values implementation operational fullValues sourceProfile
                                    nativeProfile who control trace active tape entry g target
                                      annotatedWord canonicalSupported event payload clean value
                                        positive actualControl actualAfter actual actualJoint
                                          actualLegal actualMoved wantedKept owner actualActor
                                            bindingEvent bindingPayload binding serial opening
                                              evidence (actualSelected.trans
                                                (congrArg some actionEq)) recovered
                                                  ((sourceMeaning _).symm.trans meaning)
                                rw [← actionEq] at preparation
                                exact sourceReplay_binding_alias_supported setup implementation
                                  scale scalePositive owner actualControl.execution bindingEvent
                                    bindingPayload binding serial recovered actualResponse canonical
                                      declared preparation packets none
                          exact ⟨(none, some actualAction), actualAlias, rfl⟩
                        · let draw := (values owner key).map fun sampled =>
                            phaseRecoveryDomainValue setup .concurrent bindingEvent owner
                              bindingPayload binding sampled.val.val
                          obtain ⟨sampled, sampledMember⟩ := draw.support_nonempty
                          have sampledAlias := canonicalMember
                            (some ((owner, .prepared serial), (⟨bindingPayload, sampled⟩ : Raw L)))
                              (canonical sampled) scalePositive
                          have member : (some ((owner, .prepared serial),
                              (⟨bindingPayload, sampled⟩ : Raw L)),
                                some (canonical sampled).val) ∈ kernel.support := by
                            rw [kernelEq]
                            exact (PMF.mem_support_bind_iff ..).mpr
                              ⟨sampled, sampledMember, sampledAlias⟩
                          have packets := canonicalPackets _ member (canonical sampled) rfl
                          obtain ⟨opening, evidence, actionEq⟩ := bindingMaterial bindingEvent
                            bindingPayload serial sampled (canonical sampled) (declared sampled)
                              packets
                          have usable :
                              opening.bind (fun raw => raw.as? bindingPayload) ≠ none := by
                            intro unusable
                            have atStep : (((nativeMenu).information nativeInitial
                                implementation.horizon implementation.scheduler).infoOf owner
                                  actual, actualAction) ∈ ((nativeMenu).information nativeInitial
                                implementation.horizon implementation.scheduler).ownPlay owner
                                  (actual.extend actualJoint actualLegal actualMoved) := by
                              rw [InfoSignals.ownPlay_extend, actualSelected]
                              exact List.mem_cons_self
                            let model := (nativeMenu).information nativeInitial
                              implementation.horizon implementation.scheduler
                            have atFinal := (model.ownPlay_isSuffix_of_reachesWithin owner
                              wantedKept.reachesWithin).subset atStep
                            have noBad : ¬ PhaseProposal.GeneratedUnusableBindingHistory
                                implementation.runtime implementation.leaks implementation.bounds
                                  nativeInitial implementation.horizon implementation.scheduler
                                    owner ⟨some control, trace⟩ := by
                              have prefixNZ :=
                                (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
                              unfold annotatedPrefixWeight at prefixNZ
                              have gated := (mul_ne_zero_iff.mp prefixNZ).2
                              split at gated
                              · rename_i kept
                                exact kept.1 owner focal
                              · exact (gated rfl).elim
                            exact noBad ⟨_, atFinal, bindingEvent, bindingPayload, serial, opening,
                              evidence, binding, actionEq, unusable⟩
                          obtain ⟨recovered, typed⟩ := Option.ne_none_iff_exists'.mp usable
                          let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
                            ⟨⟨.commitment bindingEvent (owner, .prepared serial), opening⟩,
                              evidence⟩
                          have transmitted : actualResponse.val.transmission = some material :=
                            congrArg (fun action : (nativeApplication).Action =>
                              action.transmission) actionEq
                          have preparation : PhaseProposal.bindingPreparation material =
                              some (⟨bindingPayload, recovered⟩ : Raw L) := by
                            simp only [material, PhaseProposal.bindingPreparation, binding, typed,
                              Option.map_some]
                          have inputTrace : (nativeProtocol).Trace
                              (some ⟨actualControl.remaining, some owner,
                                actualControl.execution⟩) := by
                            have controlEq : actualControl =
                                ⟨actualControl.remaining, some owner, actualControl.execution⟩ := by
                              exact congrArg (fun requested : Option Player =>
                                (⟨actualControl.remaining, requested, actualControl.execution⟩ :
                                  (nativeApplication).Control)) actualActor
                            rw [← controlEq]
                            exact actual
                          have initialEq : ((setup.initialLaw.map encodeInputs).map
                              (PhaseRuntimeState.initial implementation.plan)) = nativeInitial := by
                            rw [PMF.map_comp]
                            rfl
                          have originalTrace := inputTrace
                          rw [← initialEq] at originalTrace
                          have materialMember := actualResponse.property
                          change actualAction ∈ PhaseCount.onePacketActions implementation.runtime
                            implementation.leaks implementation.bounds owner
                              (actualControl.execution.recall owner)
                                (actualControl.execution.observe nativeApplication owner)
                                  at materialMember
                          rw [actionEq] at materialMember
                          obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent
                            implementation.runtime implementation.leaks implementation.bounds
                              implementation.plan (setup.initialLaw.map encodeInputs)
                                implementation.horizon implementation.scheduler
                                  actualControl.remaining owner actualControl.execution
                                    originalTrace material materialMember
                          have named := PhaseCount.onePacket_event_of_request implementation.runtime
                            implementation.leaks implementation.bounds implementation.plan
                              (serviceGraph_revealRelaxedOrdered setup .concurrent)
                                (setup.initialLaw.map encodeInputs) implementation.horizon
                                  implementation.scheduler actualControl.remaining owner
                                    actualControl.execution originalTrace coordinate request
                                      material materialMember
                          change some bindingEvent = some coordinate.event at named
                          have eventEq : coordinate.event = bindingEvent :=
                            Option.some.inj named.symm
                          have requestEvent := request
                          change actualControl.execution.application.SeedRequest owner
                            ⟨coordinate.attempt, coordinate.event⟩ at requestEvent
                          rw [request.1, eventEq] at requestEvent
                          have packetsRecovered : packetOf actualResponse =
                              packetOf (canonical recovered) := by
                            refine packets.trans ?_
                            simp only [packetOf, declared, phaseBindingResponse, Option.map_some,
                              PhaseCount.localEnvelope, EvidenceRequest.resolve]
                          have choiceMember := sourceReplay_lost_binding_supported setup values
                            implementation operational fullValues rates scalePositive scaleBelow
                              scalePositive scalePositive badPositive badBelow
                                actualControl.remaining owner actualControl.execution inputTrace
                                  bindingEvent bindingPayload binding requestEvent key query
                                    actualResponse supported material transmitted recovered
                                      preparation serial rfl canonical declared packetsRecovered
                          rw [kernelEq]
                          exact ⟨(some ((owner, .prepared serial),
                            (⟨bindingPayload, recovered⟩ : Raw L)), some actualAction),
                              choiceMember, rfl⟩
                      obtain ⟨choice, choiceMember, chosen⟩ := supportedChoice
                      refine ⟨choice :: script,
                        (PMF.mem_support_map_iff ..).mpr ⟨choice, choiceMember, rfl⟩, ?_⟩
                      apply sourceRawReplay_callback_of_actual setup implementation who target
                        reference before (some after) prior joint legal moved owner acting script
                          choice actualControl actual replayed actualActor (some actualAfter)
                            actualJoint actualLegal actualMoved actualAction actualSelected
                      simpa only [focal, ↓reduceIte] using chosen
      let next := fun script supported => (advance script supported).choose
      refine ⟨previous.bindOnSupport next, ?_, ?_⟩
      · intro script supported
        obtain ⟨earlier, earlierSupported, nextSupported⟩ :=
          (PMF.mem_support_bindOnSupport_iff ..).mp supported
        obtain ⟨nextValid, tailEq, nextMass⟩ :=
          (advance earlier earlierSupported).choose_spec.1 script nextSupported
        refine ⟨nextValid, ?_⟩
        have atom : previous.bindOnSupport next script =
            previous earlier * next earlier earlierSupported script := by
          rw [PMF.bindOnSupport_apply, tsum_eq_single earlier]
          · simp only [dite_eq_right earlierSupported]
          · intro other different
            by_cases absent : previous other = 0
            · simp only [absent, zero_mul]
            · have missing : next other absent script = 0 := by
                apply (PMF.apply_eq_zero_iff _ _).mpr
                intro offered
                have otherTail := (advance other absent).choose_spec.1 script offered |>.2.1
                exact different (otherTail.symm.trans tailEq)
              simp only [dite_eq_right absent, missing, mul_zero]
        rw [atom]
        exact nextMass
      · intro endpoint positiveEndpoint actual actualKept actualWord
        rcases actual with ⟨actualState, actualTrace⟩
        cases actualTrace with
        | start =>
          have lengths := congrArg List.length actualWord
          simp only [mechanicalWord_length, Trace.length] at lengths
          omega
        | @extend actualBefore actualAfter actualPrior actualJoint actualLegal actualMoved =>
          have lengths := congrArg List.length actualWord
          simp only [mechanicalWord_length, Trace.length] at lengths
          have prefixLength : (mechanicalWord setup implementation who actualPrior).length =
              (mechanicalWord setup implementation who prior).length := by
            simp only [mechanicalWord_length]
            omega
          have words := actualWord
          simp only [mechanicalWord] at words
          obtain ⟨priorWord, _last⟩ := List.append_inj words prefixLength
          have priorKept : TracePrefix actualPrior endpoint.trace :=
            (TracePrefix.extend TracePrefix.refl actualJoint actualLegal actualMoved).trans
              actualKept
          obtain ⟨earlier, earlierSupported, previousReplay⟩ := previousCovered endpoint
            positiveEndpoint ⟨actualBefore, actualPrior⟩ priorKept priorWord
          obtain ⟨script, scriptSupported, replay⟩ :=
            (advance earlier earlierSupported).choose_spec.2 endpoint positiveEndpoint
              ⟨_, actualPrior.extend actualJoint actualLegal actualMoved⟩
                actualKept actualWord previousReplay
          exact ⟨script, (PMF.mem_support_bindOnSupport_iff ..).mpr
            ⟨earlier, earlierSupported, scriptSupported⟩, replay⟩
  obtain ⟨law, supported, coverage⟩ := produce referenceTrace TracePrefix.refl
  let complete : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who target reference
        ⟨some reference, referenceTrace⟩ := {
    choices := law
    restricted := fun script member => (supported script member).1.1
    introduced := fun script member => (supported script member).1.2.1
    atoms := fun script member => (supported script member).2
    replayed := by
      intro script member
      obtain ⟨actual, replay, related, word, prepared⟩ := (supported script member).1.2.2
      exact ⟨actual, replay, related, word,
        sourceReplayPrepared_good setup implementation who actual prepared⟩ }
  refine ⟨complete, ?_⟩
  intro nativeBad scalePositive scaleBelow badPositive badBelow fullValues sourceProfile
    control trace active information tape entry word canonicalSupported payload clean value
      positive wholeWord
  have positiveEndpoint : fiber ⟨some control, trace⟩ :=
    ⟨nativeBad, sourceProfile, control, trace, tape, entry, word, payload, clean, value, rfl,
      scalePositive, scaleBelow, badPositive, badBelow, fullValues, active, information,
        canonicalSupported, positive, wholeWord⟩
  exact coverage ⟨some control, trace⟩ positiveEndpoint ⟨some control, trace⟩ TracePrefix.refl
    wholeWord

private theorem sourceReplay_focal_sent_word_congr
    (first second : (nativeApplication).Execution)
    (publicEq : first.application.publicView = second.application.publicView)
    (service : first.environmentRecall = second.environmentRecall)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) (who : Player)
    (frontier event : (serviceGraph setup .concurrent).EventId)
    (firstRequest : first.application.SeedRequest who
      ⟨first.application.attempt, frontier⟩)
    (secondRequest : second.application.SeedRequest who
      ⟨second.application.attempt, frontier⟩)
    (firstHandle secondHandle : Handle (serviceGraph setup .concurrent))
    (firstMaterial secondMaterial : WitnessedSubmission (serviceGraph setup .concurrent))
    (firstCall : firstMaterial.call.packet = .commitment frontier firstHandle)
    (secondCall : secondMaterial.call.packet = .commitment frontier secondHandle) :
    ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
        (first.respond nativeApplication who ⟨some firstMaterial⟩) who event ↔
      ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
        (second.respond nativeApplication who ⟨some secondMaterial⟩) who event := by
  classical
  have leftRequest := respond_request implementation.runtime implementation.leaks first who
    ⟨some firstMaterial⟩ who ⟨first.application.attempt, frontier⟩ firstRequest
  have rightRequest := respond_request implementation.runtime implementation.leaks second who
    ⟨some secondMaterial⟩ who ⟨second.application.attempt, frontier⟩ secondRequest
  have leftActive : who ∉ (first.respond nativeApplication who
      ⟨some firstMaterial⟩).application.current.excluded := firstRequest.2.2.2.2
  have rightActive : who ∉ (second.respond nativeApplication who
      ⟨some secondMaterial⟩).application.current.excluded := secondRequest.2.2.2.2
  have activated := congrArg (fun view => view.native.activatedAt) publicEq
  change first.application.current.native.activatedAt =
    second.application.current.native.activatedAt at activated
  have frontierEq : ReservedEpoch.frontierQualification implementation.runtime
        implementation.leaks tape (first.respond nativeApplication who ⟨some firstMaterial⟩)
          who frontier ↔
      ReservedEpoch.frontierQualification implementation.runtime implementation.leaks tape
        (second.respond nativeApplication who ⟨some secondMaterial⟩) who frontier := by
    rw [ReservedEpoch.frontierQualification_sent_binding_iff implementation.runtime
      implementation.leaks tape first who frontier firstHandle firstMaterial firstCall,
      ReservedEpoch.frontierQualification_sent_binding_iff implementation.runtime
        implementation.leaks tape second who frontier secondHandle secondMaterial secondCall]
    rw [activated, service]
  simp only [ReservedEpoch.ownedAcceptanceWord, leftActive, rightActive, ↓reduceIte]
  constructor
  · intro survived other requested
    have same : other = frontier :=
      (serviceGraph_revealRelaxedOrdered setup .concurrent).ready_actor_unique _
        rightRequest.2.2.1 requested.2.2.1 rightRequest.2.2.2.1 requested.2.2.2.1
    subst other
    exact (survived frontier leftRequest).imp_right frontierEq.mp
  · intro survived other requested
    have same : other = frontier :=
      (serviceGraph_revealRelaxedOrdered setup .concurrent).ready_actor_unique _
        leftRequest.2.2.1 requested.2.2.1 leftRequest.2.2.2.1 requested.2.2.2.1
    subst other
    exact (survived frontier rightRequest).imp_right frontierEq.mpr

private theorem sourceReplay_owned_word_congr
    (first second : (nativeApplication).Execution)
    (publicEq : first.application.publicView = second.application.publicView)
    (requests : ∀ owner coordinate,
      first.application.SeedRequest owner coordinate ↔
        second.application.SeedRequest owner coordinate)
    (network : first.network = second.network)
    (service : first.environmentRecall = second.environmentRecall)
    (outputs : ∀ owner, (nativeApplication).outputs (first.recall owner) =
      (nativeApplication).outputs (second.recall owner))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) :
    ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
        first owner event ↔
      ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
        second owner event := by
  classical
  have excluded := congrArg PhasePublicView.excluded publicEq
  change first.application.current.excluded = second.application.current.excluded at excluded
  have accepted := congrArg (fun view => view.native.accepted) publicEq
  change first.application.current.native.accepted = second.application.current.native.accepted
    at accepted
  have activated := congrArg (fun view => view.native.activatedAt) publicEq
  change first.application.current.native.activatedAt =
    second.application.current.native.activatedAt at activated
  have attempt := congrArg PhasePublicView.attempt publicEq
  change first.application.attempt = second.application.attempt at attempt
  have frontier (named : (serviceGraph setup .concurrent).EventId) :
      ReservedEpoch.frontierQualification implementation.runtime implementation.leaks tape
          first owner named ↔
        ReservedEpoch.frontierQualification implementation.runtime implementation.leaks tape
          second owner named := by
    unfold ReservedEpoch.frontierQualification
    rw [outputs owner, activated, attempt, network, service]
  by_cases absent : owner ∈ second.application.current.excluded
  · simp only [ReservedEpoch.ownedAcceptanceWord, excluded, accepted, absent, ↓reduceIte]
  · simp only [ReservedEpoch.ownedAcceptanceWord, excluded, absent, ↓reduceIte]
    apply forall_congr'
    intro named
    apply imp_congr
    · rw [attempt]
      exact requests owner _
    · exact or_congr Iff.rfl (frontier named)

private theorem RawReplayState.admission
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference first second : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (firstTrace : (nativeProtocol).Trace (some first))
    (secondTrace : (nativeProtocol).Trace (some second))
    (related : RawReplayState setup implementation who target reference lost
      ⟨some first, firstTrace⟩ ⟨some second, secondTrace⟩)
    (event : (serviceGraph setup .concurrent).EventId)
    (request : first.execution.application.SeedRequest who
      ⟨first.execution.application.attempt, event⟩)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    bindingAdmissionBit setup implementation who event ⟨some second, secondTrace⟩ tape =
      bindingAdmissionBit setup implementation who event ⟨some first, firstTrace⟩ tape := by
  classical
  obtain ⟨_remaining, _actor, execution, recalled, observed⟩ := related
  have application := congrArg (fun execution : (nativeApplication).Execution =>
    execution.application) execution
  change second.execution.application = sourceSnapshotAssignment setup implementation
    target reference lost first.execution.application at application
  have publicEq : second.execution.application.publicView =
      first.execution.application.publicView := by
    rw [application]
    exact sourceSnapshotAssignment_public setup implementation target reference lost _
  have network := congrArg (fun execution : (nativeApplication).Execution => execution.network)
    execution
  change second.execution.network = first.execution.network at network
  have service := congrArg
    (fun execution : (nativeApplication).Execution => execution.environmentRecall) execution
  change second.execution.environmentRecall = first.execution.environmentRecall at service
  have requests (owner : Player) (coordinate : CommitAttemptEvent
      (serviceGraph setup .concurrent)) :
      second.execution.application.SeedRequest owner coordinate ↔
        first.execution.application.SeedRequest owner coordinate := by
    rw [application]
    exact Iff.rfl
  have actualRequest : second.execution.application.SeedRequest who
      ⟨second.execution.application.attempt, event⟩ := by
    rw [application]
    exact request
  have firstCount := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
      firstTrace)
  have secondCount := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
      secondTrace)
  have outputs (owner : Player) :
      (nativeApplication).outputs (second.execution.recall owner) =
        (nativeApplication).outputs (first.execution.recall owner) := by
    rw [← secondCount.1 owner, ← firstCount.1 owner, network]
  have phases := congrArg (fun state : PhaseRuntimeState (serviceGraph setup .concurrent) =>
    state.phases) application
  change second.execution.application.phases = first.execution.application.phases at phases
  have entry := congrArg (fun state : PhaseRuntimeState (serviceGraph setup .concurrent) =>
    state.entry.excluded) application
  change second.execution.application.entry.excluded =
    first.execution.application.entry.excluded at entry
  have word (leftMaterial rightMaterial : WitnessedSubmission (serviceGraph setup .concurrent))
      (leftHandle rightHandle : Handle (serviceGraph setup .concurrent))
      (leftCall : leftMaterial.call.packet = .commitment event leftHandle)
      (rightCall : rightMaterial.call.packet = .commitment event rightHandle)
      (owner : Player) (named : (serviceGraph setup .concurrent).EventId) :
      ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
          (second.execution.respond nativeApplication who ⟨some leftMaterial⟩) owner named ↔
        ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
          (first.execution.respond nativeApplication who ⟨some rightMaterial⟩) owner named := by
    by_cases focal : owner = who
    · subst owner
      exact sourceReplay_focal_sent_word_congr setup implementation second.execution
        first.execution publicEq service tape who event named actualRequest request
          leftHandle rightHandle leftMaterial rightMaterial leftCall rightCall
    · exact (ReservedEpoch.ownedAcceptanceWord_respond_foreign implementation.runtime
        implementation.leaks tape second.execution who owner focal ⟨some leftMaterial⟩
          named).trans
        ((sourceReplay_owned_word_congr setup implementation second.execution first.execution
          publicEq requests network service outputs tape owner named).trans
            (ReservedEpoch.ownedAcceptanceWord_respond_foreign implementation.runtime
              implementation.leaks tape first.execution who owner focal ⟨some rightMaterial⟩
                named).symm)
  dsimp only [bindingAdmissionBit]
  split
  next actualOffered =>
    split
    next originalOffered =>
      obtain ⟨_leftAvailable, _leftPayload, _leftValue, leftSerial, _leftBinding, leftCall,
          _leftPrepared⟩ := Classical.choose_spec actualOffered
      obtain ⟨_rightAvailable, _rightPayload, _rightValue, rightSerial, _rightBinding, rightCall,
          _rightPrepared⟩ := Classical.choose_spec originalOffered
      apply decide_eq_decide.mpr
      rw [phases, entry]
      apply exists_congr
      intro phase
      apply and_congr Iff.rfl
      apply and_congr Iff.rfl
      apply forall_congr'
      intro named
      apply imp_congr Iff.rfl
      apply forall_congr'
      intro owner
      apply imp_congr Iff.rfl
      apply imp_congr Iff.rfl
      exact word (Classical.choose actualOffered) (Classical.choose originalOffered)
        (who, .prepared leftSerial) (who, .prepared rightSerial) leftCall rightCall owner named
    next absent =>
      apply (absent ?_).elim
      obtain ⟨material, available, proper⟩ := actualOffered
      exact ⟨material, by simpa only [recalled, observed] using available, proper⟩
  next absent =>
    split
    next originalOffered =>
      apply (absent ?_).elim
      obtain ⟨material, available, proper⟩ := originalOffered
      exact ⟨material, by simpa only [recalled, observed] using available, proper⟩
    next _ => rfl

open Classical in
/-- Only a retained lost slot contributes a new queried value atom. The
original signed call fixes its event; the query is evaluated at the actual
reconstructed callback input. -/
def sourceReplayLostDrawAtom
    (owner : Player) (execution : (nativeApplication).Execution)
    (original : (nativeApplication).Action)
    (choice : RawReplayChoice setup implementation) : ℝ≥0∞ :=
  match choice.1 with
  | none => 1
  | some (_, ⟨payload, value⟩) => match original.transmission with
    | none => 0
    | some material => match material.call.packet with
      | .commitment event _ =>
        if binding : (serviceGraph setup .concurrent).outputLayout event =
            .binding owner payload then
          match phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
              implementation.plan owner event (execution.recall owner)
                (execution.observe nativeApplication owner) with
          | none => 0
          | some key => ((values owner key).map (fun sampled => phaseRecoveryDomainValue setup
              .concurrent event owner payload binding sampled.val.val)) value
        else 0
      | .opening .. | .malformed .. => 0

open Classical in
/-- The raw alias atom is taken in the genuine menu at this exact input.
Legality proofs identify the response subtype without adding multiplicity. -/
def sourceReplayAliasAtom
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (choice : RawReplayChoice setup implementation) : ℝ≥0∞ :=
  match choice.2 with
  | none => 0
  | some action =>
    if offered : action ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) then
      sourceReplayAliases setup implementation scale owner execution choice.1
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) ⟨action, offered⟩) choice
    else 0

private theorem sourceReplayCallbackAtoms_factor
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) (original : (nativeApplication).Action)
    (kernel : PMF (RawReplayChoice setup implementation))
    (atoms : SourceReplayCallbackAtoms (setup := setup) (values := values)
      (implementation := implementation) scale owner execution target reference original kernel)
    (choice : RawReplayChoice setup implementation) (supported : choice ∈ kernel.support) :
    kernel choice = sourceReplayLostDrawAtom setup values implementation owner execution
      original choice *
        sourceReplayAliasAtom setup implementation scale owner execution choice := by
  classical
  obtain ⟨_tag, response, responseEq, _proper, aliases | lost⟩ := atoms choice supported
  · have aliasEq : sourceReplayAliasAtom setup implementation scale owner execution choice =
        sourceReplayAliases setup implementation scale owner execution choice.1
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) choice := by
      simp only [sourceReplayAliasAtom, responseEq, dite_eq_left response.property]
    rw [aliasEq, aliases.2]
    simp only [sourceReplayLostDrawAtom, aliases.1, one_mul]
  · obtain ⟨event, payload, binding, key, handle, value,
        ⟨material, transmitted, packet⟩, queried, drawn, _prepared, atom⟩ := lost
    have aliasEq : sourceReplayAliasAtom setup implementation scale owner execution choice =
        sourceReplayAliases setup implementation scale owner execution choice.1
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) choice := by
      simp only [sourceReplayAliasAtom, responseEq, dite_eq_left response.property]
    rw [aliasEq, atom]
    congr 1
    simp only [sourceReplayLostDrawAtom, drawn, transmitted, packet, dite_eq_left binding, queried]

/-- Chronological lost-draw and alias products of one actual augmented replay.
Nonforeign transitions contribute no factor; every foreign callback retains
its actual input, including WAIT and already-sent callbacks. -/
def sourceReplayScriptProducts
    (scale : Set.Icc (0 : ℝ) 1) (who : Player) :
    (nativeProtocol).History → (nativeProtocol).History →
      List (RawReplayChoice setup implementation) → ℝ≥0∞ × ℝ≥0∞
  | ⟨_, .start⟩, _, [] => (1, 1)
  | ⟨_, .extend prior joint _ _⟩, actual, choice :: script =>
    let earlier := sourceReplayScriptProducts scale who ⟨_, prior⟩ actual.prior script
    match (nativeApplication).actor (⟨_, prior⟩ : (nativeProtocol).History).state with
    | none => earlier
    | some owner => if owner = who then earlier else
      match actual.prior.state with
      | none => (0, 0)
      | some previous =>
        (earlier.1 * sourceReplayLostDrawAtom setup values implementation owner previous.execution
          ((joint owner).getD ⟨none⟩) choice,
          earlier.2 * sourceReplayAliasAtom setup implementation scale owner previous.execution
            choice)
  | _, _, _ => (0, 0)

/-- The chronological product at an actual trace extension. -/
private theorem sourceReplayScriptProducts_extend
    (scale : Set.Icc (0 : ℝ) 1) (who : Player)
    {before after : (nativeProtocol).State} (prior : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support)
    (actual : (nativeProtocol).History) (choice : RawReplayChoice setup implementation)
    (script : List (RawReplayChoice setup implementation)) :
    sourceReplayScriptProducts setup values implementation scale who
        ⟨after, prior.extend joint legal moved⟩ actual (choice :: script) =
      let earlier := sourceReplayScriptProducts setup values implementation scale who
        ⟨before, prior⟩ actual.prior script
      match (nativeApplication).actor before with
      | none => earlier
      | some owner => if owner = who then earlier else
        match actual.prior.state with
        | none => (0, 0)
        | some previous =>
          (earlier.1 * sourceReplayLostDrawAtom setup values implementation owner previous.execution
            ((joint owner).getD ⟨none⟩) choice,
            earlier.2 * sourceReplayAliasAtom setup implementation scale owner previous.execution
              choice) := by
  rfl

/-- The actual normalized script atom is exactly its chronological product
of mapped lost-value atoms and actual-menu alias atoms. This uses the same
replay prefixes as the constructor and introduces no independent kernel. -/
private theorem sourceReplayScriptMass_factor
    (scale : Set.Icc (0 : ℝ) 1) (who : Player)
    (target : setup.proposalRecoveryProtocol.History) (reference : (nativeApplication).Control)
    (original : (nativeProtocol).History) (script : List (RawReplayChoice setup implementation))
    (mass : ℝ≥0∞)
    (supported : SourceReplayScriptMass (setup := setup) (values := values)
      (implementation := implementation) scale who target reference original script mass)
    (actual : (nativeProtocol).History)
    (replayed : sourceRawReplay setup implementation who target reference original script =
      some actual) :
    let products := sourceReplayScriptProducts setup values implementation scale who original
      actual script
    mass = products.1 * products.2 := by
  classical
  dsimp only
  induction supported generalizing actual with
  | start =>
      change (1 : ℝ≥0∞) = 1 * 1
      exact (mul_one 1).symm
  | @deterministic before after prior joint legal moved script mass quiet earlier ih =>
      obtain ⟨previous, previousReplay, priorEq⟩ := sourceRawReplay_step_prior setup implementation
        who target reference prior joint legal moved (none, none) script actual replayed
      have previousAtom := ih previous previousReplay
      rw [sourceReplayScriptProducts_extend, priorEq]
      rcases quiet with quiet | quiet
      · simpa only [quiet] using previousAtom
      · simpa only [quiet, ↓reduceIte] using previousAtom
  | @foreign before after prior joint legal moved script mass owner different acting previous
      previousTrace previousReplay _related kernel atoms _description choice member earlier ih =>
      obtain ⟨older, olderReplay, priorEq⟩ := sourceRawReplay_step_prior setup implementation
        who target reference prior joint legal moved choice script actual replayed
      have same : older = (⟨some previous, previousTrace⟩ : (nativeProtocol).History) :=
        Option.some.inj (olderReplay.symm.trans previousReplay)
      rw [same] at priorEq
      have previousAtom := ih ⟨some previous, previousTrace⟩ previousReplay
      have callbackAtom := sourceReplayCallbackAtoms_factor setup values implementation scale
        owner previous.execution target reference ((joint owner).getD ⟨none⟩) kernel atoms
          choice member
      rw [sourceReplayScriptProducts_extend, priorEq]
      simp only [ReactiveApplication.actor, Option.bind_some, acting, ite_eq_right different]
      rw [callbackAtom, previousAtom]
      ring

theorem sourceRawReplay_qualified
    (operational : implementation.Operational)
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference
      (sourceCutTrace setup implementation referenceTrace) who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (alignment : SourceReplayAlignment (setup := setup) (values := values)
      (implementation := implementation) operational who reference referenceTrace event cut g
        sourceChoice targetCurrent targetTrace)
    (good : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner ⟨some reference, referenceTrace⟩)
    (scale nativeBad : Set.Icc (0 : ℝ) 1) (scalePositive : 0 < scale.val)
    (nativeProfile : ∀ owner, ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        nativeInitial implementation.horizon implementation.scheduler values
          ⟨nativeBad, scale, scale, scale⟩)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapeSupported : prefixTapeLaw setup implementation ⟨some reference, referenceTrace⟩ tape ≠ 0)
    (admitted : bindingAdmissionBit setup implementation who event
      ⟨some reference, referenceTrace⟩ tape = true) :
    ∃ law : SourceRawReplayLaw (setup := setup) (values := values)
        (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
          ⟨some reference, referenceTrace⟩,
      ∃ selected : ∀ script, script ∈ law.choices.support →
        ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).InformationHistory who
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).infoOf who referenceTrace),
        let nativeLaw := law.choices.bindOnSupport
          (fun script member => PMF.pure (selected script member))
        (∀ script (member : script ∈ law.choices.support),
          sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
              ⟨some reference, referenceTrace⟩ script = some (selected script member).val ∧
          mechanicalWord setup implementation who (selected script member).val.trace =
            mechanicalWord setup implementation who referenceTrace ∧
          ((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).historyReachWeight nativeProfile
              (selected script member).val ≠ 0 ∧
          prefixTapeLaw setup implementation (selected script member).val tape ≠ 0 ∧
          (∀ owner, owner ≠ who →
            ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
              implementation.leaks implementation.bounds nativeInitial implementation.horizon
                implementation.scheduler owner (selected script member).val) ∧
          (selected script member).val.state.elim True (fun control =>
            who ∉ control.execution.application.current.excluded) ∧
          bindingAdmissionBit setup implementation who event
            (selected script member).val tape = true) ∧
        (∀ script (member : script ∈ law.choices.support),
          sourceRawReplayReadback setup implementation who
            ⟨some targetCurrent, targetTrace⟩ reference ⟨some reference, referenceTrace⟩
              (selected script member).val = some script) ∧
        (∀ actual, actual ∈ nativeLaw.support ↔
          ∃ script, ∃ member : script ∈ law.choices.support,
            selected script member = actual) ∧
        (∀ script (member : script ∈ law.choices.support),
          let products := sourceReplayScriptProducts setup values implementation scale who
            ⟨some reference, referenceTrace⟩ (selected script member).val script
          nativeLaw (selected script member) = products.1 * products.2) ∧
        SourceRawReplayLaw.coversOriginalAnnotations setup values implementation operational who
          reference referenceTrace event g targetCurrent targetTrace scale law := by
  classical
  have full : ∀ owner
      (site : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).InformationSite owner)
      (choice : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).Choice owner site.1),
      choice ∈ (nativeProfile owner site.1).support := by
    rw [nativePrescribed]
    exact phaseProposalReferenceStrategy_fullSupport setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan nativeInitial
        implementation.horizon implementation.scheduler values ⟨nativeBad, scale, scale, scale⟩
          scalePositive
  obtain ⟨law, coverage⟩ := sourceRawReplay_law (setup := setup) (values := values)
    (implementation := implementation) operational who reference referenceTrace event cut g
      sourceChoice targetCurrent targetTrace alignment good scale
  have qualified : ∀ script ∈ law.choices.support,
        ∃ actual : ((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).InformationHistory who
              (((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).infoOf who referenceTrace),
          sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
              ⟨some reference, referenceTrace⟩ script = some actual.val ∧
          mechanicalWord setup implementation who actual.val.trace =
            mechanicalWord setup implementation who referenceTrace ∧
          ((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).historyReachWeight nativeProfile actual.val ≠ 0 ∧
          prefixTapeLaw setup implementation actual.val tape ≠ 0 ∧
          (∀ owner, owner ≠ who →
            ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
              implementation.leaks implementation.bounds nativeInitial implementation.horizon
                implementation.scheduler owner actual.val) ∧
          actual.val.state.elim True (fun control =>
            who ∉ control.execution.application.current.excluded) ∧
          bindingAdmissionBit setup implementation who event actual.val tape = true := by
    intro script member
    obtain ⟨actual, replayed, related, word, actualGood⟩ := law.replayed script member
    rcases actual with ⟨state, trace⟩
    cases state with
    | none => cases related
    | some control =>
      obtain ⟨remaining, actor, execution, recalled, observed⟩ := related
      have active : control.actor = some who := actor.trans cut.active
      have information : ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).infoOf who trace =
        ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).infoOf who referenceTrace := by
        change ((nativeMenu).signals nativeInitial implementation.horizon
            implementation.scheduler).infoOf who trace =
          ((nativeMenu).signals nativeInitial implementation.horizon
            implementation.scheduler).infoOf who referenceTrace
        rw [(nativeMenu).info nativeInitial implementation.horizon implementation.scheduler
          who trace, (nativeMenu).info nativeInitial implementation.horizon
            implementation.scheduler who referenceTrace]
        simp only [ReactiveApplication.observe, active, cut.active, ↓reduceIte]
        exact congrArg some (Prod.ext recalled observed)
      let selected : ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).InformationHistory who
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).infoOf who referenceTrace) :=
        ⟨⟨some control, trace⟩, information⟩
      refine ⟨selected, replayed, word, ?_, ?_, actualGood, ?_, ?_⟩
      · exact ne_of_gt (((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).historyReachWeight_pos_of_fullSupport nativeProfile full
            selected.val)
      · have service := congrArg
          (fun execution : (nativeApplication).Execution => execution.environmentRecall) execution
        change control.execution.environmentRecall = reference.execution.environmentRecall
          at service
        simpa only [selected, prefixTapeLaw, service] using tapeSupported
      · change who ∉ control.execution.application.current.excluded
        have application := congrArg (fun execution : (nativeApplication).Execution =>
          execution.application) execution
        change control.execution.application = sourceSnapshotAssignment setup implementation
          ⟨some targetCurrent, targetTrace⟩ reference (rawReplayLost setup implementation script)
            reference.execution.application at application
        rw [application]
        exact cut.request.2.2.2.2
      · exact (RawReplayState.admission setup implementation who ⟨some targetCurrent, targetTrace⟩
          reference reference control (rawReplayLost setup implementation script) referenceTrace
            trace ⟨remaining, actor, execution, recalled, observed⟩ event cut.request tape).trans
              admitted
  let selected := fun script member => (qualified script member).choose
  have properties := fun script member => (qualified script member).choose_spec
  refine ⟨law, selected, properties, ?_, ?_, ?_, coverage⟩
  · intro script member
    exact sourceRawReplay_readback setup values implementation scale who
      ⟨some targetCurrent, targetTrace⟩ reference ⟨some reference, referenceTrace⟩
        script (law.choices script) (law.atoms script member)
          (selected script member).val (properties script member).1
  · intro actual
    constructor
    · intro supported
      obtain ⟨script, member, image⟩ :=
        (PMF.mem_support_bindOnSupport_iff ..).mp supported
      exact ⟨script, member,
        ((PMF.mem_support_pure_iff ..).mp image).symm⟩
    · rintro ⟨script, member, rfl⟩
      apply (PMF.mem_support_bindOnSupport_iff ..).mpr
      exact ⟨script, member, by simp⟩
  · intro script member
    calc
      _ = law.choices script := by
        apply bindOnSupport_pure_apply_of_injective law.choices
        · intro first firstMember second secondMember same
          apply SourceRawReplayLaw.replay_injective setup values implementation scale who
            ⟨some targetCurrent, targetTrace⟩ reference ⟨some reference, referenceTrace⟩ law
              first second firstMember secondMember (selected first firstMember).val
                (properties first firstMember).1
          exact (properties second secondMember).1.trans
            (congrArg (fun h => some (Subtype.val h)) same.symm)
        · exact member
      _ = _ := sourceReplayScriptMass_factor setup values implementation scale who
        ⟨some targetCurrent, targetTrace⟩ reference ⟨some reference, referenceTrace⟩ script
          (law.choices script) (law.atoms script member) (selected script member).val
            (properties script member).1

end Vegas.PhaseProposalQualifiedBinding

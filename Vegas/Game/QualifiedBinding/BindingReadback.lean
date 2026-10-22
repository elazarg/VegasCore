/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.OrdinaryContinuation

/-! # Literal binding origins and assigned native reads -/

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
/-- Full focal information aligns every source prefix at its literal depth.
The corresponding prefix retains the complete focal information there. -/
theorem source_information_prefix
    (who : Player) (left right earlier : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryModel.infoOf who left.trace =
      setup.proposalRecoveryModel.infoOf who right.trace)
    (kept : TracePrefix earlier.trace left.trace) :
    ∃ other : setup.proposalRecoveryProtocol.History,
      TracePrefix other.trace right.trace ∧ other.trace.length = earlier.trace.length ∧
        setup.proposalRecoveryModel.infoOf who earlier.trace =
          setup.proposalRecoveryModel.infoOf who other.trace := by
  rcases earlier with ⟨state, trace⟩
  cases trace with
  | start =>
      exact ⟨setup.proposalRecoveryProtocol.initHistory, TracePrefix.start right.trace, rfl, rfl⟩
  | @extend before after prior joint legal reached =>
      obtain ⟨otherBefore, otherAfter, other, choices, offered, moved, otherKept,
        _beforeInfo, afterInfo, _own⟩ := source_information_row setup who prior joint legal
          reached left.trace right.trace kept same
      refine ⟨⟨otherAfter, other.extend choices offered moved⟩, otherKept, ?_, afterInfo⟩
      have lengths := congrArg (fun information => information.1.2.length) afterInfo
      change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who
          (prior.extend joint legal reached)).1.2.length =
        (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who
          (other.extend choices offered moved)).1.2.length at lengths
      rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at lengths
      simpa only [setup.source_signal_depth] using lengths.symm

omit [Fintype Player] in
/-- The complete source chronology has a depth-preserving correspondence in
both directions on each full focal information fiber. Hidden foreign cause
labels are retained in the corresponding target prefix. -/
theorem source_prefix_correspondence
    (who : Player) (left right : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryModel.infoOf who left.trace =
      setup.proposalRecoveryModel.infoOf who right.trace) :
    ∃ correspondence :
        {earlier : setup.proposalRecoveryProtocol.History // TracePrefix earlier.trace left.trace} ≃
        {earlier : setup.proposalRecoveryProtocol.History // TracePrefix earlier.trace right.trace},
      ∀ earlier,
        (correspondence earlier).val.trace.length = earlier.val.trace.length ∧
          setup.proposalRecoveryModel.infoOf who earlier.val.trace =
            setup.proposalRecoveryModel.infoOf who (correspondence earlier).val.trace := by
  classical
  let forward := fun earlier : {earlier : setup.proposalRecoveryProtocol.History //
      TracePrefix earlier.trace left.trace} =>
    source_information_prefix setup who left right earlier.val same earlier.property
  let backward := fun earlier : {earlier : setup.proposalRecoveryProtocol.History //
      TracePrefix earlier.trace right.trace} =>
    source_information_prefix setup who right left earlier.val same.symm earlier.property
  let toTarget := fun earlier : {earlier : setup.proposalRecoveryProtocol.History //
      TracePrefix earlier.trace left.trace} =>
    (⟨Classical.choose (forward earlier), (Classical.choose_spec (forward earlier)).1⟩ :
      {earlier : setup.proposalRecoveryProtocol.History // TracePrefix earlier.trace right.trace})
  let toSource := fun earlier : {earlier : setup.proposalRecoveryProtocol.History //
      TracePrefix earlier.trace right.trace} =>
    (⟨Classical.choose (backward earlier), (Classical.choose_spec (backward earlier)).1⟩ :
      {earlier : setup.proposalRecoveryProtocol.History // TracePrefix earlier.trace left.trace})
  have targetDepth (earlier) : (toTarget earlier).val.trace.length = earlier.val.trace.length :=
    (Classical.choose_spec (forward earlier)).2.1
  have sourceDepth (earlier) : (toSource earlier).val.trace.length = earlier.val.trace.length :=
    (Classical.choose_spec (backward earlier)).2.1
  let correspondence :
      {earlier : setup.proposalRecoveryProtocol.History // TracePrefix earlier.trace left.trace} ≃
      {earlier : setup.proposalRecoveryProtocol.History // TracePrefix earlier.trace right.trace} :=
    { toFun := toTarget
      invFun := toSource
      left_inv := fun earlier => Subtype.ext
        ((toSource (toTarget earlier)).property.eq_of_same_length earlier.property
          ((sourceDepth (toTarget earlier)).trans (targetDepth earlier)))
      right_inv := fun earlier => Subtype.ext
        ((toTarget (toSource earlier)).property.eq_of_same_length earlier.property
          ((targetDepth (toSource earlier)).trans (sourceDepth earlier))) }
  refine ⟨correspondence, fun earlier => ⟨targetDepth earlier, ?_⟩⟩
  exact (Classical.choose_spec (forward earlier)).2.2

/-- A live binding read uses the whole historical window. Only exclusions
inside its current attempt are normalized; the proposal coordinate is read
from this actual sender's complete initialized traffic. -/
theorem source_query_of_live_window
    (operational : implementation.Operational)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup .concurrent).EventId)
    (current : CommitRecoveryState setup.program)
    (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (typed : phaseVirtualSourceView? setup .concurrent implementation.runtime
      implementation.leaks owner event (execution.observe nativeApplication owner) =
        some (ProtocolView.eraseHistory owner setup.program
          (ProtocolState.observe owner setup.program current.point)))
    (proposals : setup.proposalRecoveryArchive owner
        (setup.proposalRecoveryModel.infoOf owner sourceTrace) =
      PhaseProposal.sourceArchive execution.network.inputs)
    (cut : Nat) (excluded : Finset Player) :
    let publicView := (execution.observe nativeApplication owner).application.2
    let footprint := publicView.native.sourceFailureFootprint
    let inherited := (publicView.retired.map fun record =>
      record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅
    let actualRead := setup.commitRecoveryErasedRead owner
      (ProtocolView.eraseHistory owner setup.program
        (ProtocolState.observe owner setup.program current.point))
      (inherited ∪ footprint.1 publicView.attempt.phase,
        publicView.attempt.generation, publicView.attempt.phase)
      ((publicView.sourcePublicAddressWord implementation.plan event.val).reverse ++
        [(none, (∅, 0, 0))])
    let sourceRead := setup.commitRecoveryErasedInformation owner
      (setup.commitRecoveryModel.infoOf owner (setup.proposalRecoveryEraseTrace sourceTrace))
    actualRead.1.1.1.elim false (ProtocolView.atCommit owner setup.program) = true →
    sourceRead.1.1.1.elim false (ProtocolView.atCommit owner setup.program) = true →
    owner ∉ actualRead.1.1.2.1 → owner ∉ sourceRead.1.1.2.1 → owner ∉ excluded →
    setup.commitRecoveryAttemptStart owner actualRead = cut →
    setup.commitRecoveryAttemptStart owner sourceRead = cut →
    setup.commitRecoverySavedExclusions owner actualRead = excluded →
    setup.commitRecoverySavedExclusions owner sourceRead = excluded →
    List.Forall₂ (fun first second => first.1 = second.1 ∧ first.2.2 = second.2.2)
      (actualRead.1.1 :: actualRead.1.2) (sourceRead.1.1 :: sourceRead.1.2) →
    (actualRead.1.1 :: actualRead.1.2).reverse.take cut =
      (sourceRead.1.1 :: sourceRead.1.2).reverse.take cut →
    phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) =
      some (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner sourceTrace)) := by
  classical
  intro publicView footprint inherited actualRead sourceRead
    actualCommit sourceCommit actualActive sourceActive entryActive actualCut sourceCut
    actualEntry sourceEntry controls past
  have normalized : setup.commitRecoveryNoMissInformation owner actualRead =
      setup.commitRecoveryNoMissInformation owner sourceRead :=
    setup.commitRecoveryNoMissInformation_eq_of_window owner actualRead sourceRead cut
      excluded rfl rfl actualCommit sourceCommit actualActive sourceActive entryActive
        actualCut sourceCut actualEntry sourceEntry controls past
  have semantic : phaseVirtualSourceQuery? setup .concurrent implementation.runtime
      implementation.leaks implementation.plan owner event
        (execution.observe nativeApplication owner) =
      some (setup.commitRecoveryErasedInformation owner
        (setup.commitRecoveryNoMissInformation owner
          (setup.commitRecoveryModel.infoOf owner
            (setup.proposalRecoveryEraseTrace sourceTrace)))) := by
    unfold phaseVirtualSourceQuery?
    rw [typed, Option.map_some]
    change some (setup.commitRecoveryErasedInformation owner
      (setup.commitRecoveryNoMissInformation owner actualRead)) = _
    rw [normalized]
    dsimp only [sourceRead]
    rw [← setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryErasedInformation_idempotent]
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have counted : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace
        (some ⟨remaining, some owner, execution⟩) := initialEq ▸ trace
  have archive := PhaseProposal.observedSourceArchive_eq_submitted implementation.runtime
    implementation.leaks operational.completePending
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler
        (⟨remaining, some owner, execution⟩ : (nativeApplication).Control)
          ((nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler counted)
            owner rfl
  unfold phaseProposalQuery? Setup.proposalRecoveryQuery
  rw [semantic, Option.map_some, setup.proposalRecoveryEraseInfo_observed, archive, proposals]

/-- Every accepted current, saved or retired snapshot binding has its actual
source row in the selected chronology, retaining the raw image before restore. -/
theorem source_admitted_binding_row
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (before : (nativeApplication).Control)
    (prior : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before))
    (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (owner : Player) (payload : L.Ty)
    (named : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted (.inr named) = some handle) :
    ∃ (record : (nativeApplication).PlayerEntry)
      (material : WitnessedSubmission (serviceGraph setup .concurrent))
      (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
      (current next : CommitRecoveryState setup.program)
      (sourcePrior : setup.proposalRecoveryProtocol.Trace (some current))
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
      (moved : some next ∈
        (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support),
      handle.1 = owner ∧ record ∈ reference.execution.recall owner ∧
      record.action.transmission = some material ∧ record.emitted = some message ∧
      message.payload.packet.call = .commitment named handle ∧
      (message.id, true) ∈ reference.execution.receipts ∧
      TracePrefix (sourcePrior.extend joint legal moved) cut.completed.trace ∧
      current.generation = message.payload.attempt.generation ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.saved = message.payload.attempt.phase ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.point = named.val ∧
      owner ∉ current.excluded ∧ owner ∉ next.excluded ∧
      phaseRecoveryBindingData setup .concurrent named owner payload binding
        ((joint owner).map (·.semantic)) =
          (reference.execution.application.current.native.bindingResult handle payload, false) ∧
      (TracePrefix (sourcePrior.extend joint legal moved) cut.trace ∨
        (TracePrefix cut.trace sourcePrior ∧
          message.payload.attempt = reference.execution.application.attempt ∧ owner ≠ who)) ∧
      (TracePrefix (sourcePrior.extend joint legal moved) cut.cursor.trace ∨
        message.payload.attempt = reference.execution.application.attempt) := by
  classical
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  obtain ⟨priorNative, entryNative, traceNative, retainedNative, entryRetainedNative⟩ :
      ∃ (priorNative : (nativeProtocol).Trace (some before))
        (entryNative : (nativeProtocol).Trace (some cut.entry))
        (traceNative : (nativeProtocol).Trace (some reference)),
        TracePrefix priorNative traceNative ∧ TracePrefix entryNative traceNative := by
    rw [initialEq]
    exact ⟨prior, cut.entryTrace, trace, retained, cut.nativeRetained⟩
  let raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler traceNative
  obtain ⟨validSnapshot, catalogue⟩ := accepted_snapshot_catalogue setup implementation
    reference traceNative before priorNative retainedNative snapshot selected owner payload
      ⟨.inr named, binding⟩ handle accepted
  obtain ⟨otherPayload, typed⟩ := validSnapshot.accepted_typed (.inr named) handle accepted
  have owned : handle.1 = owner := (EventField.binding.inj (typed.symm.trans binding)).1
  obtain ⟨message, inclusionBefore, inclusionAfter, inclusionTrace, inclusionJoint,
      inclusionLegal, inclusionMoved, includedNative, inclusionRetained, input, receipt,
      sender, call, inclusionNamespace, inclusionHandled, inclusionFound, rawHandled,
      rawAccepted, inclusionEffect, inclusionNormalized⟩ :=
    accepted_binding_inclusion setup implementation reference traceNative before priorNative
      retainedNative
      snapshot selected named handle accepted
  obtain ⟨record, recorded, material, transmitted, emitted, _packet⟩ :=
    ((nativeApplication).history_provenance nativeInitial implementation.horizon
      implementation.scheduler raw).inputs message input
  rw [sender, owned] at recorded
  have inclusionPrefix : TracePrefix inclusionTrace traceNative :=
    (TracePrefix.extend .refl inclusionJoint inclusionLegal inclusionMoved).trans inclusionRetained
  let inclusionWitness :=
    (checkpointSelection setup implementation operational inclusionTrace).val
  obtain ⟨inclusionReady, _timely, _actualOwner, _actualPayload, _actualBinding,
      _actualCode, _node, _sender, _owner, _vacant, _unused⟩ :=
    handle_commitment_conditions implementation.runtime
      inclusionBefore.execution.application.current.native includedNative message.id named handle
        (by simpa only [call] using rawHandled)
  obtain ⟨actualPhase, actualRemaining, actualInstalled, actualCommitment, namedInside⟩ :=
    phase_ready_binding_phase implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      (by
        have initialEq : (setup.initialLaw.map encodeInputs).map
            (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp ..
        rw [initialEq]
        exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler inclusionTrace) owner named payload binding inclusionReady
  have inclusionGeometry := source_checkpoint_binding_interval setup implementation inclusionWitness
    operational.maximalPhases actualPhase actualRemaining actualInstalled actualCommitment
  let rawInclusion := inclusionBefore.execution.application.current.inclusionResult
    message.payload.packet.call includedNative
  have inclusionOrdered : inclusionBefore.execution.application.Ordered :=
    inclusionWitness.receipts.exclusion.frontier.adjacent
  have includedAccepted : rawInclusion.native.accepted (.inr named) = some handle := rawAccepted
  have inclusionPresent : actualPhase ∈ inclusionBefore.execution.application.phases.head? := by
    simp only [actualInstalled, List.head?_cons, Option.mem_some_iff]
  have actualImage :
      (message.payload.attempt = reference.execution.application.attempt ∧
        reference.execution.application.current.native.accepted (.inr named) = some handle) ∨
      ∃ (exitBefore exitAfter : (nativeApplication).Control)
        (exitTrace : (nativeProtocol).Trace (some exitBefore))
        (exitJoint : Player → Option (nativeApplication).Action)
        (exitLegal : (nativeProtocol).Legal (some exitBefore) exitJoint)
        (exitMoved : some exitAfter ∈
          ((nativeProtocol).step (some exitBefore) ⟨exitJoint, exitLegal⟩).support)
        (rawImage : RecoveryState (serviceGraph setup .concurrent)),
        TracePrefix inclusionTrace exitTrace ∧
        TracePrefix (exitTrace.extend exitJoint exitLegal exitMoved) traceNative ∧
        exitBefore.execution.application.attempt = message.payload.attempt ∧
        exitAfter.execution.application.attempt ≠ exitBefore.execution.application.attempt ∧
        actualPhase ∈ exitBefore.execution.application.phases.head? ∧
        exitAfter.execution.application =
          ({ exitBefore.execution.application with current := rawImage } :
            PhaseRuntimeState (serviceGraph setup .concurrent)).normalize ∧
        actualPhase.Finished (actualPhase.drain rawImage) ∧
        PhaseClosingEffect implementation.runtime implementation.leaks
          exitBefore.execution exitAfter.execution rawImage ∧
        (actualPhase.drain rawImage).native.accepted (.inr named) = some handle := by
    by_cases immediate :
        inclusionAfter.execution.application.attempt ≠ inclusionBefore.execution.application.attempt
    · refine Or.inr ⟨inclusionBefore, inclusionAfter, inclusionTrace, inclusionJoint,
        inclusionLegal, inclusionMoved, rawInclusion, .refl, inclusionRetained,
        inclusionNamespace.symm, immediate, inclusionPresent, inclusionNormalized, ?_,
        inclusionEffect, ?_⟩
      · apply PhaseRuntimeState.finished_of_normalize_attempt_ne
          ({ inclusionBefore.execution.application with current := rawInclusion } :
            PhaseRuntimeState (serviceGraph setup .concurrent)) actualPhase inclusionPresent
        change (PhaseRuntimeState.normalize
          { inclusionBefore.execution.application with current := rawInclusion }).attempt ≠
            inclusionBefore.execution.application.attempt
        rw [← inclusionNormalized]
        exact immediate
      · rw [(actualPhase.drain_tables rawInclusion).1]
        exact includedAccepted
    · have sameAttempt : inclusionBefore.execution.application.attempt =
          inclusionAfter.execution.application.attempt := (not_ne_iff.mp immediate).symm
      have afterAccepted :
          inclusionAfter.execution.application.current.native.accepted (.inr named) =
            some handle := by
        rw [inclusionNormalized]
        apply PhaseRuntimeState.normalize_preserves_accepted
          ({ inclusionBefore.execution.application with current := rawInclusion } :
            PhaseRuntimeState (serviceGraph setup .concurrent)) inclusionOrdered
        · change inclusionBefore.execution.application.attempt =
            (PhaseRuntimeState.normalize
              { inclusionBefore.execution.application with current := rawInclusion }).attempt
          rw [← inclusionNormalized]
          exact sameAttempt
        · exact includedAccepted
      have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
        intro state member
        obtain ⟨draw, _supported, equal⟩ := PMF.support_map .. ▸ member
        cases equal
        exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
      have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
        (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
        inclusionBefore inclusionAfter inclusionTrace
        (inclusionTrace.extend inclusionJoint inclusionLegal inclusionMoved)
        (TracePrefix.extend («E» := nativeProtocol) (prefixTrace := inclusionTrace)
          (prior := inclusionTrace) (source := some inclusionBefore) (target := some inclusionAfter)
          .refl inclusionJoint inclusionLegal inclusionMoved)
        inclusionOrdered sameAttempt
      have phaseAfter : actualPhase ∈ inclusionAfter.execution.application.phases.head? := by
        have phasesEq := congrArg Prod.fst metadata
        change inclusionBefore.execution.application.phases =
          inclusionAfter.execution.application.phases at phasesEq
        rw [← phasesEq]
        exact inclusionPresent
      rcases accepted_attempt_image setup implementation reference inclusionAfter traceNative
          (inclusionTrace.extend inclusionJoint inclusionLegal inclusionMoved) inclusionRetained
          actualPhase phaseAfter named handle afterAccepted with live | exited
      · exact Or.inl ⟨inclusionNamespace.trans (sameAttempt.trans live.1), live.2⟩
      · obtain ⟨exitBefore, exitAfter, exitTrace, exitJoint, exitLegal, exitMoved, rawImage,
          afterToExit, exitRetained, exitAttempt, changed, phaseBefore, normalized,
          finished, _bindingInvariant, _coverage, effect, acceptedAtExit⟩ := exited
        exact Or.inr ⟨exitBefore, exitAfter, exitTrace, exitJoint, exitLegal, exitMoved,
          rawImage, (TracePrefix.extend .refl inclusionJoint inclusionLegal inclusionMoved).trans
            afterToExit, exitRetained, (sameAttempt.trans exitAttempt).symm.trans
            inclusionNamespace.symm, changed, phaseBefore, normalized, finished, effect,
          acceptedAtExit⟩
  obtain ⟨index, beforeExcluded, afterExcluded, nextRank, nextGeneration, nextLow,
      bounded, beforeAddress, afterAddress⟩ :=
    source_emitted_binding_address setup values implementation operational reference trace
      who event cut owner record recorded material transmitted message emitted named handle
        payload binding call
  obtain ⟨sourceState, targetState, sourcePrior, joint, legal, moved, kept, depth,
      sourceAddress, targetAddress, _instruction⟩ :=
    source_address_row setup cut.completed.trace index bounded
  have sourceEq := Option.some.inj (sourceAddress.symm.trans beforeAddress)
  cases sourceState with
  | none => cases sourceEq
  | some current =>
      obtain ⟨next, nextSupport, targetEq⟩ := (PMF.mem_support_map_iff ..).mp moved
      cases targetEq
      have generation : current.generation = message.payload.attempt.generation :=
        congrArg (fun address => address.2.2.1) sourceEq
      have saved : instructionCount setup.program -
          ProtocolState.remaining setup.program current.saved = message.payload.attempt.phase :=
        congrArg (fun address => address.2.2.2) sourceEq
      have position : instructionCount setup.program -
          ProtocolState.remaining setup.program current.point = named.val :=
        Option.some.inj (congrArg Prod.fst sourceEq)
      have cleanStartDepth
          (actualState canonicalState : CommitRecoveryState setup.program)
          (actualTrace : setup.commitRecoveryProtocol.Trace (some actualState))
          (canonicalTrace : setup.commitRecoveryProtocol.Trace (some canonicalState))
          (actualAddresses : (setup.recoveryAddressWord actualTrace).IsPrefix
            (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace)))
          (canonicalRetained : TracePrefix canonicalTrace
            (setup.proposalRecoveryEraseTrace cut.completed.trace))
          (actualBeforeEnd : actualTrace.length < cut.completed.trace.length)
          (sameControl : setup.commitRecoveryControl (some actualState) =
            setup.commitRecoveryControl (some canonicalState)) :
          actualTrace.length = canonicalTrace.length ∧
            actualState.excluded = canonicalState.excluded := by
        have endpoint : ∀ {state : setup.commitRecoveryProtocol.State}
            (path : setup.commitRecoveryProtocol.Trace state)
            (actual : CommitRecoveryState setup.program),
            state = some actual → ∃ slot, path.length = slot + 1 ∧
              (setup.recoveryAddressWord path)[slot]? = some actual.publicAddress := by
          intro state path
          cases path with
          | start => intro actual impossible; cases impossible
          | extend earlier actions offered realized =>
              intro actual equal
              cases equal
              refine ⟨earlier.length, rfl, ?_⟩
              rw [setup.recoveryAddressWord_extend, List.getElem?_append_right
                (by rw [source_address_length]), source_address_length, Nat.sub_self]
              rfl
        obtain ⟨slot, actualDepth, actualAddress⟩ := endpoint actualTrace actualState rfl
        obtain ⟨tail, addresses⟩ := actualAddresses
        have selectedAddress :
            (setup.recoveryAddressWord
              (setup.proposalRecoveryEraseTrace cut.completed.trace))[slot]? =
                some actualState.publicAddress := by
          rw [← addresses, List.getElem?_append_left
            (by rw [source_address_length, actualDepth]; omega)]
          exact actualAddress
        obtain ⟨selectedState, selectedNext, selectedTrace, selectedJoint, selectedLegal,
            selectedMoved, selectedRetained, selectedDepth, selectedAddress', _nextAddress,
            _selectedInstruction⟩ :=
          source_address_row setup cut.completed.trace slot (by omega)
        have addressEq := Option.some.inj (selectedAddress'.symm.trans selectedAddress)
        cases selectedState with
        | none =>
            have impossible := congrArg Prod.fst addressEq
            cases impossible
        | some chosen =>
            have controlEq := congrArg
              (fun address : Option Nat × (Finset Player × Nat × Nat) =>
                address.2.2.1 * (instructionCount setup.program + 1) +
                  address.1.getD 0 + 1) addressEq
            change setup.commitRecoveryControl (some chosen) =
              setup.commitRecoveryControl (some actualState) at controlEq
            have selectedBefore : TracePrefix
                (setup.proposalRecoveryEraseTrace selectedTrace)
                (setup.proposalRecoveryEraseTrace cut.completed.trace) :=
              setup.proposalRecoveryEraseTrace_prefix
                ((TracePrefix.extend .refl selectedJoint selectedLegal selectedMoved).trans
                  selectedRetained)
            have canonicalEq := setup.commitRecovery_ancestor_eq_of_control_eq
              selectedBefore.reachesWithin canonicalRetained.reachesWithin
              (controlEq.trans sameControl)
            have depths := congrArg
              (fun history : setup.commitRecoveryProtocol.History => history.trace.length)
                canonicalEq
            rw [setup.proposalRecoveryEraseTrace_length, selectedDepth] at depths
            refine ⟨actualDepth.trans depths, ?_⟩
            have masks := congrArg
              (fun history : setup.commitRecoveryProtocol.History =>
                (setup.commitRecoveryPublic history.state).1) canonicalEq
            have addressed := congrArg (fun address => address.2.1) addressEq
            change chosen.excluded = canonicalState.excluded at masks
            change chosen.excluded = actualState.excluded at addressed
            exact addressed.symm.trans masks
      have cleanCloseDepth
          (actualState : CommitRecoveryState setup.program)
          (actualTrace : setup.commitRecoveryProtocol.Trace (some actualState))
          (actualFinal : setup.commitRecoveryProtocol.History)
          (fuel : Nat)
          (actualPath : setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨some actualState, actualTrace⟩ actualFinal)
          (actualCommitting : ProtocolState.atCommit setup.program actualState.point = true)
          (low high : Nat)
          (actualLow : instructionCount setup.program -
            ProtocolState.remaining setup.program actualState.point = low)
          (actualHigh : instructionCount setup.program -
            ProtocolState.commitEnd setup.program actualState.saved = high)
          (nonempty : low < high)
          (exited : actualFinal.state.map (fun state => state.publicAddress.2.2) ≠
            some actualState.publicAddress.2.2) :
          actualTrace.length + (high - low) ≤ actualFinal.trace.length := by
        obtain ⟨lastBefore, lastAfter, lastTrace, lastJoint, lastLegal, lastMoved,
            _startRetained, lastRetained, _saved, _generation, lastDepth, _lastRank⟩ :=
          source_commit_rank_before_exit setup (high - low - 1) actualState actualTrace
            actualCommitting (high - 1) (by rw [actualLow]; omega)
            (by rw [actualHigh]; omega) actualFinal fuel actualPath (Or.inl exited)
        have bounded := lastRetained.length_le
        simp only [Trace.length, lastDepth] at bounded
        omega
      have cleanMaskFromAddresses
          (actualStartState actualEndState : setup.commitRecoveryProtocol.State)
          (actualStart : setup.commitRecoveryProtocol.Trace actualStartState)
          (actualEnd : setup.commitRecoveryProtocol.Trace actualEndState)
          (actualRetained : TracePrefix actualStart actualEnd)
          (canonicalState : CommitRecoveryState setup.program)
          (canonicalTrace : setup.commitRecoveryProtocol.Trace (some canonicalState))
          (canonicalAddresses : (setup.recoveryAddressWord canonicalTrace).IsPrefix
            (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace)))
          (actualAddresses : (setup.recoveryAddressWord actualEnd).IsPrefix
            (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace)))
          (positive : 0 < canonicalTrace.length)
          (lower : actualStart.length ≤ canonicalTrace.length)
          (upper : canonicalTrace.length ≤ actualEnd.length)
          (excluded : Finset Player)
          (constant : ∀ {state : setup.commitRecoveryProtocol.State}
            (middle : setup.commitRecoveryProtocol.Trace state),
            TracePrefix actualStart middle → TracePrefix middle actualEnd →
              (setup.commitRecoveryPublic state).1 = excluded) :
          canonicalState.excluded = excluded := by
        have endpoint : ∀ {state : setup.commitRecoveryProtocol.State}
            (path : setup.commitRecoveryProtocol.Trace state), 0 < path.length →
            (setup.recoveryAddressWord path)[path.length - 1]? =
              some (state.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress) := by
          intro state path
          cases path with
          | start => intro impossible; simp only [Trace.length] at impossible; omega
          | extend earlier actions offered realized =>
              intro _
              simp only [Trace.length, Nat.add_sub_cancel, setup.recoveryAddressWord_extend]
              rw [List.getElem?_append_right
                (by rw [source_address_length setup earlier]),
                source_address_length setup earlier, Nat.sub_self]
              rfl
        have indexed : ∀ {state : setup.commitRecoveryProtocol.State}
            (path : setup.commitRecoveryProtocol.Trace state), 0 < path.length →
            (setup.recoveryAddressWord path).IsPrefix
              (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace)) →
            (setup.recoveryAddressWord
              (setup.proposalRecoveryEraseTrace cut.completed.trace))[path.length - 1]? =
                some (state.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress) := by
          intro state path positive retainedAddresses
          obtain ⟨tail, addresses⟩ := retainedAddresses
          rw [← addresses, List.getElem?_append_left
            (by rw [source_address_length]; omega)]
          exact endpoint path positive
        let labeled := setup.proposalRecoveryLiftTrace (fun _ _ => false) actualEnd
        obtain ⟨middleState, middleLabeled, middleRetained, middleDepth⟩ :=
          setup.proposalRecovery_prefix_at_depth labeled canonicalTrace.length
            (by simpa only [labeled, setup.proposalRecoveryLiftTrace_length] using upper)
        let middle := setup.proposalRecoveryEraseTrace middleLabeled
        have kept : TracePrefix middle actualEnd := by
          simpa only [middle, labeled, setup.proposalRecoveryEraseTrace_lift] using
            setup.proposalRecoveryEraseTrace_prefix middleRetained
        have middleLength : middle.length = canonicalTrace.length := by
          simpa only [middle, setup.proposalRecoveryEraseTrace_length] using middleDepth
        have beforeMiddle : TracePrefix actualStart middle :=
          (actualRetained.reachesWithin.ancestor_comparable kept.reachesWithin
            (by rw [middleLength]; exact lower)).tracePrefix
        have fixed := constant middle beforeMiddle kept
        have canonicalRead := indexed canonicalTrace positive canonicalAddresses
        have middleRead := indexed middle (by rw [middleLength]; exact positive)
          ((source_address_prefix setup kept).trans actualAddresses)
        rw [middleLength] at middleRead
        have masks := congrArg (fun address => address.2.1)
          (Option.some.inj (canonicalRead.symm.trans middleRead))
        have maskEq : (middleState.elim (none, (∅, 0, 0))
            CommitRecoveryState.publicAddress).2.1 =
              (setup.commitRecoveryPublic middleState).1 := by
          cases middleState <;> rfl
        change canonicalState.excluded = _ at masks
        rw [maskEq] at masks
        exact masks.trans fixed
      have cleanDecodedMasks
          {actualState canonicalState nextState : PhaseRuntimeState
            (serviceGraph setup .concurrent)}
          (actual : RecoverySourceCheckpoint setup .concurrent actualState)
          (canonical : RecoverySourceCheckpoint setup .concurrent canonicalState)
          (next : RecoverySourceCheckpoint setup .concurrent nextState)
          (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
          (actualEnd : setup.commitRecoveryProtocol.History)
          (fuel : Nat)
          (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, actual.trace⟩ actualEnd)
          (committing : ProtocolState.atCommit setup.program
            (actual.residual.lift (ProtocolState.entry actual.residual.tail actual.source)) = true)
          (low high : Nat)
          (atLow : instructionCount setup.program - ProtocolState.remaining setup.program
            (actual.residual.lift (ProtocolState.entry actual.residual.tail actual.source)) = low)
          (atHigh : instructionCount setup.program - ProtocolState.commitEnd setup.program
            (actual.residual.lift (ProtocolState.entry actual.residual.tail actual.source)) = high)
          (nonempty : low < high)
          (namespaceEq : canonicalState.attempt = actualState.attempt)
          (exited : actualEnd.state.map (fun state => state.publicAddress.2.2) ≠
            some (actualState.generation, actualState.attempt.phase))
          (canonicalRetained : TracePrefix canonical.trace
            (setup.proposalRecoveryEraseTrace cut.completed.trace))
          (nextRetained : TracePrefix next.trace
            (setup.proposalRecoveryEraseTrace cut.completed.trace))
          (actualAddresses : (setup.recoveryAddressWord actualEnd.trace).IsPrefix
            (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace)))
          (actualBeforeEnd : actual.trace.length < cut.completed.trace.length)
          (instructions : setup.recoveryJointRecall next.trace =
            (canonical.commitInstructionWord image).reverse ++
              setup.recoveryJointRecall canonical.trace)
          (constant : ∀ {state : setup.commitRecoveryProtocol.State}
            (middle : setup.commitRecoveryProtocol.Trace state),
            TracePrefix actual.trace middle → TracePrefix middle actualEnd.trace →
              (setup.commitRecoveryPublic state).1 = actualState.entry.excluded) :
          canonicalState.entry.excluded = actualState.entry.excluded ∧
            nextState.entry.excluded = canonicalState.entry.excluded := by
        let actualPoint := actual.residual.lift
          (ProtocolState.entry actual.residual.tail actual.source)
        let canonicalPoint := canonical.residual.lift
          (ProtocolState.entry canonical.residual.tail canonical.source)
        let actualSource := CommitRecoveryState.atPoint actualPoint
          actualState.entry.excluded actualState.generation
        let canonicalSource := CommitRecoveryState.atPoint canonicalPoint
          canonicalState.entry.excluded canonicalState.generation
        have phaseEq := congrArg CommitAttemptId.phase namespaceEq
        have generationEq := congrArg CommitAttemptId.generation namespaceEq
        change canonicalState.generation = actualState.generation at generationEq
        have controlEq : setup.commitRecoveryControl (some actualSource) =
            setup.commitRecoveryControl (some canonicalSource) := by
          simp only [Setup.commitRecoveryControl, Option.elim, actualSource, canonicalSource,
            CommitRecoveryState.control, CommitRecoveryState.atPoint, actualPoint, canonicalPoint,
            actual.saved_position, canonical.saved_position, generationEq, phaseEq]
        have actualStartAddresses := (source_address_prefix setup path.tracePrefix).trans
          actualAddresses
        obtain ⟨startDepth, _startMasks⟩ :=
          cleanStartDepth actualSource canonicalSource actual.trace canonical.trace
            actualStartAddresses canonicalRetained actualBeforeEnd controlEq
        have remainingEq : ProtocolState.remaining setup.program canonicalPoint =
            ProtocolState.remaining setup.program actualPoint := by
          have canonicalBound := ProtocolState.remaining_le_instructionCount
            setup.program canonicalPoint
          have actualBound := ProtocolState.remaining_le_instructionCount setup.program actualPoint
          have canonicalRank := canonical.saved_position
          have actualRank := actual.saved_position
          change instructionCount setup.program -
            ProtocolState.remaining setup.program canonicalPoint = canonicalState.attempt.phase
              at canonicalRank
          change instructionCount setup.program -
            ProtocolState.remaining setup.program actualPoint =
              actualState.attempt.phase at actualRank
          omega
        have endpointEq := (ProtocolState.commitControl_eq_of_remaining setup.program
          canonicalPoint actualPoint remainingEq).2
        have window := canonical.commit_instruction_word_window image
        change (canonical.commitInstructionWord image).length +
          ProtocolState.commitEnd setup.program canonicalPoint ≤
            ProtocolState.remaining setup.program canonicalPoint at window
        rw [remainingEq, endpointEq] at window
        have actualBound := ProtocolState.remaining_le_instructionCount setup.program actualPoint
        have endBound := ProtocolState.commitEnd_le_remaining setup.program actualPoint
        have wordBound : (canonical.commitInstructionWord image).length ≤ high - low := by
          change instructionCount setup.program -
            ProtocolState.remaining setup.program actualPoint = low at atLow
          change instructionCount setup.program -
            ProtocolState.commitEnd setup.program actualPoint = high at atHigh
          omega
        have exitDepth := cleanCloseDepth actualSource actual.trace actualEnd fuel path
          committing low high atLow atHigh nonempty (by
            simpa only [actualSource, actualPoint, CommitRecoveryState.atPoint,
              CommitRecoveryState.publicAddress, actual.saved_position] using exited)
        have lengths := congrArg List.length instructions
        simp only [setup.recoveryJointRecall_length, List.length_append, List.length_reverse]
          at lengths
        have positiveTrace : ∀ {state : setup.commitRecoveryProtocol.State}
            (trace : setup.commitRecoveryProtocol.Trace state),
            state ≠ none → 0 < trace.length := by
          intro state trace
          cases trace with
          | start => intro impossible; exact (impossible rfl).elim
          | extend prior joint legal realized => intro _; simp only [Trace.length]; omega
        have positive := positiveTrace actual.trace (by intro impossible; cases impossible)
        have firstMask := cleanMaskFromAddresses _ _ actual.trace actualEnd.trace path.tracePrefix
          canonicalSource canonical.trace (source_address_prefix setup canonicalRetained)
          actualAddresses (by omega) (by omega) (by have := path.tracePrefix.length_le; omega)
          actualState.entry.excluded constant
        have lastMask := cleanMaskFromAddresses _ _ actual.trace actualEnd.trace path.tracePrefix
          _ next.trace (source_address_prefix setup nextRetained) actualAddresses
          (by omega) (by omega) (by omega) actualState.entry.excluded constant
        exact ⟨firstMask, lastMask.trans firstMask.symm⟩
      have historicalExitBeforeEntry
          (entry : (nativeApplication).Control)
          (entryTrace : (nativeProtocol).Trace (some entry))
          (finalTrace : (nativeProtocol).Trace (some reference))
          (entryRetained : TracePrefix entryTrace finalTrace)
          (entryNamespace : entry.execution.application.attempt =
            reference.execution.application.attempt)
          (exitBefore exitAfter : (nativeApplication).Control)
          (exitTrace : (nativeProtocol).Trace (some exitBefore))
          (exitJoint : Player → Option (nativeApplication).Action)
          (exitLegal : (nativeProtocol).Legal (some exitBefore) exitJoint)
          (exitMoved : some exitAfter ∈
            ((nativeProtocol).step (some exitBefore) ⟨exitJoint, exitLegal⟩).support)
          (exitRetained : TracePrefix (exitTrace.extend exitJoint exitLegal exitMoved) finalTrace)
          (historical : exitBefore.execution.application.attempt ≠
            reference.execution.application.attempt) :
          TracePrefix (exitTrace.extend exitJoint exitLegal exitMoved) entryTrace := by
        by_cases earlier :
            (exitTrace.extend exitJoint exitLegal exitMoved).length ≤ entryTrace.length
        · exact (exitRetained.reachesWithin.ancestor_comparable entryRetained.reachesWithin
            earlier).tracePrefix
        · have beforeRetained : TracePrefix exitTrace finalTrace := by
            have rowPrefix : TracePrefix exitTrace
                (exitTrace.extend exitJoint exitLegal exitMoved) :=
              TracePrefix.extend («E» := nativeProtocol) (prefixTrace := exitTrace)
                (prior := exitTrace) (source := some exitBefore) (target := some exitAfter)
                .refl exitJoint exitLegal exitMoved
            exact rowPrefix.trans exitRetained
          have entryBefore : TracePrefix entryTrace exitTrace :=
            (entryRetained.reachesWithin.ancestor_comparable beforeRetained.reachesWithin
              (by
                change entryTrace.length ≤ exitTrace.length
                change ¬ (exitTrace.length + 1 ≤ entryTrace.length) at earlier
                omega)).tracePrefix
          have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
            intro state member
            obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
            exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
          have entryOrdered := (phaseApplication_seedOrder implementation.runtime
            implementation.leaks).history nativeInitial implementation.horizon
              implementation.scheduler initialized
              ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                implementation.scheduler entryTrace)
          have exitOrdered := (phaseApplication_seedOrder implementation.runtime
            implementation.leaks).history nativeInitial implementation.horizon
              implementation.scheduler initialized
              ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                implementation.scheduler exitTrace)
          have lower := phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
            (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
              entry exitBefore entryTrace exitTrace entryBefore entryOrdered
          have upper := phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
            (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
              exitBefore reference exitTrace finalTrace beforeRetained exitOrdered
          rw [entryNamespace] at lower
          have generation := Nat.le_antisymm upper.1 lower.1
          have phase := Nat.le_antisymm upper.2.1 lower.2.1
          apply (historical _).elim
          change exitBefore.execution.application.attempt.generation =
            reference.execution.application.attempt.generation at generation
          change exitBefore.execution.application.attempt.phase =
            reference.execution.application.attempt.phase at phase
          cases firstEq : exitBefore.execution.application.attempt
          cases lastEq : reference.execution.application.attempt
          simp only [firstEq, lastEq] at phase generation
          cases phase
          cases generation
          rfl
      have actualCleanInterval
          (exitBefore exitAfter : (nativeApplication).Control)
          (exitTrace : (nativeProtocol).Trace (some exitBefore))
          (exitJoint : Player → Option (nativeApplication).Action)
          (exitLegal : (nativeProtocol).Legal (some exitBefore) exitJoint)
          (exitMoved : some exitAfter ∈
            ((nativeProtocol).step (some exitBefore) ⟨exitJoint, exitLegal⟩).support)
          (exitRetained : TracePrefix
            (exitTrace.extend exitJoint exitLegal exitMoved) traceNative)
          (rawImage : RecoveryState (serviceGraph setup .concurrent))
          (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
          (installed : exitBefore.execution.application.phases = actualPhase :: remaining)
          (normalized : exitAfter.execution.application =
            ({ exitBefore.execution.application with current := rawImage } :
              PhaseRuntimeState (serviceGraph setup .concurrent)).normalize)
          (effect : PhaseClosingEffect implementation.runtime implementation.leaks
            exitBefore.execution exitAfter.execution rawImage)
          (changed : exitAfter.execution.application.attempt ≠
            exitBefore.execution.application.attempt)
          (acceptedAtExit :
            (actualPhase.drain rawImage).native.accepted (.inr named) = some handle)
          (clean : ¬ (((actualPhase.drain rawImage).excluded \
            exitBefore.execution.application.entry.excluded) ∩ actualPhase.owners).Nonempty) :
          let selected := checkpointSelection setup implementation operational exitTrace
          owner ∉ exitBefore.execution.application.entry.excluded ∧
          ∃ follower : RecoverySourceWitness setup .concurrent implementation.plan
              exitAfter.execution.application,
            ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
              ⟨_, selected.val.checkpoint.trace⟩ ⟨_, follower.checkpoint.trace⟩ ∧
            (setup.recoveryAddressWord follower.checkpoint.trace).IsPrefix
              (setup.recoveryAddressWord
                (setup.proposalRecoveryEraseTrace cut.completed.trace)) ∧
            ∀ {state : setup.commitRecoveryProtocol.State}
              (middle : setup.commitRecoveryProtocol.Trace state),
              TracePrefix selected.val.checkpoint.trace middle →
              TracePrefix middle follower.checkpoint.trace →
              (setup.commitRecoveryPublic state).1 =
                exitBefore.execution.application.entry.excluded := by
        let selected := checkpointSelection setup implementation operational exitTrace
        obtain ⟨rawWitness, _transferred, _sameSource⟩ :=
          RecoverySourceWitness.raw_closing_checkpoint setup .concurrent
            implementation.runtime implementation.leaks implementation.plan
            exitBefore exitAfter selected.val rawImage effect changed
        have present : actualPhase ∈
            ({ exitBefore.execution.application with current := rawImage } :
              PhaseRuntimeState (serviceGraph setup .concurrent)).phases.head? := by
          simp only [installed, List.head?_cons, Option.mem_some_iff]
        have ordered := (rawWitness.receipts.ordered actualPhase present actualCommitment).congr
          (actualPhase.drain_tables rawImage).1
        have entryActive := (ordered named owner payload handle
          ((actualPhase.mem_events named).mp namedInside).1 binding acceptedAtExit).1
        have rawChanged :
            ({ exitBefore.execution.application with current := rawImage } :
              PhaseRuntimeState (serviceGraph setup .concurrent)).normalize.attempt ≠
              exitBefore.execution.application.attempt := by
          rw [← normalized]
          exact changed
        have unchanged := (clean_exit_excluded setup implementation
          ({ exitBefore.execution.application with current := rawImage } :
            PhaseRuntimeState (serviceGraph setup .concurrent))
          rawWitness actualPhase remaining installed clean rawChanged).2
        have exitUnchanged : exitAfter.execution.application.entry.excluded =
            exitBefore.execution.application.entry.excluded := by
          rw [normalized]
          exact unchanged
        have exitPrefix : TracePrefix exitTrace
            (exitTrace.extend exitJoint exitLegal exitMoved) :=
          TracePrefix.extend («E» := nativeProtocol) (prefixTrace := exitTrace)
            (prior := exitTrace) (source := some exitBefore) (target := some exitAfter)
            .refl exitJoint exitLegal exitMoved
        obtain ⟨follower, archived, fuel, path, constant⟩ :=
          source_clean_interval setup implementation operational exitBefore exitAfter
            exitTrace (exitTrace.extend exitJoint exitLegal exitMoved) exitPrefix
            selected.val selected.property exitUnchanged
        obtain ⟨last, equal, finalFollower, _finalArchived, later, onward⟩ :=
          follower.prefix_archived_source setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan
            operational.maximalPhases implementation.horizon implementation.scheduler
            exitAfter (exitTrace.extend exitJoint exitLegal exitMoved) archived
            traceNative exitRetained
        cases Option.some.inj equal
        have addresses := (source_address_prefix setup onward.tracePrefix).trans
          (source_checkpoint_addresses_in_cut setup values implementation reference trace
            who event cut finalFollower)
        exact ⟨entryActive, follower, fuel, path, addresses, constant⟩
      have cleanNativeAction
          (exitBefore exitAfter : (nativeApplication).Control)
          (exitTrace : (nativeProtocol).Trace (some exitBefore))
          (exitJoint : Player → Option (nativeApplication).Action)
          (exitLegal : (nativeProtocol).Legal (some exitBefore) exitJoint)
          (exitMoved : some exitAfter ∈
            ((nativeProtocol).step (some exitBefore) ⟨exitJoint, exitLegal⟩).support)
          (exitRetained : TracePrefix
            (exitTrace.extend exitJoint exitLegal exitMoved) traceNative)
          (beforeEntry : TracePrefix
            (exitTrace.extend exitJoint exitLegal exitMoved) entryNative)
          (rawImage : RecoveryState (serviceGraph setup .concurrent))
          (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
          (installed : exitBefore.execution.application.phases = actualPhase :: remaining)
          (normalized : exitAfter.execution.application =
            ({ exitBefore.execution.application with current := rawImage } :
              PhaseRuntimeState (serviceGraph setup .concurrent)).normalize)
          (effect : PhaseClosingEffect implementation.runtime implementation.leaks
            exitBefore.execution exitAfter.execution rawImage)
          (changed : exitAfter.execution.application.attempt ≠
            exitBefore.execution.application.attempt)
          (finished : actualPhase.Finished (actualPhase.drain rawImage))
          (acceptedAtExit : (actualPhase.drain rawImage).native.accepted (.inr named) = some handle)
          (clean : ¬ (((actualPhase.drain rawImage).excluded \
            exitBefore.execution.application.entry.excluded) ∩ actualPhase.owners).Nonempty) :
          ∃ action : (serviceGraph setup .concurrent).Action named,
            ⟨named, action⟩ ∈ cut.entry.execution.application.entry.native.config.history ∧
            cast (congrArg EventField.Action binding) action =
              reference.execution.application.current.native.bindingResult handle payload := by
        have counted : ((nativeMenu).protocol
            ((setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan))
            implementation.horizon implementation.scheduler).Trace (some exitBefore) := by
          rw [← initialEq]
          exact exitTrace
        obtain ⟨⟨_draw, native⟩, bindings, _receipts, _stored, _history, _coverage⟩ :=
          phaseClosingEffect_checkpoint_facts setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan
            implementation.horizon implementation.scheduler exitBefore exitAfter counted
            rawImage effect changed
        have valid := actualPhase.drain_bindingInvariant rawImage bindings.active
        have reachable := actualPhase.drain_reachable rawImage native.active.reachable
        obtain ⟨action, recorded, actionValue⟩ := valid.completed_binding_action reachable
          named owner payload binding (finished namedInside)
        rw [acceptedAtExit, Option.elim_some] at actionValue
        have cleanRetained : (actualPhase.drain rawImage).native.config.history.IsPrefix
            exitAfter.execution.application.entry.native.config.history := by
          rw [normalized]
          change (actualPhase.drain rawImage).native.config.history.IsPrefix
            (PhaseRuntimeState.settle exitBefore.execution.application.phases
              exitBefore.execution.application.generation exitBefore.execution.application.entry
              rawImage exitBefore.execution.application.retired).entry.native.config.history
          rw [installed, PhaseRuntimeState.settle_clean actualPhase remaining
            exitBefore.execution.application.generation exitBefore.execution.application.entry
            rawImage exitBefore.execution.application.retired finished
            (fun failed => clean failed.2)]
          exact (settle_retains_entry_history setup remaining
            exitBefore.execution.application.generation (actualPhase.drain rawImage)
            (actualPhase.drain rawImage) exitBefore.execution.application.retired
            (List.prefix_refl _)).1
        have later := (saved_history_of_prefix setup implementation cut.entry entryNative
          exitAfter (exitTrace.extend exitJoint exitLegal exitMoved) beforeEntry).1
        have fixed := valid.accepted_fixed (.inr named) handle acceptedAtExit
        have physical := (PhaseRuntimeState.settle_physical
          exitBefore.execution.application.phases exitBefore.execution.application.generation
          exitBefore.execution.application.entry rawImage
          exitBefore.execution.application.retired).2.1
        have afterCatalogue :
            exitAfter.execution.application.current.native.candidates.lookup handle =
              (actualPhase.drain rawImage).native.candidates.lookup handle := by
          rw [normalized]
          exact congrArg (fun catalogue => catalogue.lookup handle)
            (physical.trans (actualPhase.drain_tables rawImage).2.1.symm)
        let stable := phaseApplication_preservesFixedCandidates implementation.runtime
          implementation.leaks
        have invariant : (nativeApplication).Invariant (fun state =>
            state.current.native.candidates.lookup handle =
              (actualPhase.drain rawImage).native.candidates.lookup handle) := by
          constructor
          · intro state actor material known
            exact (stable.submit state actor material handle
              (by rw [known]; exact fixed)).trans known
          · intro state message next known handled
            exact (stable.handle state message next handled handle
              (by rw [known]; exact fixed)).trans known
          · intro state command next known reached
            exact (stable.environment state command next reached handle
              (by rw [known]; exact fixed)).trans known
        have finalCatalogue := invariant.tracePrefix (nativeMenu) nativeInitial
          implementation.horizon implementation.scheduler exitAfter reference
          (exitTrace.extend exitJoint exitLegal exitMoved) traceNative
          exitRetained afterCatalogue
        have finalValue :
            reference.execution.application.current.native.bindingResult handle payload =
              (actualPhase.drain rawImage).native.bindingResult handle payload := by
          simp only [State.bindingResult, finalCatalogue]
        exact ⟨action, (cleanRetained.trans later).subset recorded,
          actionValue.trans finalValue.symm⟩
      have cleanNamedValue
          {state nextState : PhaseRuntimeState (serviceGraph setup .concurrent)}
          (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
          (nextCheckpoint : RecoverySourceCheckpoint setup .concurrent nextState)
          (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
          (committing : ProtocolState.atCommit checkpoint.residual.tail
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
          {fuel : Nat}
          (path : setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, checkpoint.trace⟩ ⟨_, nextCheckpoint.trace⟩)
          (instructions : setup.recoveryJointRecall nextCheckpoint.trace =
            (checkpoint.commitInstructionWord image).reverse ++
              setup.recoveryJointRecall checkpoint.trace)
          (unchanged : nextState.entry.excluded = state.entry.excluded)
          (onward : TracePrefix nextCheckpoint.trace cut.witness.checkpoint.trace)
          (action : (serviceGraph setup .concurrent).Action named)
          (recorded : ⟨named, action⟩ ∈
            cut.entry.execution.application.entry.native.config.history)
          (meaning : cast (congrArg EventField.Action binding) action =
            reference.execution.application.current.native.bindingResult handle payload) :
          match commitPhase checkpoint.residual.tail with
          | ⟨_, _, suffix, block, reconstruct, _⟩ =>
            let embedding := cast (congrArg (fun program => OutputEmbedding
              (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
                checkpoint.embedding
            let decoded := decodeCommitAttempt setup.program .concurrent block suffix
              embedding image checkpoint.source state.entry.excluded
            ∀ (name : VarId)
              (terminalCell : HasVar setup.program.terminalCtx name (.commitment owner payload)),
              ((terminalRefs setup.program).get terminalCell).field = .inr named →
              ∀ value : PublicationResult (L.Val payload),
                SourceProgram.State.cell? decoded.1.state name (.commitment owner payload) =
                  some value →
                value = reference.execution.application.current.native.bindingResult
                  handle payload := by
        have decoded := source_clean_decoded_point setup checkpoint nextCheckpoint image
          committing path instructions unchanged
        generalize decomposition : commitPhase checkpoint.residual.tail = segment at decoded ⊢
        rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
        dsimp only at decoded ⊢
        intro name terminalCell field value cell
        have readback := (decoded.2 name (.commitment owner payload)).trans cell
        exact (source_saved_binding_readback setup implementation cut.entry entryNative
          nextCheckpoint cut.witness.checkpoint onward name owner payload terminalCell
          named binding field value readback action recorded).trans meaning
      have cleanCase
          {state nextState : PhaseRuntimeState (serviceGraph setup .concurrent)}
          (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
          (nextCheckpoint : RecoverySourceCheckpoint setup .concurrent nextState)
          (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
          (committing : ProtocolState.atCommit checkpoint.residual.tail
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
          {fuel : Nat}
          (path : setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, checkpoint.trace⟩ ⟨_, nextCheckpoint.trace⟩)
          (instructions : setup.recoveryJointRecall nextCheckpoint.trace =
            (checkpoint.commitInstructionWord image).reverse ++
              setup.recoveryJointRecall checkpoint.trace)
          (closedKept : TracePrefix nextCheckpoint.trace
            (setup.proposalRecoveryEraseTrace cut.completed.trace))
          (lower : checkpoint.trace.length ≤ sourcePrior.length)
          (upper : sourcePrior.length < nextCheckpoint.trace.length)
          (onward : TracePrefix nextCheckpoint.trace cut.witness.checkpoint.trace)
          (exitBefore exitAfter : (nativeApplication).Control)
          (exitTrace : (nativeProtocol).Trace (some exitBefore))
          (exitJoint : Player → Option (nativeApplication).Action)
          (exitLegal : (nativeProtocol).Legal (some exitBefore) exitJoint)
          (exitMoved : some exitAfter ∈
            ((nativeProtocol).step (some exitBefore) ⟨exitJoint, exitLegal⟩).support)
          (exitRetained : TracePrefix
            (exitTrace.extend exitJoint exitLegal exitMoved) traceNative)
          (beforeEntry : TracePrefix
            (exitTrace.extend exitJoint exitLegal exitMoved) entryNative)
          (rawImage : RecoveryState (serviceGraph setup .concurrent))
          (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
          (installed : exitBefore.execution.application.phases = actualPhase :: remaining)
          (exitAttempt : exitBefore.execution.application.attempt = message.payload.attempt)
          (normalized : exitAfter.execution.application =
            ({ exitBefore.execution.application with current := rawImage } :
              PhaseRuntimeState (serviceGraph setup .concurrent)).normalize)
          (effect : PhaseClosingEffect implementation.runtime implementation.leaks
            exitBefore.execution exitAfter.execution rawImage)
          (changed : exitAfter.execution.application.attempt ≠
            exitBefore.execution.application.attempt)
          (finished : actualPhase.Finished (actualPhase.drain rawImage))
          (acceptedAtExit : (actualPhase.drain rawImage).native.accepted (.inr named) = some handle)
          (clean : ¬ (((actualPhase.drain rawImage).excluded \
            exitBefore.execution.application.entry.excluded) ∩ actualPhase.owners).Nonempty) :
          owner ∉ current.excluded ∧ owner ∉ next.excluded ∧
            phaseRecoveryBindingData setup .concurrent named owner payload binding
              ((joint owner).map (·.semantic)) =
                (reference.execution.application.current.native.bindingResult handle payload,
                  false) := by
        have decoded := source_decoded_binding_row setup checkpoint image
          ⟨_, nextCheckpoint.trace⟩ path instructions cut.completed closedKept
          current next sourcePrior joint legal moved kept lower upper
        have lowEq := checkpoint.saved_position
        rw [← decoded.1] at lowEq
        have phaseEq : state.attempt.phase = exitBefore.execution.application.attempt.phase :=
          lowEq.symm.trans (saved.trans (congrArg CommitAttemptId.phase exitAttempt.symm))
        have generationEq :
            state.attempt.generation = exitBefore.execution.application.attempt.generation :=
          decoded.2.1.symm.trans
            (generation.trans (congrArg CommitAttemptId.generation exitAttempt.symm))
        have namespaceEq : state.attempt = exitBefore.execution.application.attempt := by
          cases firstEq : state.attempt
          cases lastEq : exitBefore.execution.application.attempt
          simp only [firstEq, lastEq] at phaseEq generationEq
          cases phaseEq
          cases generationEq
          rfl
        let selected := checkpointSelection setup implementation operational exitTrace
        obtain ⟨entryActive, follower, actualFuel, actualPath, addresses, constant⟩ :=
          actualCleanInterval exitBefore exitAfter exitTrace exitJoint exitLegal exitMoved
            exitRetained rawImage remaining installed normalized effect changed acceptedAtExit clean
        have geometry := source_checkpoint_binding_interval setup implementation selected.val
          operational.maximalPhases actualPhase remaining installed actualCommitment
        let actualEnd : setup.commitRecoveryProtocol.History := ⟨_, follower.checkpoint.trace⟩
        have exited : actualEnd.state.map (fun state => state.publicAddress.2.2) ≠
            some (exitBefore.execution.application.generation,
              exitBefore.execution.application.attempt.phase) := by
          simp only [actualEnd, Option.map_some, CommitRecoveryState.atPoint,
            CommitRecoveryState.publicAddress, follower.checkpoint.saved_position]
          intro equal
          have pairEq := Option.some.inj equal
          exact changed (congrArg (fun pair : Nat × Nat =>
            CommitAttemptId.mk pair.2 pair.1) pairEq)
        have strict : selected.val.checkpoint.trace.length < follower.checkpoint.trace.length := by
          by_contra failed
          have sameDepth :
              selected.val.checkpoint.trace.length = follower.checkpoint.trace.length :=
            Nat.le_antisymm actualPath.tracePrefix.length_le (Nat.le_of_not_gt failed)
          have same := actualPath.tracePrefix.eq_of_same_length TracePrefix.refl sameDepth
          have endpoint := congrArg (fun history : setup.commitRecoveryProtocol.History =>
            history.state.map (fun state => state.publicAddress.2.2)) same.symm
          apply exited
          change some (exitAfter.execution.application.generation,
              instructionCount setup.program - ProtocolState.remaining setup.program
                (follower.checkpoint.residual.lift (ProtocolState.entry
                  follower.checkpoint.residual.tail follower.checkpoint.source))) = _ at endpoint
          change some (exitAfter.execution.application.generation,
              instructionCount setup.program - ProtocolState.remaining setup.program
                (follower.checkpoint.residual.lift (ProtocolState.entry
                  follower.checkpoint.residual.tail follower.checkpoint.source))) = _
          have saved := selected.val.checkpoint.saved_position
          exact endpoint.trans (congrArg (fun rank =>
            some (exitBefore.execution.application.generation, rank)) saved)
        have finalBound := addresses.length_le
        rw [source_address_length, source_address_length,
          setup.proposalRecoveryEraseTrace_length] at finalBound
        have masks := cleanDecodedMasks selected.val.checkpoint checkpoint nextCheckpoint image
          actualEnd actualFuel actualPath geometry.1 actualPhase.low actualPhase.high
          geometry.2.1 geometry.2.2 actualPhase.nonempty namespaceEq exited
          (path.tracePrefix.trans closedKept) closedKept addresses
          (strict.trans_le finalBound) instructions constant
        have grows : ∀ {first last : setup.commitRecoveryProtocol.State}
            (left : setup.commitRecoveryProtocol.Trace first)
            (right : setup.commitRecoveryProtocol.Trace last), TracePrefix left right →
              (setup.commitRecoveryPublic first).1 ⊆ (setup.commitRecoveryPublic last).1 := by
          intro first last left right retained
          induction retained with
          | refl => exact Finset.Subset.refl _
          | extend previous actions available supported ih =>
              exact ih.trans (setup.commitRecovery_step_excluded_subset actions available supported)
        have semanticRow := setup.proposalRecoveryEraseTrace_prefix kept
        have semanticBefore := setup.proposalRecoveryEraseTrace_prefix
          ((TracePrefix.extend .refl joint legal moved).trans kept)
        have beforeClosed : TracePrefix (setup.proposalRecoveryEraseTrace sourcePrior)
            nextCheckpoint.trace :=
          (semanticBefore.reachesWithin.ancestor_comparable closedKept.reachesWithin
            (by simpa only [setup.proposalRecoveryEraseTrace_length] using upper.le)).tracePrefix
        have afterClosed : TracePrefix
            (setup.proposalRecoveryEraseTrace (sourcePrior.extend joint legal moved))
            nextCheckpoint.trace :=
          (semanticRow.reachesWithin.ancestor_comparable closedKept.reachesWithin
            (by simp only [setup.proposalRecoveryEraseTrace_length, Trace.length]
                omega)).tracePrefix
        have beforeSubset := grows _ _ beforeClosed
        have afterSubset := grows _ _ afterClosed
        change current.excluded ⊆ nextState.entry.excluded at beforeSubset
        change next.excluded ⊆ nextState.entry.excluded at afterSubset
        have currentActive : owner ∉ current.excluded := by
          intro excluded
          apply entryActive
          rw [← masks.1, ← masks.2]
          exact beforeSubset excluded
        have nextActive : owner ∉ next.excluded := by
          intro excluded
          apply entryActive
          rw [← masks.1, ← masks.2]
          exact afterSubset excluded
        obtain ⟨action, recorded, meaning⟩ := cleanNativeAction exitBefore exitAfter exitTrace
          exitJoint exitLegal exitMoved exitRetained beforeEntry rawImage remaining installed
          normalized effect changed finished acceptedAtExit clean
        have read := cleanNamedValue checkpoint nextCheckpoint image committing path instructions
          masks.2 onward action recorded meaning
        have rows := decoded.2.2
        generalize decomposition : commitPhase checkpoint.residual.tail = segment at rows read
        rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
        dsimp only at rows read
        obtain ⟨sourceEvent, sourceOwner, sourcePayload, sourceBinding, sourceRank, row⟩ := rows
        have eventEq : sourceEvent = named := Fin.ext (sourceRank.trans position)
        subst sourceEvent
        have typed := EventField.binding.inj (sourceBinding.symm.trans binding)
        cases typed.1
        cases typed.2
        obtain ⟨Ξ, Q, name, fresh, guard, earlier, rest, _slot, _split, _selected,
          ⟨terminalCell, field⟩, literal, cell⟩ := row.2 currentActive
        have value := read name terminalCell field _ cell
        obtain ⟨atCommit, acting, _decode⟩ := source_binding_at_rank setup.program current.point
          named owner payload binding position.symm
        have nonmissing :
            CommitRecoveryMove.missed (SourceProgram.Setup.proposalRecoveryJoint joint owner) =
              false := by
          cases missed : CommitRecoveryMove.missed
              (SourceProgram.Setup.proposalRecoveryJoint joint owner) with
          | false => rfl
          | true =>
              exact (nextActive (CommitRecoveryState.missed_excludes owner current
                (SourceProgram.Setup.proposalRecoveryJoint joint) atCommit acting missed
                next nextSupport)).elim
        have flag :
            (phaseRecoveryBindingData setup .concurrent named owner payload binding
              ((joint owner).map (·.semantic))).2 = false := by
          change ((joint owner).map (·.semantic)).elim false (·.missing) = false at nonmissing
          simp only [phaseRecoveryBindingData, nonmissing, Bool.false_eq_true, ↓reduceIte]
        exact ⟨currentActive, nextActive, Prod.ext ((congrArg Prod.fst literal).trans value) flag⟩
      obtain ⟨finished, last, lastTrace, attempt, completed, _point, excluded,
        _lastGeneration, _live, agreement, instructions, _labels⟩ := cut.blockResult
      change cut.completed = ⟨some last, lastTrace⟩ at completed
      have word := phaseProposalBindingWord_of_ordinary_attempt setup.program cut.block
        cut.suffix cut.cursor.embedding cut.cursor.refs cut.key.2.1 cut.cursor.source
        cut.cursor.source cut.cursor.current.excluded finished last.excluded attempt
        excluded agreement
      have wordFinal : setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace cut.completed.trace) = attempt.joints.reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace cut.cursor.trace) := by
        rw [completed]
        exact instructions
      have positive : 0 < cut.block.length := by
        have size := cut.size
        have inside := (cut.phase.mem_events event).mp cut.inside
        omega
      have startRank : instructionCount setup.program -
          ProtocolState.remaining setup.program cut.cursor.current.point = cut.phase.low := by
        rw [cut.cursor.point, cut.cursor.origin.remaining_lift, ProtocolState.remaining_entry]
        have count := cut.cursor.compiled.countEq
        simp only [eventCount_eq_instructionCount] at count
        have offset := cut.offset
        omega
      have startEnd : instructionCount setup.program -
          ProtocolState.commitEnd setup.program cut.cursor.current.saved = cut.phase.high := by
        rw [cut.cursor.savedEnd positive]
        have count := cut.cursor.compiled.countEq
        simp only [eventCount_eq_instructionCount, cut.block.instructionCount_prepend] at count
        have offset := cut.offset
        have size := cut.size
        omega
      have committing : ProtocolState.atCommit setup.program
          cut.cursor.current.point = true := by
        rw [cut.cursor.point, cut.cursor.origin.atCommit_lift]
        have nonempty : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
            (block : SourceProgram.CommitPrefix Γ O Δ P)
            (suffix : SourceProgram Player L Δ P) (entry : SourceProgram.Config Player L Γ),
            0 < block.length → ProtocolState.atCommit (block.prepend suffix)
              (ProtocolState.entry (block.prepend suffix) entry) = true := by
          intro Γ Δ O P block
          cases block with
          | nil => intro suffix entry impossible; cases Nat.not_lt_zero _ impossible
          | commit => intro suffix entry _; rfl
        exact nonempty cut.block cut.suffix cut.cursor.source positive
      have startState := congrArg History.state cut.cursorHistory
      have startGeneration : cut.cursor.current.generation =
          reference.execution.application.generation := by
        have same := congrArg (fun state => state.map (·.generation)) startState
        have atEntry : cut.cursor.current.generation =
            cut.entry.execution.application.generation :=
          by simpa only [Option.map_some, Option.some.injEq,
            CommitRecoveryState.atPoint] using same
        exact atEntry.trans (congrArg CommitAttemptId.generation cut.sameAttempt)
      have currentCase
          (sameAttempt : message.payload.attempt = reference.execution.application.attempt)
          (acceptedNow : reference.execution.application.current.native.accepted (.inr named) =
            some handle) :
          owner ∉ current.excluded ∧ owner ∉ next.excluded ∧
            phaseRecoveryBindingData setup .concurrent named owner payload binding
              ((joint owner).map (·.semantic)) =
                (reference.execution.application.current.native.bindingResult handle payload,
                  false) := by
        have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
          intro state member
          obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
          exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
        have metadata := phase_attempt_metadata_of_prefix implementation.runtime
          implementation.leaks (nativeMenu) nativeInitial initialized implementation.horizon
          implementation.scheduler inclusionBefore reference inclusionTrace traceNative
          inclusionPrefix inclusionOrdered (inclusionNamespace.symm.trans sameAttempt)
        have phaseEq : actualPhase = cut.phase := by
          have heads := congrArg (fun pair => pair.1.head?) metadata
          simpa only [actualInstalled, List.head?_cons, cut.installed,
            Option.some.injEq] using heads
        have inside : named ∈ cut.phase.events := phaseEq ▸ namedInside
        let actual := (checkpointSelection setup implementation operational traceNative).val
        have bounds := (cut.phase.mem_events named).mp inside
        have receipt := actual.receipts.ordered cut.phase
          (by rw [cut.installed]; exact Option.mem_some_iff.mpr rfl) cut.commitment
        have entryActive := (receipt named owner payload handle bounds.1 binding acceptedNow).1
        have sourceActive : owner ∉ cut.current.excluded := by
          have masks := congrArg Prod.fst cut.native_readback.1
          change cut.current.excluded = reference.execution.application.entry.excluded at masks
          exact fun member => entryActive (masks ▸ member)
        have beforeMask := setup.commitRecovery_public_excluded_of_reaches
          (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
        change cut.cursor.current.excluded ⊆ cut.current.excluded at beforeMask
        have active : owner ∉ cut.cursor.current.excluded := fun member =>
          sourceActive (beforeMask member)
        let slot := named.val - cut.phase.low
        have slotBound : slot < attempt.joints.length := by
          rw [attempt.joints_length]; dsimp only [slot]; have size := cut.size; omega
        obtain ⟨rowCurrent, rowNext, rowPrior, rowJoint, rowLegal, rowMoved, rowKept,
          _rowDepth, rowWord, _rowSaved, rowGeneration, rowPosition⟩ :=
          source_commit_chunk_at_rank setup cut.cursor.current cut.cursor.trace committing
            cut.completed (cut.past.trans cut.future) attempt.joints wordFinal slot slotBound
            named.val (by rw [startRank]; dsimp only [slot]; omega)
            (by rw [startEnd]; exact bounds.2)
        have rowBefore := (TracePrefix.extend («E» := setup.proposalRecoveryProtocol)
          (prefixTrace := rowPrior) (prior := rowPrior)
            .refl rowJoint rowLegal rowMoved).trans rowKept
        have currentBefore := (TracePrefix.extend («E» := setup.proposalRecoveryProtocol)
          (prefixTrace := sourcePrior) (prior := sourcePrior) .refl joint legal moved).trans kept
        have sameControl : setup.commitRecoveryControl (some rowCurrent) =
            setup.commitRecoveryControl (some current) := by
          simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control]
          rw [rowGeneration, startGeneration, generation,
            congrArg CommitAttemptId.generation sameAttempt, rowPosition, position]
          rfl
        have erasedEqual := setup.commitRecovery_ancestor_eq_of_control_eq
          (setup.proposalRecoveryEraseTrace_prefix rowBefore).reachesWithin
          (setup.proposalRecoveryEraseTrace_prefix currentBefore).reachesWithin sameControl
        have sameDepth := congrArg (fun history : setup.commitRecoveryProtocol.History =>
          history.trace.length) erasedEqual
        simp only [setup.proposalRecoveryEraseTrace_length] at sameDepth
        have sameAfter := rowKept.eq_of_same_length kept
          (by simpa only [Trace.length] using congrArg Nat.succ sameDepth)
        have sameWord := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)) sameAfter
        have jointEq : Setup.proposalRecoveryJoint joint = attempt.joints[slot] :=
          (List.cons.inj sameWord).1.symm.trans rowWord
        have activeAt : ∀ {state : CommitRecoveryState setup.program}
            (path : setup.proposalRecoveryProtocol.Trace (some state)),
            TracePrefix path cut.completed.trace → owner ∉ state.excluded := by
          intro state path retained
          have grows := setup.commitRecovery_public_excluded_of_reaches
            (setup.proposalRecoveryEraseTrace_prefix retained).reachesWithin
          rw [completed] at grows
          change state.excluded ⊆ last.excluded at grows
          exact fun member => active (excluded ▸ grows member)
        have currentActive := activeAt sourcePrior currentBefore
        have nextActive := activeAt (sourcePrior.extend joint legal moved) kept
        let selected : Fin (eventCount (cut.block.prepend cut.suffix)) := ⟨slot, by
          have count := cut.block.eventCount_prepend cut.suffix
          rw [attempt.joints_length] at slotBound
          omega⟩
        have selectedEvent : cut.cursor.embedding.event selected = named := by
          apply Fin.ext
          rw [cut.cursor.compiled.rankEq, cut.offset]
          dsimp only [selected, slot]
          omega
        let field : FieldRef (graphLayout setup.program) (.binding owner payload) :=
          ⟨.inr named, binding⟩
        have stored := actual.binding.active.binding_read field named rfl
          (actual.receipts.exclusion.active named handle acceptedNow)
        rw [acceptedNow, Option.elim_some] at stored
        have locked := field.get?_preserved _ _ cut.lockedStore _ stored
        have read := fillCommitPrefix_wordAction setup.program cut.block cut.suffix
          cut.cursor.embedding cut.cursor.views.actionEq cut.key.2.1 cut.cursor.source
          owner selected (by simpa only [attempt.joints_length] using slotBound)
          payload (by rw [selectedEvent]; exact binding)
        have selectedWord := congrArg (fun joints :
            List (Player → Option (CommitRecoveryMove Player L)) => joints[slot]?) word
        have wordBound : slot < (phaseProposalBindingWord setup.program cut.block
            cut.suffix cut.cursor.embedding cut.cursor.current.excluded cut.key.2.1
              cut.cursor.source).length := by
          rw [word]
          exact slotBound
        simp only [List.getElem?_eq_getElem wordBound,
          List.getElem?_eq_getElem slotBound] at selectedWord
        have component := congrFun (jointEq.trans (Option.some.inj selectedWord).symm) owner
        simp only [phaseProposalBindingWord, List.getElem_map, List.getElem_range,
          ite_eq_right active] at component
        rw [read] at component
        simp only [selectedEvent] at component
        have decodeAt (first second : (serviceGraph setup .concurrent).EventId)
            (same : first = second)
            (leftShape : (serviceGraph setup .concurrent).outputLayout first =
              .binding owner payload)
            (rightShape : (serviceGraph setup .concurrent).outputLayout second =
              .binding owner payload)
            (value : PublicationResult (L.Val payload)) :
            decodeEventAction setup.program first
                (cast (congrArg EventField.Action leftShape.symm) value) =
              decodeEventAction setup.program second
                (cast (congrArg EventField.Action rightShape.symm) value) := by
          cases same
          rfl
        erw [decodeAt _ _ selectedEvent (by rw [selectedEvent]; exact binding) binding
          ((field.get? cut.key.2.1).getD .failure)] at component
        change ((joint owner).map (·.semantic)) =
          (decodeEventAction setup.program named
            (cast (congrArg EventField.Action binding.symm)
              ((field.get? cut.key.2.1).getD .failure))).map
                (fun action => ⟨action, false⟩) at component
        rw [locked, Option.getD_some] at component
        cases decoded : decodeEventAction setup.program named
            (cast (congrArg EventField.Action binding.symm)
              (reference.execution.application.current.native.bindingResult handle payload)) with
        | none =>
            rw [decoded, Option.map_none] at component
            have absent : joint owner = none := Option.map_eq_none_iff.mp component
            have offered := legal.2 owner
            rw [absent] at offered
            obtain ⟨_, acting, _⟩ := source_binding_at_rank setup.program current.point
              named owner payload binding position.symm
            exact (offered ⟨acting, currentActive⟩).elim
        | some action =>
            have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program named
              _ action decoded
            rw [decoded, Option.map_some] at component
            refine ⟨currentActive, nextActive, ?_⟩
            simp only [component, phaseRecoveryBindingData, Option.elim_some,
              Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoded,
              Option.map_some, Option.getD_some, cast_cast, cast_eq]
      have rowInCurrentBlock
          (startBound : cut.cursor.trace.length ≤ sourcePrior.length) :
          message.payload.attempt = reference.execution.application.attempt ∧
            sourcePrior.length = cut.cursor.trace.length + (named.val - cut.phase.low) ∧
            cut.phase.low ≤ named.val := by
        have sourceBefore := (TracePrefix.extend («E» := setup.proposalRecoveryProtocol)
          (prefixTrace := sourcePrior) (prior := sourcePrior) .refl joint legal moved).trans kept
        let slot := sourcePrior.length - cut.cursor.trace.length
        have totalLength := congrArg List.length wordFinal
        simp only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
          List.length_append, List.length_reverse] at totalLength
        have sourceBound := kept.length_le
        have slotBound : slot < attempt.joints.length := by
          simp only [Trace.length] at sourceBound
          dsimp only [slot]
          omega
        have blockBound : slot < cut.block.length := by
          simpa only [attempt.joints_length] using slotBound
        obtain ⟨rowCurrent, rowNext, rowPrior, rowJoint, rowLegal, rowMoved, rowKept,
          rowDepth, _rowWord, rowSaved, rowGeneration, rowPosition⟩ :=
          source_commit_chunk_at_rank setup cut.cursor.current cut.cursor.trace committing
            cut.completed (cut.past.trans cut.future) attempt.joints wordFinal slot slotBound
            (cut.phase.low + slot) (by rw [startRank])
            (by rw [startEnd]; have size := cut.size; omega)
        have rowBefore := (TracePrefix.extend («E» := setup.proposalRecoveryProtocol)
          (prefixTrace := rowPrior) (prior := rowPrior)
            .refl rowJoint rowLegal rowMoved).trans rowKept
        have sameBefore := rowBefore.eq_of_same_length sourceBefore
          (by rw [rowDepth]; dsimp only [slot]; omega)
        have sameState : rowCurrent = current :=
          Option.some.inj (congrArg History.state sameBefore)
        subst rowCurrent
        have savedStart : instructionCount setup.program -
            ProtocolState.remaining setup.program cut.cursor.current.saved =
              reference.execution.application.attempt.phase := by
          have same := congrArg (fun state => state.map fun source =>
            instructionCount setup.program - ProtocolState.remaining setup.program source.saved)
              startState
          have atEntry : instructionCount setup.program -
              ProtocolState.remaining setup.program cut.cursor.current.saved =
                cut.entry.execution.application.attempt.phase := by
            simpa only [Option.map_some, Option.some.injEq, CommitRecoveryState.atPoint,
              cut.witness.checkpoint.saved_position] using same
          exact atEntry.trans (congrArg CommitAttemptId.phase cut.sameAttempt)
        have namespaceEq : message.payload.attempt = reference.execution.application.attempt := by
          have phaseEq : message.payload.attempt.phase =
              reference.execution.application.attempt.phase := by
            rw [← saved, rowSaved, savedStart]
          have generationEq : message.payload.attempt.generation =
              reference.execution.application.attempt.generation :=
            generation.symm.trans (rowGeneration.trans startGeneration)
          cases firstEq : message.payload.attempt
          cases lastEq : reference.execution.application.attempt
          simp only [firstEq, lastEq] at phaseEq generationEq
          cases phaseEq
          cases generationEq
          rfl
        refine ⟨namespaceEq, ?_⟩
        rw [position] at rowPosition
        dsimp only [slot] at rowPosition
        constructor <;> omega
      have rowLocation :
          TracePrefix (sourcePrior.extend joint legal moved) cut.trace ∨
            (TracePrefix cut.trace sourcePrior ∧
              message.payload.attempt = reference.execution.application.attempt ∧ owner ≠ who) := by
        by_cases earlier : (sourcePrior.extend joint legal moved).length ≤ cut.trace.length
        · obtain ⟨state, prefixTrace, retained, length⟩ :=
            setup.proposalRecovery_prefix_at_depth cut.trace
              (sourcePrior.extend joint legal moved).length earlier
          have same := kept.eq_of_same_length (retained.trans cut.future) length.symm
          cases same
          exact Or.inl retained
        have lower : cut.trace.length ≤ sourcePrior.length := by
          simp only [Trace.length] at earlier
          omega
        obtain ⟨state, prefixTrace, retained, length⟩ :=
          setup.proposalRecovery_prefix_at_depth sourcePrior cut.trace.length lower
        have sourceBefore := (TracePrefix.extend («E» := setup.proposalRecoveryProtocol)
          (prefixTrace := sourcePrior) (prior := sourcePrior) .refl joint legal moved).trans kept
        have same := cut.future.eq_of_same_length (retained.trans sourceBefore) length.symm
        have cutKept : TracePrefix cut.trace sourcePrior := by cases same; exact retained
        obtain ⟨namespaceEq, rowDepth, rowLow⟩ := rowInCurrentBlock
          (cut.past.length_le.trans lower)
        refine Or.inr ⟨cutKept, namespaceEq, ?_⟩
        intro equalOwner
        have focalRecorded : record ∈ reference.execution.recall who := by
          simpa only [← equalOwner] using recorded
        obtain ⟨actualMessage, sent, _sender, packet⟩ := PhaseCount.recalled_submission_emitted
          implementation.runtime implementation.leaks nativeInitial implementation.horizon
          implementation.scheduler raw who record focalRecorded material transmitted
        have sameMessage : actualMessage = message := Option.some.inj (sent.symm.trans emitted)
        subst actualMessage
        have emittedAttempt := phase_recalled_emission_attempt implementation.runtime
          implementation.leaks nativeInitial implementation.horizon implementation.scheduler
          raw who record focalRecorded message emitted
        have namedBefore := phase_recorded_binding_rank_lt_of_unsent_request
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
          (setup.initialLaw.map encodeInputs) implementation.horizon
          (serviceGraph_revealRelaxedOrdered setup .concurrent) implementation.scheduler trace
          who record focalRecorded material transmitted named handle (packet.symm.trans call)
          (emittedAttempt.symm.trans namespaceEq) event cut.request cut.unsent
        have cutClock := cut.clock
        omega
      have entryLocation :
          TracePrefix (sourcePrior.extend joint legal moved) cut.cursor.trace ∨
            message.payload.attempt = reference.execution.application.attempt := by
        by_cases earlier :
            (sourcePrior.extend joint legal moved).length ≤ cut.cursor.trace.length
        · obtain ⟨state, prefixTrace, retained, length⟩ :=
            setup.proposalRecovery_prefix_at_depth cut.cursor.trace
              (sourcePrior.extend joint legal moved).length earlier
          have same := kept.eq_of_same_length
            (retained.trans (cut.past.trans cut.future)) length.symm
          cases same
          exact Or.inl retained
        · apply Or.inr
          exact (rowInCurrentBlock (by simp only [Trace.length] at earlier; omega)).1
      have matching : owner ∉ current.excluded ∧ owner ∉ next.excluded ∧
          phaseRecoveryBindingData setup .concurrent named owner payload binding
            ((joint owner).map (·.semantic)) =
              (reference.execution.application.current.native.bindingResult handle payload,
                false) := by
        rcases actualImage with ⟨sameAttempt, acceptedNow⟩ |
          ⟨exitBefore, exitAfter, exitTrace, exitJoint, exitLegal, exitMoved, rawImage,
            _inclusionToExit, exitRetained, exitAttempt, changed, phaseBefore, normalized,
            finished, effect, acceptedAtExit⟩
        · exact currentCase sameAttempt acceptedNow
        have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
          intro state member
          obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
          exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
        let exitWitness := (checkpointSelection setup implementation operational exitTrace).val
        have exitOrdered : exitBefore.execution.application.Ordered :=
          exitWitness.receipts.exclusion.frontier.adjacent
        let exitAfterTrace := exitTrace.extend exitJoint exitLegal exitMoved
        have afterOrdered := (phaseApplication_seedOrder implementation.runtime
          implementation.leaks).history nativeInitial implementation.horizon
            implementation.scheduler initialized
            ((nativeMenu).toRawTrace nativeInitial implementation.horizon
              implementation.scheduler exitAfterTrace)
        have oneStep : TracePrefix exitTrace exitAfterTrace :=
          TracePrefix.extend («E» := nativeProtocol) (prefixTrace := exitTrace)
            (prior := exitTrace) (source := some exitBefore) (target := some exitAfter)
            .refl exitJoint exitLegal exitMoved
        have lower := phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
          (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
          exitBefore exitAfter exitTrace exitAfterTrace oneStep exitOrdered
        have upper := phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
          (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
          exitAfter reference exitAfterTrace traceNative exitRetained afterOrdered
        have historical : message.payload.attempt ≠ reference.execution.application.attempt := by
          intro equalAttempt
          have same := exitAttempt.trans equalAttempt
          have sameGeneration := congrArg CommitAttemptId.generation same
          have samePhase := congrArg CommitAttemptId.phase same
          apply changed
          have phaseEq : exitAfter.execution.application.attempt.phase =
              exitBefore.execution.application.attempt.phase := by
            have below := lower.2.1
            have above := upper.2.1
            omega
          have generationEq : exitAfter.execution.application.attempt.generation =
              exitBefore.execution.application.attempt.generation := by
            change exitBefore.execution.application.generation =
              reference.execution.application.generation at sameGeneration
            change exitAfter.execution.application.generation =
              exitBefore.execution.application.generation
            have below := lower.1
            have above := upper.1
            change exitBefore.execution.application.generation ≤
              exitAfter.execution.application.generation at below
            change exitAfter.execution.application.generation ≤
              reference.execution.application.generation at above
            omega
          cases firstEq : exitAfter.execution.application.attempt
          cases lastEq : exitBefore.execution.application.attempt
          simp only [firstEq, lastEq] at phaseEq generationEq
          cases phaseEq
          cases generationEq
          rfl
        have beforeEntry := historicalExitBeforeEntry cut.entry entryNative traceNative
          entryRetainedNative cut.sameAttempt exitBefore exitAfter exitTrace exitJoint
          exitLegal exitMoved exitRetained (by
            intro same; exact historical (exitAttempt.symm.trans same))
        have beforeCursor : sourcePrior.length < cut.cursor.trace.length := by
          by_contra outside
          exact historical (rowInCurrentBlock (Nat.le_of_not_gt outside)).1
        obtain ⟨remaining, installed⟩ := List.head?_eq_some_iff.mp
          (Option.mem_def.mp phaseBefore)
        have canceledSource
            (dirty : (((actualPhase.drain rawImage).excluded \
              exitBefore.execution.application.entry.excluded) ∩ actualPhase.owners).Nonempty) :
            ∃ (follower : RecoverySourceWitness setup .concurrent implementation.plan
                exitAfter.execution.application)
              (state : PhaseRuntimeState (serviceGraph setup .concurrent))
              (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
              (closed : setup.commitRecoveryProtocol.History) (first steps later : Nat),
              follower.checkpoint.ArchivedProposals exitAfter.execution.network.inputs ∧
              setup.commitRecoveryProtocol.ReachesWithin first
                ⟨_, exitWitness.checkpoint.trace⟩ ⟨_, follower.checkpoint.trace⟩ ∧
              state.attempt = exitBefore.execution.application.attempt ∧
              (⟨_, checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
                ⟨_, exitWitness.checkpoint.trace⟩ ∧
              state.entry.excluded = exitBefore.execution.application.entry.excluded ∧
              setup.commitRecoveryProtocol.ReachesWithin steps ⟨_, checkpoint.trace⟩ closed ∧
              setup.commitRecoveryProtocol.ReachesWithin later closed
                ⟨_, follower.checkpoint.trace⟩ ∧
              setup.recoveryJointRecall closed.trace =
                (checkpoint.commitInstructionWord (actualPhase.drain rawImage).native).reverse ++
                  setup.recoveryJointRecall checkpoint.trace ∧
              BindingReceiptOrder state.attempt.phase state.entry.excluded
                (actualPhase.drain rawImage).native.accepted ∧
              (actualPhase.drain rawImage).native.bindingResult handle payload =
                reference.execution.application.current.native.bindingResult handle payload ∧
              (⟨exitBefore.execution.application.attempt,
                (actualPhase.drain rawImage).native⟩ :
                  RetiredCommitAttempt (serviceGraph setup .concurrent)) ∈
                cut.entry.execution.application.retired := by
          let record : RetiredCommitAttempt (serviceGraph setup .concurrent) :=
            ⟨⟨actualPhase.low, exitBefore.execution.application.generation⟩,
              (actualPhase.drain rawImage).native⟩
          have archived : record ∈ exitAfter.execution.application.retired := by
            rw [normalized]
            change record ∈ (PhaseRuntimeState.settle _ _ _ _ _).retired
            rw [installed]
            by_cases survives :
                (actualPhase.owners \
                  (actualPhase.drain rawImage).excluded).Nonempty
            · rw [PhaseRuntimeState.settle_retry actualPhase remaining _ _ _ _
                finished actualCommitment dirty survives]
              exact List.mem_append_right _ (List.mem_singleton_self _)
            · rw [PhaseRuntimeState.settle_exhausted actualPhase remaining _ _ _ _
                finished actualCommitment dirty survives]
              exact (PhaseRuntimeState.settle_archive _ _ _ _ _).subset
                (List.mem_append_right _ (List.mem_singleton_self _))
          have archiveInvariant : (nativeApplication).Invariant
              (fun state => record ∈ state.retired) := by
            constructor
            · intro state actor material kept
              exact kept
            · intro state packet next kept handled
              change state.handle implementation.runtime packet = some next at handled
              unfold PhaseRuntimeState.handle at handled
              split at handled
              · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp handled
                exact (PhaseRuntimeState.settle_archive _ _ _ _ _).subset kept
              · cases handled
            · intro state command next kept supported
              change next ∈ (state.environment implementation.runtime command).support at supported
              unfold PhaseRuntimeState.environment at supported
              split at supported
              · obtain ⟨native, _supported, rfl⟩ :=
                  (PMF.mem_support_map_iff _ _ _).mp supported
                exact (PhaseRuntimeState.settle_archive _ _ _ _ _).subset kept
              · cases (PMF.mem_support_pure_iff _ _).mp supported
                exact kept
          have archivedAtEntry := archiveInvariant.tracePrefix (nativeMenu) nativeInitial
            implementation.horizon implementation.scheduler exitAfter cut.entry exitAfterTrace
            entryNative beforeEntry archived
          obtain ⟨target, targetEq, follower, proposals, first, actualPath⟩ :=
            exitWitness.prefix_archived_source setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan
              operational.maximalPhases implementation.horizon implementation.scheduler
              exitBefore exitTrace
              (checkpointSelection setup implementation operational exitTrace).property
              exitAfterTrace oneStep
          cases Option.some.inj targetEq
          obtain ⟨index, inRange, recordEq⟩ := List.mem_iff_getElem.mp archived
          obtain ⟨state, checkpoint, _recall, _origins, _records, attemptEq, _retained,
              _prefix, _agrees, _nonempty, closed, steps, later, path, instructions, onward⟩ :=
            follower.origins.get index inRange
          have actualAttempt : record.attempt = exitBefore.execution.application.attempt := by
            simp only [record, PhaseRuntimeState.attempt, installed, List.head?_cons,
              Option.map_some, Option.getD_some]
          have sameAttempt := attemptEq.trans
            ((congrArg RetiredCommitAttempt.attempt recordEq).trans actualAttempt)
          have sameControl : setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
              (checkpoint.residual.lift
                (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
                state.entry.excluded state.generation)) =
              setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
                (exitWitness.checkpoint.residual.lift (ProtocolState.entry
                  exitWitness.checkpoint.residual.tail exitWitness.checkpoint.source))
                  exitBefore.execution.application.entry.excluded
                  exitBefore.execution.application.generation)) := by
            have phases := congrArg CommitAttemptId.phase sameAttempt
            have generations := congrArg CommitAttemptId.generation sameAttempt
            change state.generation = exitBefore.execution.application.generation at generations
            simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control,
              CommitRecoveryState.atPoint, checkpoint.saved_position,
              exitWitness.checkpoint.saved_position, phases, generations]
          have sameHistory := setup.commitRecovery_ancestor_eq_of_control_eq
            (path.trans onward) actualPath sameControl
          have masks : state.entry.excluded =
              exitBefore.execution.application.entry.excluded := by
            have same := congrArg (fun history : setup.commitRecoveryProtocol.History =>
              (setup.commitRecoveryPublic history.state).1) sameHistory
            simpa only [Setup.commitRecoveryPublic, Option.elim_some,
              CommitRecoveryState.atPoint] using same
          obtain ⟨rawWitness, _transferred, _sameSource⟩ :=
            RecoverySourceWitness.raw_closing_checkpoint setup .concurrent
              implementation.runtime implementation.leaks implementation.plan
              exitBefore exitAfter exitWitness rawImage effect changed
          have present : actualPhase ∈
              ({ exitBefore.execution.application with current := rawImage } :
                PhaseRuntimeState (serviceGraph setup .concurrent)).phases.head? := by
            simp only [installed, List.head?_cons, Option.mem_some_iff]
          have ordered := (rawWitness.receipts.ordered actualPhase present actualCommitment).congr
            (actualPhase.drain_tables rawImage).1
          obtain ⟨_valid, catalogue⟩ := accepted_snapshot_catalogue setup implementation
            reference traceNative exitAfter exitAfterTrace exitRetained
            (actualPhase.drain rawImage).native (Or.inr (Or.inr ⟨record, archived, rfl⟩))
            owner payload ⟨.inr named, binding⟩ handle acceptedAtExit
          have meaning : (actualPhase.drain rawImage).native.bindingResult handle payload =
              reference.execution.application.current.native.bindingResult handle payload := by
            simp only [State.bindingResult, catalogue]
          have imageEq : exitAfter.execution.application.retired[index].state =
              (actualPhase.drain rawImage).native :=
            congrArg RetiredCommitAttempt.state recordEq
          have actualInstructions := instructions.trans (congrArg (fun image =>
            (checkpoint.commitInstructionWord image).reverse ++
              setup.recoveryJointRecall checkpoint.trace) imageEq)
          refine ⟨follower, state, checkpoint, closed, first, steps, later, proposals,
            actualPath, sameAttempt, sameHistory, masks, path, onward, actualInstructions,
            ?_, meaning, ?_⟩
          · have samePhase := congrArg CommitAttemptId.phase sameAttempt
            rw [samePhase, masks]
            simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons,
              Option.map_some, Option.getD_some] using ordered
          · have sameRecord : record =
                ⟨exitBefore.execution.application.attempt,
                  (actualPhase.drain rawImage).native⟩ := by
              exact congrArg (fun attempt =>
                (⟨attempt, (actualPhase.drain rawImage).native⟩ :
                  RetiredCommitAttempt (serviceGraph setup .concurrent))) actualAttempt
            exact sameRecord ▸ archivedAtEntry
        by_cases dirty : (((actualPhase.drain rawImage).excluded \
            exitBefore.execution.application.entry.excluded) ∩ actualPhase.owners).Nonempty
        · obtain ⟨follower, archivedState, archivedCheckpoint, closed, first, steps, later,
            proposals, actualPath, archivedAttempt, sameHistory, inherited, path, onward,
            instructions, receiptOrder, meaning, archivedAtEntry⟩ := canceledSource dirty
          let start := CommitRecoveryState.atPoint
            (archivedCheckpoint.residual.lift (ProtocolState.entry
              archivedCheckpoint.residual.tail archivedCheckpoint.source))
            archivedState.entry.excluded archivedState.generation
          let actualStart := CommitRecoveryState.atPoint
            (exitWitness.checkpoint.residual.lift (ProtocolState.entry
              exitWitness.checkpoint.residual.tail exitWitness.checkpoint.source))
            exitBefore.execution.application.entry.excluded
            exitBefore.execution.application.generation
          have startEq : start = actualStart :=
            Option.some.inj (congrArg History.state sameHistory)
          have interval := source_checkpoint_binding_interval setup implementation exitWitness
            operational.maximalPhases actualPhase remaining installed actualCommitment
          have starts : ProtocolState.atCommit setup.program start.point = true ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program start.point = actualPhase.low ∧
              instructionCount setup.program -
                ProtocolState.commitEnd setup.program start.saved = actualPhase.high := by
            rw [startEq]
            exact interval
          have bounds := (actualPhase.mem_events named).mp namedInside
          have wordSize := source_commit_instruction_word_length setup archivedCheckpoint
            (actualPhase.drain rawImage).native
          have remainingBound := ProtocolState.remaining_le_instructionCount setup.program
            start.point
          have slotInside : named.val - actualPhase.low <
              (archivedCheckpoint.commitInstructionWord
                (actualPhase.drain rawImage).native).length := by
            change _ = ProtocolState.remaining setup.program start.point -
              ProtocolState.commitEnd setup.program start.saved at wordSize
            omega
          have actualLengths := congrArg List.length instructions
          simp only [setup.recoveryJointRecall_length, List.length_append,
            List.length_reverse] at actualLengths
          obtain ⟨recordIndex, recordBound, recordEq⟩ := List.mem_iff_getElem.mp archivedAtEntry
          obtain ⟨canonicalState, canonicalCheckpoint, _recall, _origins, _archive,
              canonicalAttempt, _retained, _cut, _agrees, _positive, canonicalClosed,
              canonicalSteps, canonicalLater, canonicalPath, canonicalWord, canonicalOnward⟩ :=
            cut.witness.origins.get recordIndex recordBound
          let canonicalStart := CommitRecoveryState.atPoint
            (canonicalCheckpoint.residual.lift (ProtocolState.entry
              canonicalCheckpoint.residual.tail canonicalCheckpoint.source))
            canonicalState.entry.excluded canonicalState.generation
          have canonicalAttempt' : canonicalState.attempt =
              exitBefore.execution.application.attempt :=
            canonicalAttempt.trans (congrArg RetiredCommitAttempt.attempt recordEq)
          have canonicalImage := congrArg RetiredCommitAttempt.state recordEq
          have nativeWord := canonicalWord.trans (congrArg (fun image =>
            (canonicalCheckpoint.commitInstructionWord image).reverse ++
              setup.recoveryJointRecall canonicalCheckpoint.trace) canonicalImage)
          have sameAttempt := archivedAttempt.trans canonicalAttempt'.symm
          have sameControl : setup.commitRecoveryControl (some start) =
              setup.commitRecoveryControl (some canonicalStart) := by
            have phases := congrArg CommitAttemptId.phase sameAttempt
            have generations := congrArg CommitAttemptId.generation sameAttempt
            change archivedState.generation = canonicalState.generation at generations
            simp only [start, canonicalStart, Setup.commitRecoveryControl, Option.elim_some,
              CommitRecoveryState.control, CommitRecoveryState.atPoint,
              archivedCheckpoint.saved_position, canonicalCheckpoint.saved_position,
              phases, generations]
          have entryHistory : (⟨some cut.cursor.current,
              setup.proposalRecoveryEraseTrace cut.cursor.trace⟩ :
                setup.commitRecoveryProtocol.History) =
              ⟨_, cut.witness.checkpoint.trace⟩ := by
            have same := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
              (⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ :
                setup.commitRecoveryProtocol.History)) cut.cursorHistory
            simpa only [setup.proposalRecoveryEraseTrace_lift] using same
          have entryPath := (setup.proposalRecoveryEraseTrace_prefix
            (cut.past.trans cut.future)).reachesWithin
          change setup.commitRecoveryProtocol.ReachesWithin _
            ⟨some cut.cursor.current, setup.proposalRecoveryEraseTrace cut.cursor.trace⟩
            ⟨_, setup.proposalRecoveryEraseTrace cut.completed.trace⟩ at entryPath
          rw [entryHistory] at entryPath
          have canonicalClosedKept := (canonicalOnward.trans entryPath).tracePrefix
          have canonicalStartKept :=
            ((canonicalPath.trans canonicalOnward).trans entryPath).tracePrefix
          obtain ⟨finalState, finalEq, finalWitness, _finalProposals, finalFuel, finalPath⟩ :=
            follower.prefix_archived_source setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan
              operational.maximalPhases implementation.horizon implementation.scheduler
              exitAfter exitAfterTrace proposals traceNative exitRetained
          cases Option.some.inj finalEq
          have finalAddresses := source_checkpoint_addresses_in_cut setup values implementation
            reference trace who event cut finalWitness
          have actualAddresses := (source_address_prefix setup
            ((path.trans onward).trans finalPath).tracePrefix).trans finalAddresses
          have finalBound := finalAddresses.length_le
          rw [source_address_length, source_address_length,
            setup.proposalRecoveryEraseTrace_length] at finalBound
          have actualBound := (onward.trans finalPath).tracePrefix.length_le
          change closed.trace.length ≤ finalWitness.checkpoint.trace.length at actualBound
          have actualBeforeEnd : archivedCheckpoint.trace.length < cut.completed.trace.length := by
            omega
          obtain ⟨startDepth, startMasks⟩ := cleanStartDepth start canonicalStart
            archivedCheckpoint.trace canonicalCheckpoint.trace actualAddresses canonicalStartKept
            actualBeforeEnd sameControl
          have canonicalReceipt : BindingReceiptOrder canonicalState.attempt.phase
              canonicalState.entry.excluded (actualPhase.drain rawImage).native.accepted := by
            change archivedState.entry.excluded = canonicalState.entry.excluded at startMasks
            rw [← congrArg CommitAttemptId.phase sameAttempt, ← startMasks]
            exact receiptOrder
          have remainingEq : ProtocolState.remaining setup.program canonicalStart.point =
              ProtocolState.remaining setup.program start.point := by
            have first := archivedCheckpoint.saved_position
            have second := canonicalCheckpoint.saved_position
            have firstBound := ProtocolState.remaining_le_instructionCount setup.program start.point
            have secondBound := ProtocolState.remaining_le_instructionCount setup.program
              canonicalStart.point
            have phases := congrArg CommitAttemptId.phase sameAttempt
            change instructionCount setup.program -
              ProtocolState.remaining setup.program start.point = archivedState.attempt.phase
                at first
            change instructionCount setup.program -
              ProtocolState.remaining setup.program canonicalStart.point =
                canonicalState.attempt.phase at second
            omega
          have control := ProtocolState.commitControl_eq_of_remaining setup.program
            canonicalStart.point start.point remainingEq
          have canonicalSize := source_commit_instruction_word_length setup canonicalCheckpoint
            (actualPhase.drain rawImage).native
          have canonicalLengths := congrArg List.length nativeWord
          simp only [setup.recoveryJointRecall_length, List.length_append,
            List.length_reverse] at canonicalLengths
          have sameSize : (canonicalCheckpoint.commitInstructionWord
              (actualPhase.drain rawImage).native).length =
                (archivedCheckpoint.commitInstructionWord
                  (actualPhase.drain rawImage).native).length := by
            rw [canonicalSize, wordSize]
            exact congrArg₂ Nat.sub remainingEq control.2
          obtain ⟨rowBefore, rowAfter, rowTrace, rowJoint, rowLegal, rowMoved,
              _initial, rowKept, _rowSaved, rowGeneration, rowDepth, rowRank⟩ :=
            source_commit_rank_before_exit setup (named.val - actualPhase.low) canonicalStart
              canonicalCheckpoint.trace (control.1.trans starts.1) named.val
              (by rw [remainingEq, starts.2.1]; omega)
              (by change named.val < instructionCount setup.program -
                    ProtocolState.commitEnd setup.program canonicalStart.point
                  rw [control.2]
                  change named.val < instructionCount setup.program -
                    ProtocolState.commitEnd setup.program start.saved
                  rw [starts.2.2]
                  exact bounds.2)
              canonicalClosed canonicalSteps canonicalPath (Or.inr (by omega))
          have actualRowKept := setup.proposalRecoveryEraseTrace_prefix
            ((TracePrefix.extend .refl joint legal moved).trans kept)
          have decodedRowKept := ((TracePrefix.extend .refl rowJoint rowLegal rowMoved).trans
            rowKept).trans canonicalClosedKept
          have rowControl : setup.commitRecoveryControl (some rowBefore) =
              setup.commitRecoveryControl (some current) := by
            have generations := congrArg CommitAttemptId.generation canonicalAttempt'
            have emittedGeneration := congrArg CommitAttemptId.generation exitAttempt
            simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control]
            rw [rowRank, position, rowGeneration]
            change canonicalState.generation * (instructionCount setup.program + 1) +
                named.val + 1 = current.generation * (instructionCount setup.program + 1) +
                  named.val + 1
            have equal : canonicalState.generation = current.generation :=
              generations.trans (emittedGeneration.trans generation.symm)
            rw [equal]
          have rowSame := setup.commitRecovery_ancestor_eq_of_control_eq
            decodedRowKept.reachesWithin actualRowKept.reachesWithin rowControl
          have actualDepth := congrArg
            (fun history : setup.commitRecoveryProtocol.History => history.trace.length) rowSame
          rw [setup.proposalRecoveryEraseTrace_length, rowDepth] at actualDepth
          have geometry := source_decoded_binding_row setup canonicalCheckpoint
            (actualPhase.drain rawImage).native canonicalClosed canonicalPath nativeWord
            cut.completed canonicalClosedKept current next sourcePrior joint legal moved kept
            (by omega) (by omega)
          obtain ⟨_saved, _generation, geometry⟩ := geometry
          generalize decomposition : commitPhase canonicalCheckpoint.residual.tail = segment
            at geometry
          rcases segment with ⟨Ξ, Q, suffix, block, reconstruct, boundary⟩
          dsimp only at geometry
          obtain ⟨rowEvent, rowOwner, rowPayload, rowBinding, rowPosition,
            receiptActive, geometry⟩ := geometry
          have sameEvent : rowEvent = named := Fin.ext (rowPosition.trans position)
          subst rowEvent
          obtain ⟨sameOwner, samePayload⟩ := EventField.binding.inj (rowBinding.symm.trans binding)
          subst rowOwner
          subst rowPayload
          have active : owner ∉ current.excluded := receiptActive canonicalReceipt
            (by rw [acceptedAtExit]; exact Option.some_ne_none _)
          obtain ⟨Δ, P, name, fresh, guard, earlier, rest, earlierLength, splitBlock,
            selectedIndex, terminalCell, data, namedCell⟩ := geometry active
          have literal : phaseRecoveryBindingData setup .concurrent named owner payload binding
              ((joint owner).map (·.semantic)) =
                (reference.execution.application.current.native.bindingResult handle payload,
                  false) := by
            simpa only [acceptedAtExit, Option.elim_some, Option.isNone_some, meaning] using data
          obtain ⟨committing, acting, _decode⟩ := source_binding_at_rank setup.program
            current.point named owner payload binding position.symm
          have ownNoMiss : CommitRecoveryMove.missed
              (Setup.proposalRecoveryJoint joint owner) = false := by
            change (((joint owner).map (·.semantic)).elim false (·.missing)) = false
            by_cases missing : (((joint owner).map (·.semantic)).elim false (·.missing)) = true
            · have impossible := congrArg Prod.snd literal
              simp only [phaseRecoveryBindingData, missing, ↓reduceIte] at impossible
              cases impossible
            · exact Bool.eq_false_iff.mpr missing
          have noMiss : ∀ actor,
              CommitRecoveryMove.missed (Setup.proposalRecoveryJoint joint actor) = false := by
            intro actor
            by_cases same : actor = owner
            · subst actor; exact ownNoMiss
            · have offered := legal.2 actor
              cases chosen : joint actor with
              | none => simp [Setup.proposalRecoveryJoint, chosen, CommitRecoveryMove.missed]
              | some move =>
                  rw [chosen] at offered
                  exact (same (Option.some.inj (offered.1.1.symm.trans acting))).elim
          have afterActive : owner ∉ next.excluded := by
            obtain ⟨result, supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp nextSupport
            have rawSupported : result.1 ∈ (ProtocolState.recoveryStep setup.program current.point
                current.excluded (Setup.proposalRecoveryJoint joint)).support := by
              rw [← map_val_pmfToSubtype
                (ProtocolState.recoveryStep setup.program current.point current.excluded
                  (Setup.proposalRecoveryJoint joint))
                (fun result supported => ProtocolState.recoveryStep_excluded_monotone
                  setup.program current.point current.excluded _ result supported)]
              exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
            have same := (ProtocolState.recoveryStep_noMiss_observe owner setup.program
              current.point current.point rfl committing current.excluded current.excluded
              active active _ _ rfl noMiss _ rawSupported _ rawSupported).2
            rw [← equal, CommitRecoveryState.close_excluded]
            change owner ∉ result.val.2
            rw [same]
            exact active
          exact ⟨active, afterActive, literal⟩
        · let retiredAttempt := exitBefore.execution.application.attempt
          have settleAbsent : ∀ phases generation entry current
              (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent))),
              phases.IsChain (fun before after => before.high = after.low) →
              retiredAttempt.Precedes ⟨PhaseRuntimeState.phaseLow phases, generation⟩ →
              (∀ record ∈ retired, record.attempt ≠ retiredAttempt) →
              let result := PhaseRuntimeState.settle phases generation entry current retired
              result.Ordered ∧ retiredAttempt.Precedes result.attempt ∧
                ∀ record ∈ result.retired, record.attempt ≠ retiredAttempt := by
            intro phases generation entry current retired ordered earlier absent
            refine ⟨PhaseRuntimeState.settle_ordered _ _ _ _ _ ordered, ?_, ?_⟩
            · have progress := PhaseRuntimeState.settle_namespace phases generation entry
                current retired ordered
              rcases earlier with lower | ⟨same, lower⟩
              · exact Or.inl (lower.trans_le progress.1)
              · by_cases equal : retiredAttempt.generation =
                    (PhaseRuntimeState.settle phases generation entry current retired).generation
                · exact Or.inr ⟨equal, lower.trans_le progress.2⟩
                · have grows := progress.1
                  change generation ≤
                    (PhaseRuntimeState.settle phases generation entry current retired).generation
                      at grows
                  change retiredAttempt.generation = generation at same
                  apply Or.inl
                  change retiredAttempt.generation <
                    (PhaseRuntimeState.settle phases generation entry current retired).generation
                  omega
            · induction phases generalizing generation entry current retired with
              | nil => exact absent
              | cons phase remaining ih =>
                  have tailLow : phase.low < PhaseRuntimeState.phaseLow remaining := by
                    cases remaining with
                    | nil => exact phase.nonempty.trans_le phase.bounded
                    | cons next rest =>
                        exact phase.nonempty.trans_eq (List.isChain_cons_cons.mp ordered).1
                  have later : retiredAttempt.Precedes
                      ⟨PhaseRuntimeState.phaseLow remaining, generation⟩ := by
                    rcases earlier with lower | ⟨same, lower⟩
                    · exact Or.inl lower
                    · exact Or.inr ⟨same, lower.trans tailLow⟩
                  have unequal : (⟨phase.low, generation⟩ : CommitAttemptId) ≠ retiredAttempt := by
                    intro equal
                    rw [← equal] at earlier
                    rcases earlier with impossible | ⟨_, impossible⟩ <;>
                      exact Nat.lt_irrefl _ impossible
                  have extended : ∀ record ∈ retired ++
                      [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩],
                      record.attempt ≠ retiredAttempt := by
                    intro record member
                    rcases List.mem_append.mp member with old | added
                    · exact absent record old
                    · cases List.mem_singleton.mp added; exact unequal
                  simp only [PhaseRuntimeState.settle]
                  split
                  · split
                    · split
                      · exact extended
                      · exact ih _ _ _ _ ordered.tail later extended
                    · exact ih _ _ _ _ ordered.tail later absent
                  · exact absent
          have absentInvariant : (nativeApplication).Invariant (fun state => state.Ordered ∧
              retiredAttempt.Precedes state.attempt ∧
                ∀ record ∈ state.retired, record.attempt ≠ retiredAttempt) := by
            constructor
            · intro state actor material valid; exact valid
            · intro state packet next valid handled
              change state.handle implementation.runtime packet = some next at handled
              unfold PhaseRuntimeState.handle at handled
              split at handled
              · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp handled
                exact settleAbsent _ _ _ _ _ valid.1 valid.2.1 valid.2.2
              · cases handled
            · intro state command next valid supported
              change next ∈ (state.environment implementation.runtime command).support at supported
              unfold PhaseRuntimeState.environment at supported
              split at supported
              · obtain ⟨native, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
                exact settleAbsent _ _ _ _ _ valid.1 valid.2.1 valid.2.2
              · cases (PMF.mem_support_pure_iff _ _).mp supported; exact valid
          have oldChronology := PhaseRuntimeState.retiredOrdered_history implementation.runtime
            implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
            implementation.horizon implementation.scheduler
            (by
              rw [← initialEq]
              exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
                implementation.scheduler exitTrace)
          have oldAbsent : ∀ record ∈ exitBefore.execution.application.retired,
              record.attempt ≠ retiredAttempt := by
            intro record member equal
            have earlier := oldChronology.2 record member
            rw [equal] at earlier
            rcases earlier with impossible | ⟨_, impossible⟩ <;> exact Nat.lt_irrefl _ impossible
          have tailLow : actualPhase.low < PhaseRuntimeState.phaseLow remaining := by
            have ordered := exitOrdered
            change exitBefore.execution.application.phases.IsChain _ at ordered
            rw [installed] at ordered
            cases remaining with
            | nil => exact actualPhase.nonempty.trans_le actualPhase.bounded
            | cons next rest =>
                exact actualPhase.nonempty.trans_eq (List.isChain_cons_cons.mp ordered).1
          have afterValid : exitAfter.execution.application.Ordered ∧
              retiredAttempt.Precedes exitAfter.execution.application.attempt ∧
              ∀ record ∈ exitAfter.execution.application.retired,
                record.attempt ≠ retiredAttempt := by
            rw [normalized]
            change (let result := (PhaseRuntimeState.settle
                exitBefore.execution.application.phases exitBefore.execution.application.generation
                exitBefore.execution.application.entry rawImage
                exitBefore.execution.application.retired);
              result.Ordered ∧ retiredAttempt.Precedes result.attempt ∧
                ∀ record ∈ result.retired, record.attempt ≠ retiredAttempt)
            dsimp only
            rw [installed, PhaseRuntimeState.settle_clean actualPhase remaining _ _ _ _
              finished (by intro failed; exact dirty failed.2)]
            apply settleAbsent
            · have ordered := exitOrdered
              change exitBefore.execution.application.phases.IsChain _ at ordered
              rw [installed] at ordered
              exact ordered.tail
            · apply Or.inr
              refine ⟨rfl, ?_⟩
              simpa only [retiredAttempt, PhaseRuntimeState.attempt, installed,
                List.head?_cons, Option.map_some, Option.getD_some] using tailLow
            · exact oldAbsent
          have noArchive := (absentInvariant.tracePrefix (nativeMenu) nativeInitial
            implementation.horizon implementation.scheduler exitAfter cut.entry exitAfterTrace
            entryNative beforeEntry afterValid).2.2
          have entryHistory : (⟨some cut.cursor.current,
              setup.proposalRecoveryEraseTrace cut.cursor.trace⟩ :
                setup.commitRecoveryProtocol.History) =
              ⟨_, cut.witness.checkpoint.trace⟩ := by
            have same := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
              (⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ :
                setup.commitRecoveryProtocol.History)) cut.cursorHistory
            simpa only [setup.proposalRecoveryEraseTrace_lift] using same
          have entryLength := congrArg
            (fun history : setup.commitRecoveryProtocol.History => history.trace.length)
              entryHistory
          rw [setup.proposalRecoveryEraseTrace_length] at entryLength
          have rowUntilCursor : TracePrefix (sourcePrior.extend joint legal moved)
              cut.cursor.trace := by
            obtain ⟨earlierState, earlier, earlierKept, earlierDepth⟩ :=
              setup.proposalRecovery_prefix_at_depth cut.cursor.trace (sourcePrior.length + 1)
                (by omega)
            have same := (earlierKept.trans (cut.past.trans cut.future)).eq_of_same_length kept
              (by simp only [Trace.length]; exact earlierDepth)
            cases same
            exact earlierKept
          have committing := (source_binding_at_rank setup.program current.point
            named owner payload binding position.symm).1
          have entrySteps := congrArg
            (fun history : setup.commitRecoveryProtocol.History =>
              proposalSourceSteps setup history.trace) entryHistory
          have nonempty : ∀ {state : setup.proposalRecoveryProtocol.State}
              (history : setup.proposalRecoveryProtocol.Trace state),
              state ≠ none → 0 < history.length := by
            intro state history
            cases history with
            | start => intro impossible; exact (impossible rfl).elim
            | extend => intro _; simp only [Trace.length]; omega
          obtain ⟨state, checkpoint, image, closed, steps, later, path, onward, lower, upper,
              instructions, _addresses, kind⟩ :=
            source_commit_chunk setup cut.witness.origins sourcePrior.length
              (nonempty sourcePrior (by simp))
              (by omega) (by
                rw [← entrySteps]
                exact source_commit_step_readback setup current next sourcePrior joint legal
                  moved committing cut.cursor.trace rowUntilCursor)
          have entryPath := (setup.proposalRecoveryEraseTrace_prefix
            (cut.past.trans cut.future)).reachesWithin
          change setup.commitRecoveryProtocol.ReachesWithin _
            ⟨some cut.cursor.current, setup.proposalRecoveryEraseTrace cut.cursor.trace⟩
            ⟨_, setup.proposalRecoveryEraseTrace cut.completed.trace⟩ at entryPath
          rw [entryHistory] at entryPath
          have closedKept := (onward.trans entryPath).tracePrefix
          have decoded := source_decoded_binding_row setup checkpoint image closed path
            instructions cut.completed closedKept current next sourcePrior joint legal moved
            kept lower upper
          have lowEq := checkpoint.saved_position
          rw [← decoded.1] at lowEq
          have phaseEq : state.attempt.phase = exitBefore.execution.application.attempt.phase :=
            lowEq.symm.trans (saved.trans (congrArg CommitAttemptId.phase exitAttempt.symm))
          have generationEq : state.attempt.generation =
              exitBefore.execution.application.attempt.generation :=
            decoded.2.1.symm.trans
              (generation.trans (congrArg CommitAttemptId.generation exitAttempt.symm))
          have namespaceEq : state.attempt = retiredAttempt :=
            congrArg₂ CommitAttemptId.mk phaseEq generationEq
          rcases kind with ⟨record, member, _image, attempt⟩ |
            ⟨nextState, nextCheckpoint, phase, remaining', installed', kind', _generation,
              _boundary, _image, closedEq⟩
          · exact (noArchive record member (attempt.symm.trans namespaceEq)).elim
          · cases closedEq
            have low : state.attempt.phase = phase.low := by
              simp only [PhaseRuntimeState.attempt, installed', List.head?_cons,
                Option.map_some, Option.getD_some]
            have localCommit := checkpoint.compiled.atCommit_of_bindingPhase setup.program
              .concurrent checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations
              checkpoint.registry checkpoint.embedding checkpoint.before state.attempt.phase
              phase kind' low.symm checkpoint.source
            exact cleanCase checkpoint nextCheckpoint image localCommit path instructions
              closedKept lower upper onward.tracePrefix exitBefore exitAfter exitTrace exitJoint
              exitLegal exitMoved exitRetained beforeEntry rawImage remaining installed exitAttempt
              normalized effect changed finished acceptedAtExit dirty
      exact ⟨record, material, message, current, next, sourcePrior, joint, legal, moved,
        owned, recorded, transmitted, emitted, call, receipt, kept, generation, saved,
        position, matching.1, matching.2.1, matching.2.2, rowLocation, entryLocation⟩

/-- Proper accepted handles read the corresponding target source value,
including canceled rows and current rows after the focal cut. -/
theorem sourceHandleMeaning_of_accepted_binding
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (good : setup.proposalRecoveryForeignGood who g)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (G : setup.proposalRecoveryProtocol.History)
    (supported : G ∈ (sourceForcedBlock setup values who g choice).support)
    (before : (nativeApplication).Control)
    (prior : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before))
    (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (owner : Player) (payload : L.Ty)
    (named : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent)) (old : L.Val payload)
    (accepted : snapshot.accepted (.inr named) = some handle)
    (stored : (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)).get? snapshot.config.store = some (.success old)) :
    ∃ new : L.Val payload,
      reference.execution.application.current.native.candidates.lookup handle =
        .openable (⟨payload, old⟩ : Raw L) ∧
      sourceHandleMeaning setup implementation G reference handle = some ⟨payload, new⟩ ∧
      (owner = who → new = old) := by
  classical
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  obtain ⟨priorNative, traceNative, retainedNative⟩ :
      ∃ (first : (nativeProtocol).Trace (some before))
        (last : (nativeProtocol).Trace (some reference)), TracePrefix first last := by
    rw [initialEq]
    exact ⟨prior, trace, retained⟩
  obtain ⟨valid, preserved⟩ := accepted_snapshot_catalogue setup implementation
    reference traceNative
    before priorNative retainedNative snapshot selected owner payload
      ⟨.inr named, binding⟩ handle accepted
  obtain ⟨candidate, associated, _owned, opened⟩ :=
    valid.success_provenance ⟨.inr named, binding⟩ old stored
  have same : candidate = handle := Option.some.inj (associated.symm.trans accepted)
  subst candidate
  have original := preserved.trans opened
  have oldMeaning : reference.execution.application.current.native.bindingResult handle payload =
      .success old := by
    simp [State.bindingResult, original, Raw.as?]
  obtain ⟨record, material, message, current, next, sourcePrior, joint, legal, moved,
    handleOwner, recorded, transmitted, emitted, call, _receipt, kept, generation, saved,
    position, active, survives, literal, location, _entryLocation⟩ :=
    source_admitted_binding_row setup values implementation operational reference trace who event
      cut before prior retained snapshot selected owner payload named binding handle accepted
  have authored : record ∈ reference.execution.recall handle.1 := by
    simpa only [handleOwner] using recorded
  rcases location with past | ⟨later, currentAttempt, foreign⟩
  · have read : phaseRecoveryBindingData setup .concurrent named owner payload binding
        ((joint owner).map (·.semantic)) = (.success old, false) := by
      simpa only [oldMeaning] using literal
    obtain ⟨value, atG, focal⟩ := sourceBindingAt_same_information setup who owner
      message.payload.attempt named payload binding current next sourcePrior joint legal moved
      generation saved position active survives old read ⟨some cut.current, cut.trace⟩ g
      past sameInfo.symm good
    have continuationPrefix : TracePrefix g.trace G.trace := by
      have support := supported
      unfold sourceForcedBlock at support
      obtain ⟨middle, first, last⟩ := (PMF.mem_support_bind_iff ..).mp support
      exact ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
        g middle first).tracePrefix).trans
          ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
            middle G last).tracePrefix)
    obtain ⟨source, preceding, choices, offered, target, reached, retainedRow,
      sourceGeneration, sourceSaved, sourcePosition, actual⟩ :=
      sourceBindingAt_origin setup message.payload.attempt named owner payload binding
        g.trace value atG
    have atFinal : sourceBindingAt setup message.payload.attempt named owner payload binding
        G.trace = some value :=
      sourceBindingAt_of_origin setup message.payload.attempt named owner payload binding
        source preceding choices offered target reached sourceGeneration sourceSaved sourcePosition
        (.success value, false) actual G.trace (retainedRow.trans continuationPrefix)
    exact ⟨value, original, sourceHandleMeaning_of_emission setup implementation G reference
      traceNative
      handle record authored message emitted named call owner payload binding (some value) atFinal,
      focal⟩
  · have inherited := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix (cut.past.trans later)).reachesWithin
    change cut.cursor.current.excluded ⊆ current.excluded at inherited
    have entryActive : owner ∉ cut.cursor.current.excluded :=
      fun member => active (inherited member)
    obtain ⟨value, meaning⟩ := sourceHandleMeaning_of_current_emission setup values implementation
      operational reference trace who event cut g sameInfo good choice properChoice G supported
      owner entryActive record recorded material transmitted message emitted currentAttempt
      named payload binding handle call
    exact ⟨value, original, meaning, fun same => False.elim (foreign same)⟩

/-- A focal failed binding remains a literal failed source action under
equal full focal information and every retained source continuation. -/
theorem sourceHandleMeaning_of_focal_failure
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (G : setup.proposalRecoveryProtocol.History)
    (supported : G ∈ (sourceForcedBlock setup values who g choice).support)
    (before : (nativeApplication).Control)
    (prior : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before))
    (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (payload : L.Ty) (named : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding who payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted (.inr named) = some handle)
    (failed : reference.execution.application.current.native.bindingResult handle payload =
      .failure) :
    sourceHandleMeaning setup implementation G reference handle = none := by
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  obtain ⟨priorNative, traceNative, retainedNative⟩ :
      ∃ (first : (nativeProtocol).Trace (some before))
        (last : (nativeProtocol).Trace (some reference)), TracePrefix first last := by
    rw [initialEq]
    exact ⟨prior, trace, retained⟩
  obtain ⟨record, material, message, current, next, sourcePrior, joint, legal, moved,
    handleOwner, recorded, _transmitted, emitted, call, _receipt, _kept, generation, saved,
    position, _active, _survives, literal, location, _entryLocation⟩ :=
    source_admitted_binding_row setup values implementation operational reference trace who event
      cut before prior retained snapshot selected who payload named binding handle accepted
  have past : TracePrefix (sourcePrior.extend joint legal moved) cut.trace := by
    rcases location with past | ⟨_later, _attempt, foreign⟩
    · exact past
    · exact (foreign rfl).elim
  obtain ⟨sourceState, targetState, preceding, choices, offered, reached, kept,
    beforeInfo, _afterInfo, own⟩ := source_information_row setup who sourcePrior joint legal moved
      cut.trace g.trace past sameInfo.symm
  have metadata := source_information_metadata setup who ⟨some current, sourcePrior⟩
    ⟨sourceState, preceding⟩ beforeInfo
  cases sourceState with
  | none => exact metadata.elim
  | some source =>
      obtain ⟨target, _targetSupport, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
      have actual : phaseRecoveryBindingData setup .concurrent named who payload binding
          ((choices who).map (·.semantic)) = (.failure, false) := by
        rw [← own]
        simpa only [failed] using literal
      have continuationPrefix : TracePrefix g.trace G.trace := by
        have support := supported
        unfold sourceForcedBlock at support
        obtain ⟨middle, first, last⟩ := (PMF.mem_support_bind_iff ..).mp support
        exact ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
          g middle first).tracePrefix).trans
            ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
              middle G last).tracePrefix)
      have atFinal : sourceBindingAt setup message.payload.attempt named who payload binding
          G.trace = none := by
        apply sourceBindingAt_of_origin setup message.payload.attempt named who payload binding
          source preceding choices offered (some target) reached
          (metadata.2.2.2.2.symm.trans generation) _ _ (.failure, false) actual G.trace
          (kept.trans continuationPrefix)
        · rw [← (ProtocolState.MetadataEq.controls setup.program current.saved source.saved
            metadata.2.1).1]
          exact saved
        · rw [← (ProtocolState.MetadataEq.controls setup.program current.point source.point
            metadata.1).1]
          exact position
      have authored : record ∈ reference.execution.recall handle.1 := by
        simpa only [handleOwner] using recorded
      exact sourceHandleMeaning_of_emission setup implementation G reference traceNative handle
        record authored message emitted named call who payload binding none atFinal

omit [Fintype Player] in
/-- Consecutive actual instruction windows concatenate without inserting a
second row for a close or an exhausted automatic rebuild. -/
private theorem instruction_path_append
    (initializer : SourceProgram.Config Player L setup.context)
    {first middle last : CommitRecoveryState setup.program}
    {left right : List (Player → Option (CommitRecoveryMove Player L))}
    {before after : List (Option Nat × (Finset Player × Nat × Nat))}
    (earlier : CommitRecoveryState.InstructionPath setup.program initializer
      left before first middle)
    (later : CommitRecoveryState.InstructionPath setup.program initializer
      right after middle last) :
    CommitRecoveryState.InstructionPath setup.program initializer (left ++ right) (before ++ after)
      first last := by
  induction earlier with
  | refl => exact later
  | step legal reached rest ih => exact .step legal reached (ih later)

omit [Fintype Player] in
/-- A literal initialized-source prefix interval carries its actual raw
instruction word and post-close address word. Its length counts source rows,
including exactly one row for the last commitment instruction. -/
theorem source_instruction_window
    (initializer : SourceProgram.Config Player L setup.context)
    (current : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some current))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (kept : TracePrefix prior trace) :
    ∃ (last : CommitRecoveryState setup.program)
      (joints : List (Player → Option (CommitRecoveryMove Player L)))
      (addresses : List (Option Nat × (Finset Player × Nat × Nat))),
      state = some last ∧
      CommitRecoveryState.InstructionPath setup.program initializer joints addresses current last ∧
      joints.length + prior.length = trace.length ∧
      setup.recoveryJointRecall trace = joints.reverse ++ setup.recoveryJointRecall prior ∧
      setup.recoveryAddressWord trace = setup.recoveryAddressWord prior ++ addresses := by
  induction kept with
  | refl =>
      exact ⟨current, [], [], rfl, .refl current,
        by simp only [List.length_nil, Nat.zero_add], rfl, (List.append_nil _).symm⟩
  | @extend before after earlier retained joint legal reached ih =>
      obtain ⟨middle, joints, addresses, stateEq, path, length, word, signals⟩ := ih
      cases stateEq
      obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
      let choices : Player → Option (CommitRecoveryMove Player L) := joint
      have rawLegal : (SourceProgram.commitRecoveryProtocol setup.program initializer).Legal
          middle choices := legal
      have rawSupport : next ∈
          ((SourceProgram.commitRecoveryProtocol setup.program initializer).step middle
            ⟨choices, rawLegal⟩).support := supported
      have combined := instruction_path_append setup initializer path
        (CommitRecoveryState.InstructionPath.step rawLegal rawSupport (.refl next))
      refine ⟨next, joints ++ [choices], addresses ++ [next.publicAddress], rfl, combined,
        ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton, Trace.length]
        omega
      · simp only [Setup.recoveryJointRecall, List.reverse_append, List.reverse_singleton,
          List.nil_append, word, List.cons_append, choices]
      · rw [setup.recoveryAddressWord_extend, signals]
        simp only [Option.elim_some, List.append_assoc]

omit [Fintype Player] in
/-- An actual target interval of the literal block length determines its
complete target attempt and its exact closed endpoint. Its own instruction
word is extracted from that interval, with no reference-word equality. -/
theorem source_attempt_of_literal_window
    (initializer : SourceProgram.Config Player L setup.context)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
    (entry : SourceProgram.Config Player L Γ)
    (current last : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (trace : setup.proposalRecoveryProtocol.Trace (some last))
    (kept : TracePrefix prior trace)
    (point : current.point = lift (ProtocolState.entry (block.prepend suffix) entry))
    (saved : ProtocolState.atCommit setup.program current.saved = true)
    (endpoint : ProtocolState.commitEnd setup.program current.saved ≤ instructionCount suffix)
    (positive : 0 < block.length)
    (depth : trace.length = prior.length + block.length) :
    ∃ (finished : SourceProgram.Config Player L Δ) (excluded : Finset Player)
      (attempt : block.Attempt entry current.excluded finished excluded)
      (addresses : List (Option Nat × (Finset Player × Nat × Nat))),
      CommitRecoveryState.InstructionPath setup.program initializer attempt.joints addresses
        current last ∧
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace trace) =
        attempt.joints.reverse ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior) ∧
      setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace trace) =
        setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace prior) ++ addresses ∧
      ∃ monotone : current.excluded ⊆ excluded,
        last = (current.install
          (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), excluded)
          monotone).close := by
  obtain ⟨target, joints, addresses, stateEq, path, length, word, signals⟩ :=
    source_instruction_window setup initializer current (setup.proposalRecoveryEraseTrace prior)
      (setup.proposalRecoveryEraseTrace trace) (setup.proposalRecoveryEraseTrace_prefix kept)
  have equal : last = target := Option.some.inj stateEq
  subst target
  have wordLength : joints.length = block.length := by
    rw [setup.proposalRecoveryEraseTrace_length, setup.proposalRecoveryEraseTrace_length]
      at length
    omega
  obtain ⟨finished, excluded, attempt, actual, monotone, closed⟩ :=
    SourceProgram.CommitPrefix.attempt_of_instructions initializer block suffix lift origin entry
      current last joints addresses point saved endpoint positive path wordLength
  rw [← actual] at path word
  exact ⟨finished, excluded, attempt, addresses, path, word, signals, monotone, closed⟩

omit [Fintype Player] in
/-- Metadata at an entry has an actual Config of the same residual source
type. Its private values and private action history remain unrestricted. -/
private theorem config_of_entry_metadata
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first : SourceProgram.Config Player L Γ)
    (second : ProtocolState program)
    (related : ProtocolState.MetadataEq program (ProtocolState.entry program first) second) :
    ∃ config : SourceProgram.Config Player L Γ,
      second = ProtocolState.entry program config ∧ first.MetadataEq config := by
  cases program with
  | ret payoffs => exact ⟨second, rfl, related⟩
  | sample name fresh law tail =>
      cases second with
      | inl config => exact ⟨config, rfl, related⟩
      | inr point => cases related
  | commit name owner fresh guard tail =>
      cases second with
      | inl config => exact ⟨config, rfl, related⟩
      | inr point => cases related
  | reveal published owner name fresh selected unresolved tail =>
      cases second with
      | inl config => exact ⟨config, rfl, related⟩
      | inr point => cases related

omit [Fintype Player] in
/-- The literal source suffix extracts the actual target entry. This uses
metadata to identify syntax and deferred code, rather than identifying the
reference and target instruction words or their private histories. -/
theorem config_of_lifted_entry_metadata
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program program lift)
    (first : SourceProgram.Config Player L Γ) (second : ProtocolState setup.program)
    (related : ProtocolState.MetadataEq setup.program
      (lift (ProtocolState.entry program first)) second) :
    ∃ config : SourceProgram.Config Player L Γ,
      second = lift (ProtocolState.entry program config) ∧ first.MetadataEq config := by
  obtain ⟨localPoint, image, localMetadata⟩ :=
    Setup.metadata_restrict_to_suffix origin (ProtocolState.entry program first) second related
  obtain ⟨config, localEntry, metadata⟩ :=
    config_of_entry_metadata program first localPoint localMetadata
  exact ⟨config, image.trans (congrArg lift localEntry), metadata⟩

omit [Fintype Player] in
/-- Full focal information supplies the actual target current and saved
entries independently. Both target histories are retained literally; only
their metadata and the public controls are inherited from the reference. -/
theorem source_target_entries
    (who : Player) (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (target : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryModel.infoOf who prior =
      setup.proposalRecoveryModel.infoOf who target.trace)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (live : SourceProgram Player L Γ O) (saved : SourceProgram Player L Δ P)
    (liveLift : ProtocolState live → ProtocolState setup.program)
    (savedLift : ProtocolState saved → ProtocolState setup.program)
    (liveOrigin : ProtocolSuffix setup.program live liveLift)
    (savedOrigin : ProtocolSuffix setup.program saved savedLift)
    (liveConfig : SourceProgram.Config Player L Γ)
    (savedConfig : SourceProgram.Config Player L Δ)
    (livePoint : current.point = liveLift (ProtocolState.entry live liveConfig))
    (savedPoint : current.saved = savedLift (ProtocolState.entry saved savedConfig)) :
    ∃ (other : CommitRecoveryState setup.program)
      (targetLive : SourceProgram.Config Player L Γ)
      (targetSaved : SourceProgram.Config Player L Δ),
      target.state = some other ∧
      other.point = liveLift (ProtocolState.entry live targetLive) ∧
      other.saved = savedLift (ProtocolState.entry saved targetSaved) ∧
      liveConfig.MetadataEq targetLive ∧ savedConfig.MetadataEq targetSaved ∧
      current.excluded = other.excluded ∧ current.entryExcluded = other.entryExcluded ∧
      current.generation = other.generation := by
  have metadata := source_information_metadata setup who ⟨some current, prior⟩ target same
  cases state : target.state with
  | none =>
      rw [state] at metadata
      exact metadata.elim
  | some other =>
      rw [state] at metadata
      have liveMetadata : ProtocolState.MetadataEq setup.program
          (liveLift (ProtocolState.entry live liveConfig)) other.point := by
        rw [← livePoint]
        exact metadata.1
      have savedMetadata : ProtocolState.MetadataEq setup.program
          (savedLift (ProtocolState.entry saved savedConfig)) other.saved := by
        rw [← savedPoint]
        exact metadata.2.1
      obtain ⟨targetLive, liveEq, liveMeta⟩ := config_of_lifted_entry_metadata setup live
        liveLift liveOrigin liveConfig other.point liveMetadata
      obtain ⟨targetSaved, savedEq, savedMeta⟩ := config_of_lifted_entry_metadata setup saved
        savedLift savedOrigin savedConfig other.saved savedMetadata
      exact ⟨other, targetLive, targetSaved, rfl, liveEq, savedEq, liveMeta, savedMeta,
        metadata.2.2.1, metadata.2.2.2.1, metadata.2.2.2.2⟩

omit [Fintype Player] in
/-- The raw exclusion after an active commitment is determined before close.
The result holds inside any compiler suffix and includes the closing row. -/
private theorem raw_commit_excluded
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) :
    ∀ (point : ProtocolState program) (excluded : Finset Player)
      (joint : Player → Option (CommitRecoveryMove Player L)) (owner : Player)
      (result : ProtocolState program × Finset Player),
      ProtocolState.atCommit program point = true →
      ProtocolState.actor program point = some owner →
      result ∈ (ProtocolState.recoveryStep program point excluded joint).support →
      result.2 = if owner ∈ excluded then excluded else
        excludeCommit excluded owner (CommitRecoveryMove.missed (joint owner)) := by
  induction program with
  | ret =>
      intro point excluded joint owner result committing
      cases committing
  | sample name fresh law tail ih =>
      intro point excluded joint owner result committing acting reached
      cases point with
      | inl config => cases committing
      | inr point =>
          obtain ⟨raw, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
          exact ih point excluded joint owner raw committing acting supported
  | commit name author fresh guard tail ih =>
      intro point excluded joint owner result committing acting reached
      cases point with
      | inl config =>
          have ownerEq : author = owner := Option.some.inj acting
          subst owner
          simp only [ProtocolState.recoveryStep, Sum.elim_inl] at reached
          by_cases inactive : author ∈ excluded
          · rw [ite_eq_left inactive, PMF.mem_support_pure_iff] at reached
            cases reached
            exact (ite_eq_left inactive).symm
          · rw [ite_eq_right inactive, PMF.mem_support_pure_iff] at reached
            cases reached
            rw [ite_eq_right inactive]
            rfl
      | inr point =>
          obtain ⟨raw, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
          exact ih point excluded joint owner raw committing acting supported
  | reveal published author name fresh selected unresolved tail ih =>
      intro point excluded joint owner result committing acting reached
      cases point with
      | inl config => cases committing
      | inr point =>
          obtain ⟨raw, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
          exact ih point excluded joint owner raw committing acting supported

omit [Fintype Player] in
/-- Closing does not create a commitment omission. For an active row the
actual post-row exclusion determines its missing bit, including at block end. -/
theorem source_binding_missing_iff
    (current next : CommitRecoveryState setup.program)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (reached : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (position : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (active : owner ∉ current.excluded) :
    (phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic))).2 = true ↔ owner ∈ next.excluded := by
  obtain ⟨committing, acting, _decode⟩ := source_binding_at_rank setup.program current.point
    event owner payload binding position
  have supported : next ∈ (current.step (Setup.proposalRecoveryJoint joint)).support := by
    obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff ..).mp reached
    cases Option.some.inj equal
    exact member
  obtain ⟨raw, rawSupport, closed⟩ :=
    current.step_raw_result (Setup.proposalRecoveryJoint joint) next supported
  have mask : next.excluded =
      excludeCommit current.excluded owner
        (CommitRecoveryMove.missed (Setup.proposalRecoveryJoint joint owner)) := by
    rw [closed, CommitRecoveryState.close_excluded]
    exact (raw_commit_excluded setup.program current.point current.excluded
      (Setup.proposalRecoveryJoint joint) owner raw.val committing acting rawSupport).trans
        (ite_eq_right active)
  have second : (phaseRecoveryBindingData setup .concurrent event owner payload binding
        ((joint owner).map (·.semantic))).2 =
      CommitRecoveryMove.missed (Setup.proposalRecoveryJoint joint owner) := by
    change (phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic))).2 =
        ((joint owner).map (·.semantic)).elim false (·.missing)
    cases missing : ((joint owner).map (·.semantic)).elim false (·.missing) <;>
      simp only [phaseRecoveryBindingData, missing, Bool.false_eq_true, ↓reduceIte]
  rw [second, mask]
  cases CommitRecoveryMove.missed (Setup.proposalRecoveryJoint joint owner) <;>
    simp only [excludeCommit, Bool.false_eq_true, ↓reduceIte,
      Finset.mem_insert, true_or, active, iff_self]

omit [Fintype Player] in
/-- Equal full focal information fixes every active historical missing bit.
The argument uses both actual row masks; hidden foreign actions remain free. -/
private theorem source_binding_missing_eq
    (who owner : Player) (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current next other after : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (target : setup.proposalRecoveryProtocol.Trace (some other))
    (joint choices : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (offered : setup.proposalRecoveryProtocol.Legal (some other) choices)
    (moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (reached : some after ∈
      (setup.proposalRecoveryProtocol.step (some other) ⟨choices, offered⟩).support)
    (beforeInfo : setup.proposalRecoveryModel.infoOf who prior =
      setup.proposalRecoveryModel.infoOf who target)
    (afterInfo : setup.proposalRecoveryModel.infoOf who (prior.extend joint legal moved) =
      setup.proposalRecoveryModel.infoOf who (target.extend choices offered reached))
    (position : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (active : owner ∉ current.excluded) :
    (phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic))).2 =
    (phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((choices owner).map (·.semantic))).2 := by
  have first := source_information_metadata setup who ⟨some current, prior⟩
    ⟨some other, target⟩ beforeInfo
  have last := source_information_metadata setup who
    ⟨some next, prior.extend joint legal moved⟩
    ⟨some after, target.extend choices offered reached⟩ afterInfo
  have otherPosition : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program other.point := by
    rw [← (ProtocolState.MetadataEq.controls setup.program current.point other.point first.1).1]
    exact position
  have otherActive : owner ∉ other.excluded := by
    rw [← first.2.2.1]
    exact active
  apply Bool.eq_iff_iff.mpr
  rw [source_binding_missing_iff setup current next joint legal moved owner event payload binding
    position active,
    source_binding_missing_iff setup other after choices offered reached owner event payload binding
      otherPosition otherActive,
    last.2.2.1]

omit [Fintype Player] in
/-- A literal missing row carries failure before any guard is evaluated. -/
private theorem binding_data_missing_failure
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (move : Option (CommitRecoveryMove Player L)) (result : PublicationResult (L.Val payload))
    (read : phaseRecoveryBindingData setup .concurrent event owner payload binding move =
      (result, true)) : result = .failure := by
  unfold phaseRecoveryBindingData at read
  split at read
  · exact (Prod.mk.inj read).1.symm
  · cases (Prod.mk.inj read).2

omit [Fintype Player] in
/-- The exact typed substitution at an actual active historical row. Missing
rows stay missing, focal accepted failure stays failure, and each proper row
reads its addressed target value. The last row is still the raw attempted row. -/
theorem source_binding_data_transport
    (who owner : Player) (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current next other after : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (target : setup.proposalRecoveryProtocol.Trace (some other))
    (joint choices : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (offered : setup.proposalRecoveryProtocol.Legal (some other) choices)
    (moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (reached : some after ∈
      (setup.proposalRecoveryProtocol.step (some other) ⟨choices, offered⟩).support)
    (beforeInfo : setup.proposalRecoveryModel.infoOf who prior =
      setup.proposalRecoveryModel.infoOf who target)
    (afterInfo : setup.proposalRecoveryModel.infoOf who (prior.extend joint legal moved) =
      setup.proposalRecoveryModel.infoOf who (target.extend choices offered reached))
    (own : joint who = choices who)
    (referenceGood : setup.proposalRecoveryForeignGood who
      ⟨some next, prior.extend joint legal moved⟩)
    (targetGood : setup.proposalRecoveryForeignGood who
      ⟨some after, target.extend choices offered reached⟩)
    (attempt : CommitAttemptId)
    (generation : current.generation = attempt.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved = attempt.phase)
    (position : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (active : owner ∉ current.excluded)
    (completed : setup.proposalRecoveryProtocol.History)
    (retained : TracePrefix (target.extend choices offered reached) completed.trace) :
    let original := phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic))
    phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((choices owner).map (·.semantic)) =
      ((if original.2 then .failure else
        match original.1 with
        | .failure => .failure
        | .success _ => (sourceBindingAt setup attempt event owner payload binding
            completed.trace).elim .failure .success), original.2) := by
  classical
  dsimp only
  have first := source_information_metadata setup who ⟨some current, prior⟩
    ⟨some other, target⟩ beforeInfo
  have last := source_information_metadata setup who
    ⟨some next, prior.extend joint legal moved⟩
    ⟨some after, target.extend choices offered reached⟩ afterInfo
  have otherPosition : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program other.point := by
    rw [← (ProtocolState.MetadataEq.controls setup.program current.point other.point first.1).1]
    exact position
  have otherActive : owner ∉ other.excluded := by
    rw [← first.2.2.1]
    exact active
  have equalMissing := source_binding_missing_eq setup who owner event payload binding
    current next other after prior target joint choices legal offered moved reached beforeInfo
      afterInfo position active
  generalize originalRead : phaseRecoveryBindingData setup .concurrent event owner payload
    binding ((joint owner).map (·.semantic)) = original at equalMissing ⊢
  generalize targetRead : phaseRecoveryBindingData setup .concurrent event owner payload
    binding ((choices owner).map (·.semantic)) = result at equalMissing ⊢
  rcases original with ⟨originalResult, missed⟩
  rcases result with ⟨targetResult, targetMissed⟩
  dsimp only at equalMissing ⊢
  subst targetMissed
  cases missed with
  | true =>
      have failed := binding_data_missing_failure setup owner event payload binding
        ((choices owner).map (·.semantic)) targetResult targetRead
      simp only [↓reduceIte, failed]
  | false =>
      have kept : owner ∉ next.excluded := by
        intro excluded
        have missing := (source_binding_missing_iff setup current next joint legal moved owner
          event payload binding position active).mpr excluded
        rw [originalRead] at missing
        cases missing
      have otherKept : owner ∉ after.excluded := by
        rw [← last.2.2.1]
        exact kept
      cases originalResult with
      | failure =>
          have focal : owner = who := by
            by_contra foreign
            obtain ⟨value, proper⟩ := source_foreign_binding_success setup who owner foreign
              event payload binding current prior joint legal next moved position active kept
                referenceGood
            rw [originalRead] at proper
            cases proper
          have literal : targetResult = .failure := by
            have same : phaseRecoveryBindingData setup .concurrent event owner payload binding
                ((joint owner).map (·.semantic)) =
              phaseRecoveryBindingData setup .concurrent event owner payload binding
                ((choices owner).map (·.semantic)) := by
              have sameOwn : joint owner = choices owner := by simpa only [focal] using own
              rw [sameOwn]
            rw [originalRead, targetRead] at same
            exact (Prod.mk.inj same).1.symm
          simp only [Bool.false_eq_true, ↓reduceIte, literal]
      | success old =>
          obtain ⟨value, actual⟩ : ∃ value : L.Val payload,
              phaseRecoveryBindingData setup .concurrent event owner payload binding
                ((choices owner).map (·.semantic)) = (.success value, false) := by
            by_cases focal : owner = who
            · refine ⟨old, ?_⟩
              have same : phaseRecoveryBindingData setup .concurrent event owner payload binding
                  ((choices owner).map (·.semantic)) =
                phaseRecoveryBindingData setup .concurrent event owner payload binding
                  ((joint owner).map (·.semantic)) := by
                have sameOwn : joint owner = choices owner := by simpa only [focal] using own
                rw [sameOwn]
              exact same.trans originalRead
            · exact source_foreign_binding_success setup who owner focal event payload binding
                other target choices offered after reached otherPosition otherActive otherKept
                  targetGood
          have valueEq : targetResult = .success value :=
            (Prod.mk.inj (targetRead.symm.trans actual)).1
          have read : sourceBindingAt setup attempt event owner payload binding
              completed.trace = some value := by
            apply sourceBindingAt_of_origin setup attempt event owner payload binding other
              target choices offered (some after) reached
              (first.2.2.2.2.symm.trans generation) _ otherPosition.symm
                (.success value, false) actual completed.trace retained
            rw [← (ProtocolState.MetadataEq.controls setup.program current.saved other.saved
              first.2.1).1]
            exact saved
          simp only [Bool.false_eq_true, ↓reduceIte, read, Option.elim_some, valueEq]

/-- A decoder reads the complete target attempt, starting with its target
entry. Each active row compares its typed choice and its distinct omission bit. -/
def sourceAttemptTableReads :
    {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    {block : SourceProgram.CommitPrefix Γ O Δ P} →
    {entry : SourceProgram.Config Player L Γ} → {excluded : Finset Player} →
    {finished : SourceProgram.Config Player L Δ} → {after : Finset Player} →
    block.Attempt entry excluded finished after →
    (suffix : SourceProgram Player L Δ P) →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix) →
    EventGraphRuntime.State (serviceGraph setup .concurrent) → Prop
  | _, _, _, _, _, _, _, _, _, .nil _ _, _, _, _ => True
  | _, _, _, _, _, _, _, _, _,
      .active (owner := owner) (payload := payload) (rest := rest) _ choice missed _ later,
      suffix, embedding, native =>
      let event := embedding.event ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let tail := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let shape : (serviceGraph setup .concurrent).outputLayout event =
          .binding owner payload := by
        change outputLayout setup.program event = _
        simpa only [event, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.layout_eq ⟨0, by
            simp only [SourceProgram.CommitPrefix.prepend, eventCount]
            omega⟩
      (native.accepted (.inr event)).elim PublicationResult.failure
          (fun handle => native.bindingResult handle payload) = choice ∧
        (native.accepted (.inr event)).isNone = missed ∧
          (⟨.inr event, shape⟩ : FieldRef (serviceGraph setup .concurrent).layout
            (.binding owner payload)).get? native.config.store = some choice ∧
          sourceAttemptTableReads later suffix tail native
  | _, _, _, _, _, _, _, _, _,
      .excluded (owner := owner) (payload := payload) (rest := rest) _ later,
      suffix, embedding, native =>
      let event := embedding.event ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let shape : (serviceGraph setup .concurrent).outputLayout event =
          .binding owner payload := by
        change outputLayout setup.program event = _
        simpa only [event, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.layout_eq ⟨0, by
            simp only [SourceProgram.CommitPrefix.prepend, eventCount]
            omega⟩
      (⟨.inr event, shape⟩ : FieldRef (serviceGraph setup .concurrent).layout
        (.binding owner payload)).get? native.config.store = some .failure ∧
        sourceAttemptTableReads later suffix
          (embedding.tail (rest.prepend suffix) (by
            simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)) native

omit [Fintype Player] in
/-- All four source row clauses identify the literal raw final Config, with
its state, registry, revelations and target history, before any close. -/
theorem decodeCommitAttempt_eq_of_target_rows
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {block : SourceProgram.CommitPrefix Γ O Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (native : EventGraphRuntime.State (serviceGraph setup .concurrent)),
      sourceAttemptTableReads setup attempt suffix embedding native →
      decodeCommitAttempt setup.program .concurrent block suffix embedding native entry excluded =
        ⟨finished, after, attempt⟩ := by
  induction attempt with
  | nil => intro suffix embedding native reads; rfl
  | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      active choice missed missing later ih =>
      intro suffix embedding native reads
      obtain ⟨choiceEq, missedEq, _stored, tailReads⟩ := reads
      subst choice
      subst missed
      dsimp only [decodeCommitAttempt]
      rw [dite_eq_right active]
      erw [ih suffix _ native tailReads]
      rfl
  | @excluded Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      inactive later ih =>
      intro suffix embedding native reads
      dsimp only [decodeCommitAttempt]
      rw [dite_eq_left inactive]
      rw [ih suffix _ native reads.2]

omit [Fintype Player] in
/-- The same target-row recursion gives raw drained typed agreement. It uses
only the individual binding reads, without asserting a native invariant or a
supported trace for the assigned snapshot. -/
theorem target_attempt_state_agrees
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {block : SourceProgram.CommitPrefix Γ O Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (native : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (refs : ContextRefs (graphLayout setup.program) Γ),
      refs.Agrees entry.state native.config.store →
      sourceAttemptTableReads setup attempt suffix embedding native →
      (commitBlockRefs setup.program block suffix embedding refs).Agrees
        finished.state native.config.store := by
  induction attempt with
  | nil => intro suffix embedding native refs agree reads; exact agree
  | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      active choice missed missing later ih =>
      intro suffix embedding native refs agree reads
      obtain ⟨_choiceEq, _missedEq, stored, tailReads⟩ := reads
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event zero) =
          .binding owner payload := by
        change outputLayout setup.program (embedding.event zero) = _
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.layout_eq zero
      let head : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload) :=
        ⟨.inr (embedding.event zero), shape⟩
      let tail := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have nextAgree : (refs.cons head).Agrees
          (commitSuccessor name guard entry choice).state native.config.store :=
        ContextRefs.Agrees.cons refs entry.state native.config.store agree
          (name := name) (cell := .commitment owner payload) head choice stored
      intro readName readCell source
      exact ih suffix tail native (refs.cons head) nextAgree tailReads source
  | @excluded Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      inactive later ih =>
      intro suffix embedding native refs agree reads
      obtain ⟨stored, tailReads⟩ := reads
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event zero) =
          .binding owner payload := by
        change outputLayout setup.program (embedding.event zero) = _
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.layout_eq zero
      let head : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload) :=
        ⟨.inr (embedding.event zero), shape⟩
      let tail := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have nextAgree : (refs.cons head).Agrees
          (automaticCommit name owner payload entry).state native.config.store :=
        ContextRefs.Agrees.cons refs entry.state native.config.store agree
          (name := name) (cell := .commitment owner payload) head
          PublicationResult.failure stored
      intro readName readCell source
      exact ih suffix tail native (refs.cons head) nextAgree tailReads source

omit [Fintype Player] in
/-- The assigned accepted proper handle has its target typed result. No
supported assigned trace or source guard invariance is used in this equation. -/
theorem assigned_binding_result
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (handle : Handle (serviceGraph setup .concurrent)) (payload : L.Ty)
    (old next : L.Val payload)
    (stored : snapshot.candidates.lookup handle = .openable (⟨payload, old⟩ : Raw L))
    (registered : reference.execution.application.current.native.candidates.lookup handle =
      .openable (⟨payload, old⟩ : Raw L))
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L)) :
    (sourceSnapshotState setup implementation target reference lost snapshot).bindingResult
      handle payload = .success next := by
  classical
  have pair : sourceHandlePairs setup implementation target reference lost handle =
      some ((⟨payload, old⟩ : Raw L), (⟨payload, next⟩ : Raw L)) := by
    simp only [sourceHandlePairs, registered, meaning, Option.orElse_some, Option.map_some]
  unfold sourceSnapshotState
  rw [State.swap_bindingResult]
  simp only [HiddenSwap.ofPairs, stored, swapCandidate_openable, pair,
    EventGraph.pairSwap, Equiv.swap_apply_left, candidateResult, Raw.as?, ↓reduceDIte,
    cast_eq, Option.elim_some]

omit [Fintype Player] in
/-- A focal accepted BAD retains failure, including a wrong-typed physical
candidate. Its absent handle pair is stronger than preserving raw payload type. -/
theorem assigned_failed_binding_result
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (handle : Handle (serviceGraph setup .concurrent)) (payload : L.Ty)
    (failed : snapshot.bindingResult handle payload = .failure)
    (unchanged : sourceHandlePairs setup implementation target reference lost handle = none) :
    (sourceSnapshotState setup implementation target reference lost snapshot).bindingResult
      handle payload = .failure := by
  unfold sourceSnapshotState
  rw [State.swap_bindingResult]
  change candidateResult (swapCandidate
    (EventGraph.pairSwap (sourceHandlePairs setup implementation target reference lost handle))
      (snapshot.candidates.lookup handle)) payload = .failure
  rw [unchanged]
  have identity : swapCandidate (EventGraph.pairSwap (none : Option (Raw L × Raw L)))
      (snapshot.candidates.lookup handle) = snapshot.candidates.lookup handle := by
    cases snapshot.candidates.lookup handle <;> rfl
  rw [identity, ← State.bindingResult_eq]
  exact failed

omit [Fintype Player] in
/-- An assigned successful output field has the same accepted origin and
the corresponding target value. This is a field equation on the assigned
snapshot and requires no reconstructed native trace. -/
private theorem assigned_binding_store
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent)) (old next : L.Val payload)
    (stored : snapshot.config.store (.inr event) =
      some (cast (congrArg EventField.Value binding.symm) (.success old)))
    (accepted : snapshot.accepted (.inr event) = some handle)
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L)) :
    (sourceSnapshotState setup implementation target reference lost snapshot).config.store
      (.inr event) = some (cast (congrArg EventField.Value binding.symm) (.success next)) := by
  classical
  have paired : sourceSnapshotPair setup implementation target reference lost snapshot
      (.inr event) = some
        (cast (congrArg EventField.Value binding.symm) (.success old),
          cast (congrArg EventField.Value binding.symm) (.success next)) := by
    cases descriptor : nodeView (serviceGraph setup .concurrent) event with
    | bind actualOwner actualPayload shape code =>
        obtain ⟨ownerEq, payloadEq⟩ := EventField.binding.inj (shape.symm.trans binding)
        subst actualOwner
        subst actualPayload
        exact sourceSnapshotPair_binding_value setup implementation target reference lost
          snapshot event owner payload binding code descriptor handle old next stored accepted
            meaning
    | resolve actualOwner actualPayload selected checks shape code =>
        cases shape.symm.trans binding
    | sample actualPayload law shape code =>
        cases shape.symm.trans binding
  unfold sourceSnapshotState
  rw [State.swap_config, Config.swap_store]
  change (snapshot.config.store (.inr event)).map
    (EventGraph.pairSwap (sourceSnapshotPair setup implementation target reference lost snapshot
      (.inr event))) = _
  rw [stored, paired]
  simp only [Option.map_some, EventGraph.pairSwap, Equiv.swap_apply_left]

omit [Fintype Player] in
/-- An assigned output failure remains failure. Restoring a saved field or
automatically filling a slot therefore needs no target proper-value witness. -/
theorem assigned_failed_binding_store
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (stored : snapshot.config.store (.inr event) =
      some (cast (congrArg EventField.Value binding.symm) .failure)) :
    (sourceSnapshotState setup implementation target reference lost snapshot).config.store
      (.inr event) = some (cast (congrArg EventField.Value binding.symm) .failure) := by
  unfold sourceSnapshotState
  rw [State.swap_config, Config.swap_store]
  change (snapshot.config.store (.inr event)).map
    ((ValueSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost snapshot)).value
        (.inr event)) = _
  rw [stored, Option.map_some]
  exact congrArg some (ValueSwap.ofPairs_expiryFixed
    (sourceSnapshotPairs setup implementation target reference lost snapshot) event
      owner payload binding)

omit [Fintype Player] in
/-- A field already shared by saved and current snapshots retains its literal
accepted origin and stored value throughout every automatic settle branch. -/
private theorem settle_retains_binding
    (field : (serviceGraph setup .concurrent).Field)
    (handle : Handle (serviceGraph setup .concurrent))
    (value : ((serviceGraph setup .concurrent).layout field).Value)
    (phases : List (RuntimePhase (serviceGraph setup .concurrent))) (generation : Nat)
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (savedAccepted : entry.native.accepted field = some handle)
    (currentAccepted : current.native.accepted field = some handle)
    (savedStored : entry.native.config.store field = some value)
    (currentStored : current.native.config.store field = some value) :
    let settled := PhaseRuntimeState.settle phases generation entry current retired
    settled.entry.native.accepted field = some handle ∧
      settled.current.native.accepted field = some handle ∧
      settled.entry.native.config.store field = some value ∧
      settled.current.native.config.store field = some value := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨savedAccepted, currentAccepted, savedStored, currentStored⟩
  | cons phase remaining ih =>
      have drainedAccepted : (phase.drain current).native.accepted field = some handle := by
        rw [(phase.drain_tables current).1]
        exact currentAccepted
      have drainedStored : (phase.drain current).native.config.store field = some value :=
        phase.drain_keepsStore current field value currentStored
      have rebuiltAccepted :
          (phase.drain (PhaseRuntimeState.restore entry (phase.drain current))).native.accepted
            field = some handle := by
        rw [(phase.drain_tables _).1]
        exact savedAccepted
      have rebuiltStored :
          (phase.drain (PhaseRuntimeState.restore entry (phase.drain current))).native.config.store
            field = some value :=
        phase.drain_keepsStore _ field value savedStored
      simp only [PhaseRuntimeState.settle]
      split
      · split
        · split
          · exact ⟨savedAccepted, rebuiltAccepted, savedStored, rebuiltStored⟩
          · exact ih _ _ _ _ rebuiltAccepted rebuiltAccepted rebuiltStored rebuiltStored
        · exact ih _ _ _ _ drainedAccepted drainedAccepted drainedStored drainedStored
      · exact ⟨savedAccepted, drainedAccepted, savedStored, drainedStored⟩

omit [Fintype Player] in
/-- A completed raw drained field is either archived literally on a dirty
exit, or copied with its accepted handle into the actual next saved snapshot.
Subsequent automatic phases preserve the clean copy. -/
theorem completed_binding_retained
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent))) (generation : Nat)
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (finished : phase.Finished (phase.drain current))
    (field : (serviceGraph setup .concurrent).Field)
    (handle : Handle (serviceGraph setup .concurrent))
    (value : ((serviceGraph setup .concurrent).layout field).Value)
    (accepted : (phase.drain current).native.accepted field = some handle)
    (stored : (phase.drain current).native.config.store field = some value) :
    let settled := PhaseRuntimeState.settle (phase :: remaining) generation entry current retired
    (∃ record ∈ settled.retired, record.state = (phase.drain current).native) ∨
      (settled.entry.native.accepted field = some handle ∧
        settled.entry.native.config.store field = some value) := by
  classical
  dsimp only
  by_cases dirty : phase.kind = .commitment ∧
      (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty
  · left
    let record : RetiredCommitAttempt (serviceGraph setup .concurrent) :=
      ⟨⟨phase.low, generation⟩, (phase.drain current).native⟩
    refine ⟨record, ?_, rfl⟩
    by_cases survives : (phase.owners \ (phase.drain current).excluded).Nonempty
    · rw [PhaseRuntimeState.settle_retry phase remaining generation entry current retired
        finished dirty.1 dirty.2 survives]
      exact List.mem_append_right _ (List.mem_singleton_self record)
    · rw [PhaseRuntimeState.settle_exhausted phase remaining generation entry current retired
        finished dirty.1 dirty.2 survives]
      exact (PhaseRuntimeState.settle_archive _ _ _ _ _).subset
        (List.mem_append_right _ (List.mem_singleton_self record))
  · right
    rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
      finished dirty]
    have kept := settle_retains_binding setup field handle value remaining generation
      (phase.drain current) (phase.drain current) retired accepted accepted stored stored
    exact ⟨kept.1, kept.2.2.1⟩

/-- The actual accepted-origin producer supplies the complete assigned typed
read at every retained successful binding, including accepted canceled rows. -/
theorem assigned_accepted_binding_read
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (good : setup.proposalRecoveryForeignGood who g)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (G : setup.proposalRecoveryProtocol.History)
    (supported : G ∈ (sourceForcedBlock setup values who g choice).support)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : (nativeApplication).Control)
    (prior : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before))
    (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (owner : Player) (payload : L.Ty) (named : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent)) (old : L.Val payload)
    (accepted : snapshot.accepted (.inr named) = some handle)
    (stored : (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)).get? snapshot.config.store = some (.success old)) :
    ∃ next : L.Val payload,
      sourceHandleMeaning setup implementation G reference handle = some ⟨payload, next⟩ ∧
      (sourceSnapshotState setup implementation G reference lost snapshot).config.store
        (.inr named) = some (cast (congrArg EventField.Value binding.symm) (.success next)) ∧
      (sourceSnapshotState setup implementation G reference lost snapshot).bindingResult
        handle payload = .success next ∧ (owner = who → next = old) := by
  classical
  have initialEq : nativeInitial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  obtain ⟨priorNative, traceNative, retainedNative⟩ :
      ∃ (first : (nativeProtocol).Trace (some before))
        (last : (nativeProtocol).Trace (some reference)), TracePrefix first last := by
    rw [initialEq]
    exact ⟨prior, trace, retained⟩
  obtain ⟨valid, _catalogue⟩ := accepted_snapshot_catalogue setup implementation reference
    traceNative before priorNative retainedNative snapshot selected owner payload
      ⟨.inr named, binding⟩ handle accepted
  obtain ⟨other, associated, _owned, prepared⟩ := valid.success_provenance
    (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)) old stored
  have handleEq : other = handle := Option.some.inj (associated.symm.trans accepted)
  subst other
  obtain ⟨next, registered, meaning, own⟩ := sourceHandleMeaning_of_accepted_binding setup
    values implementation operational reference trace who event cut g sameInfo good choice
      properChoice G supported before prior retained snapshot selected owner payload named
        binding handle old accepted stored
  have rawStored : snapshot.config.store (.inr named) =
      some (cast (congrArg EventField.Value binding.symm) (.success old)) := by
    have castSome {α β : Type} (typeEq : α = β) (item : α) :
        cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
      cases typeEq
      rfl
    have uncast := congrArg
      (cast (congrArg (fun kind : EventField Player L => Option kind.Value) binding.symm)) stored
    change cast (congrArg Option (congrArg EventField.Value binding.symm))
      (cast (congrArg Option (congrArg EventField.Value binding))
        (snapshot.config.store (.inr named))) =
          cast (congrArg Option (congrArg EventField.Value binding.symm))
            (some (.success old)) at uncast
    have rawEq : snapshot.config.store (.inr named) =
        cast (congrArg Option (congrArg EventField.Value binding.symm))
          (some (.success old)) := by
      simpa only [cast_cast, cast_eq] using uncast
    exact rawEq.trans (castSome (congrArg EventField.Value binding.symm) (.success old))
  exact ⟨next, meaning,
    assigned_binding_store setup implementation G reference lost snapshot named owner payload
      binding handle old next rawStored accepted meaning,
    assigned_binding_result setup implementation G reference lost snapshot handle payload old
      next prepared registered meaning,
    own⟩

/-- A transient completed image obtains its accepted origin from the actual
next saved or retired snapshot. Its assigned field is then read on the raw
image itself, with no claim that the raw image was an actual trace endpoint. -/
theorem assigned_completed_binding_read
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (good : setup.proposalRecoveryForeignGood who g)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (G : setup.proposalRecoveryProtocol.History)
    (supported : G ∈ (sourceForcedBlock setup values who g choice).support)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (after : (nativeApplication).Control)
    (afterTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some after))
    (afterRetained : TracePrefix afterTrace trace)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent))) (generation : Nat)
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (finished : phase.Finished (phase.drain current))
    (normalized : after.execution.application =
      PhaseRuntimeState.settle (phase :: remaining) generation entry current retired)
    (valid : (phase.drain current).native.BindingInvariant)
    (owner : Player) (payload : L.Ty) (named : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent)) (old : L.Val payload)
    (accepted : (phase.drain current).native.accepted (.inr named) = some handle)
    (stored : (phase.drain current).native.config.store (.inr named) =
      some (cast (congrArg EventField.Value binding.symm) (.success old))) :
    ∃ next : L.Val payload,
      sourceHandleMeaning setup implementation G reference handle = some ⟨payload, next⟩ ∧
      (sourceSnapshotState setup implementation G reference lost
        (phase.drain current).native).config.store (.inr named) =
          some (cast (congrArg EventField.Value binding.symm) (.success next)) ∧
      (sourceSnapshotState setup implementation G reference lost
        (phase.drain current).native).bindingResult handle payload = .success next ∧
      (owner = who → next = old) := by
  classical
  have retainedField := completed_binding_retained setup phase remaining generation entry
    current retired finished (.inr named) handle
      (cast (congrArg EventField.Value binding.symm) (.success old)) accepted stored
  dsimp only at retainedField
  rw [← normalized] at retainedField
  obtain ⟨snapshot, selected, actualAccepted, actualStored⟩ :
      ∃ snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent),
        (snapshot = after.execution.application.current.native ∨
          snapshot = after.execution.application.entry.native ∨
          ∃ record ∈ after.execution.application.retired, snapshot = record.state) ∧
        snapshot.accepted (.inr named) = some handle ∧
        snapshot.config.store (.inr named) =
          some (cast (congrArg EventField.Value binding.symm) (.success old)) := by
    rcases retainedField with ⟨record, member, image⟩ | ⟨associated, saved⟩
    · exact ⟨(phase.drain current).native, Or.inr (Or.inr ⟨record, member, image.symm⟩),
        accepted, stored⟩
    · exact ⟨after.execution.application.entry.native, Or.inr (Or.inl rfl), associated, saved⟩
  have typedRead (state : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (read : state.config.store (.inr named) =
        some (cast (congrArg EventField.Value binding.symm) (.success old))) :
      (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
        (.binding owner payload)).get? state.config.store = some (.success old) := by
    have castSome {α β : Type} (typeEq : α = β) (item : α) :
        cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
      cases typeEq
      rfl
    have castInverse {α β : Type} (typeEq : α = β) (item : β) :
        cast typeEq (cast typeEq.symm item) = item := by
      cases typeEq
      rfl
    unfold FieldRef.get?
    rw [read]
    change cast (congrArg Option (congrArg EventField.Value binding))
      (some (cast (congrArg EventField.Value binding.symm) (.success old))) = _
    exact (castSome (congrArg EventField.Value binding)
      (cast (congrArg EventField.Value binding.symm) (.success old))).trans
        (congrArg some (castInverse (congrArg EventField.Value binding) (.success old)))
  obtain ⟨next, registered, meaning, own⟩ := sourceHandleMeaning_of_accepted_binding setup
    values implementation operational reference trace who event cut g sameInfo good choice
      properChoice G supported after afterTrace afterRetained snapshot selected owner payload
        named binding handle old actualAccepted (typedRead snapshot actualStored)
  obtain ⟨candidate, associated, _owned, prepared⟩ := valid.success_provenance
    (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)) old (typedRead _ stored)
  have candidateEq : candidate = handle := Option.some.inj (associated.symm.trans accepted)
  subst candidate
  exact ⟨next, meaning,
    assigned_binding_store setup implementation G reference lost (phase.drain current).native
      named owner payload binding handle old next stored accepted meaning,
    assigned_binding_result setup implementation G reference lost (phase.drain current).native
      handle payload old next prepared registered meaning,
    own⟩

/-- A completed source attempt reads the literal value of each signed issued
binding, including a native packet that is still pending. -/
theorem sourceBindingAt_of_issued_attempt
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (finished : SourceProgram.Config Player L Δ) (after : Finset Player)
    (attempt : block.Attempt entry excluded finished after) (same : after = excluded)
    (owner : Player) (active : owner ∉ excluded)
    (index : Fin (eventCount (block.prepend suffix))) (inside : index.val < block.length)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
      .binding owner payload) (value : PublicationResult (L.Val payload))
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (low high : Nat)
    (ledger : issuedLedger setup implementation block low control high owner (finished.view owner))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : message ∈ (nativeApplication).outputs (control.execution.recall owner))
    (currentAttempt : message.payload.attempt = control.execution.application.attempt)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment (embedding.event index) handle)
    (rank : (embedding.event index).val = low + index.val)
    (upper : (embedding.event index).val < high)
    (result : control.execution.application.current.native.bindingResult handle payload =
      value)
    (start : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some start))
    (committing : ProtocolState.atCommit setup.program start.point = true)
    (final : setup.proposalRecoveryProtocol.History) (retained : TracePrefix prior final.trace)
    (instructions : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      attempt.joints.reverse ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior))
    (coordinate : CommitAttemptId) (generation : start.generation = coordinate.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program start.saved = coordinate.phase)
    (position : (embedding.event index).val = instructionCount setup.program -
      ProtocolState.remaining setup.program start.point + index.val)
    (within : (embedding.event index).val < instructionCount setup.program -
      ProtocolState.commitEnd setup.program start.saved) :
    sourceBindingAt setup coordinate (embedding.event index) owner payload binding final.trace =
      PublicationResult.equivOption value := by
  have slots : index.val < attempt.joints.length := by
    simpa only [attempt.joints_length] using inside
  obtain ⟨current, next, row, joint, legal, moved, kept, _depth, semantic,
      rowSaved, rowGeneration, rowPosition⟩ :=
    source_commit_chunk_at_rank setup start prior committing final retained attempt.joints
      instructions index.val slots (embedding.event index).val position within
  have actual : (joint owner).map (·.semantic) =
      CommitRecoveryMove.lift (block.wordAction owner index.val (finished.view owner)) := by
    have own := congrFun semantic owner
    have word := congrArg (fun joints => (joints[index.val]?).map (fun row => row owner))
      (commitAttempt_wordAction block suffix entry excluded finished after attempt same)
    have selected : attempt.joints[index.val] owner =
        CommitRecoveryMove.lift (block.wordAction owner index.val (finished.view owner)) := by
      simpa [List.getElem?_eq_getElem, slots, inside, active] using word
    exact own.trans selected
  have slot : (embedding.event index).val - low = index.val := by omega
  have first := ((issuedLedger_iff_binding_results setup implementation block low control trace
    high owner (finished.view owner)).mp ledger) (embedding.event index) payload binding handle
      message emitted currentAttempt call ⟨by omega, upper⟩
  rw [slot, result] at first
  rw [← actual] at first
  have noMiss : ((joint owner).map (·.semantic)).elim false (·.missing) = false := by
    rw [actual]
    cases block.wordAction owner index.val (finished.view owner) <;> rfl
  have data : phaseRecoveryBindingData setup .concurrent (embedding.event index) owner payload
      binding ((joint owner).map (·.semantic)) = (value, false) := by
    unfold phaseRecoveryBindingData at first ⊢
    simp only [noMiss, Bool.false_eq_true, ite_false] at first ⊢
    exact Prod.ext first rfl
  have atFinal := sourceBindingAt_of_origin setup coordinate (embedding.event index) owner
    payload binding
    current row joint legal (some next) moved (rowGeneration.trans generation)
      (by rw [rowSaved]; exact saved) rowPosition (value, false) data final.trace kept
  cases value <;> exact atFinal

end Vegas.PhaseProposalQualifiedBinding

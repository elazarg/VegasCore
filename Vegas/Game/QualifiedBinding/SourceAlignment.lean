/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.SourceQueryTransport
import Vegas.Pending.PhaseProposalLostBinding
import Vegas.Pending.PhaseSwapInformation

/-! # Simultaneous source alignment for literal native replay -/

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
/-- A publication-only source interval reads its next proposal from the
same old commitment cells, including proposals rejected by publication guards. -/
private theorem sourceReplayRevealProposalRead :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (_prefixed : RevealPrefix program (count + 1))
      (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
      (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
      (before : ContextRefsBefore refs embedding) (offset : Nat)
      (_compiled : CompiledSuffix setup.program program refs revelations registry embedding
        before offset)
      (lift : ProtocolState program → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program program lift)
      (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) (generation : Nat)
      (last : CommitRecoveryState setup.program)
      (joints : List (Player → Option (CommitRecoveryMove Player L)))
      (addresses : List (Option Nat × (Finset Player × Nat × Nat)))
      (image : EventGraphRuntime.State (serviceGraph setup .concurrent)),
      (∀ {owner : Player} {payload : L.Ty} {name : VarId}
        (member : HasVar Γ name (.commitment owner payload)),
        (refs.get member).get? image.config.store = some (entry.state.get member)) →
      CommitRecoveryState.InstructionPath setup.program
        (setup.initialConfig setup.initialLaw.support_nonempty.choose) joints addresses
        (CommitRecoveryState.atPoint (lift (ProtocolState.entry program entry))
          excluded generation) last →
      joints.length = count →
      ∀ (joint : Player → Option (ProposalRecoveryMove Player L)) (raw : Sigma L.Val),
        (ProtocolState.recoveryProposal setup.program last.point joint).map Prod.snd = some raw →
        nativeStoredProposal? image (offset + count) = some raw := by
  intro count
  induction count with
  | zero =>
      intro Γ O program prefixed refs revelations registry embedding before offset compiled lift
        origin entry excluded generation last joints addresses image agrees path length joint raw
        proposed
      have empty : joints = [] := List.length_eq_zero_iff.mp length
      subst joints
      cases path with
      | refl =>
        have proposal : (ProtocolState.recoveryProposal program
            (ProtocolState.entry program entry) joint).map Prod.snd = some raw :=
          (origin.recoveryProposal_value_lift (ProtocolState.entry program entry) joint).symm.trans
            proposed
        cases program with
        | ret => exact prefixed.elim
        | sample => exact prefixed.elim
        | commit => exact prefixed.elim
        | @reveal Γ O published owner name payload fresh source unresolved next =>
          let zero : Fin (eventCount (.reveal published owner name fresh source unresolved next)) :=
            ⟨0, by simp only [eventCount]; omega⟩
          let event := embedding.event zero
          have rank : event.val = offset := by
            rw [compiled.rankEq]
            rfl
          have output : (serviceGraph setup .concurrent).outputLayout event =
              .publication payload := (embedding.layout_eq zero).trans rfl
          have code : cast (congrArg (EventCode (graphLayout setup.program)) output)
              ((serviceGraph setup .concurrent).nodes event) =
                .resolve owner payload (refs.get source)
                  (compileChecks (published := published) refs registry revelations source) := by
            simpa only [event, zero, EventGraph.withMode_nodes, Setup.eventGraph,
              compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
              using compiled.nodeEq zero
          have read := nativeStoredProposal?_resolve image event (refs.get source)
            (compileChecks (published := published) refs registry revelations source) output code
              (entry.state.get source) (agrees source)
          simp only [ProtocolState.entry, ProtocolState.recoveryProposal, Sum.elim_inl] at proposal
          split at proposal
          · cases stored : entry.state.get source with
            | failure => simp only [stored, Option.map_none] at proposal; cases proposal
            | success value =>
                simp only [stored, Option.map_some] at proposal
                rw [rank, stored] at read
                simpa only [Nat.add_zero, bindingProposalValue?] using
                  read.trans (congrArg some (Option.some.inj proposal))
          · cases proposal
  | succ count ih =>
      intro Γ O program prefixed refs revelations registry embedding before offset compiled lift
        origin entry excluded generation last joints addresses image agrees path length joint raw
        proposed
      cases program with
      | ret => exact prefixed.elim
      | sample => exact prefixed.elim
      | commit => exact prefixed.elim
      | @reveal Γ O published owner name payload fresh source unresolved next =>
        cases path with
        | refl => simp only [List.length_nil] at length; omega
        | @step first middle last current rest addresses legal supported later =>
          let result := revealSuccessor published source entry
            (if owner ∈ excluded then false else
              OwnAction.disclosure ((current owner).map (·.action)))
          let kept := if owner ∈ excluded then { result with history := entry.history } else result
          let after := match result.state.get .here with
            | .failure => insert owner excluded
            | .success _ => excluded
          have notCommit : ProtocolState.atCommit setup.program
              (lift (ProtocolState.entry _ entry)) = false := by
            rw [origin.atCommit_lift]
            rfl
          obtain ⟨step, rawSupport, middleEq⟩ :=
            (CommitRecoveryState.atPoint (lift (ProtocolState.entry _ entry))
              excluded generation).step_noncommit_atPoint
                (CommitRecoveryState.atPoint_blockFrontier _ _ _)
                notCommit current middle supported
          have kernel : ProtocolState.recoveryStep
              (.reveal published owner name fresh source unresolved next)
              (ProtocolState.entry _ entry) excluded current =
                PMF.pure ((Sum.inr (ProtocolState.entry next kept) : ProtocolState _), after) := rfl
          change step ∈ (ProtocolState.recoveryStep setup.program
            (lift (ProtocolState.entry _ entry)) excluded current).support at rawSupport
          rw [origin.recoveryStep_lift, kernel, PMF.pure_map,
            PMF.mem_support_pure_iff] at rawSupport
          have middleAtPoint : middle = CommitRecoveryState.atPoint
              (lift (.inr (ProtocolState.entry next kept))) after generation := by
            rw [middleEq, rawSupport]
            rfl
          rw [middleAtPoint] at later
          have tailCompiled := compiled.revealTail setup.program fresh source unresolved next refs
            revelations registry embedding before offset
          have tailAgrees : ∀ {other : Player} {domain : L.Ty} {cellName : VarId}
              (member : HasVar ((published, .publication payload) :: Γ) cellName
                (.commitment other domain)),
              ((refs.cons (name := published) ⟨.inr (embedding.event
                ⟨0, by simp only [eventCount]; omega⟩), reveal_head_layout embedding⟩).get
                  member).get? image.config.store = some (kept.state.get member) := by
            intro other domain cellName member
            cases member with
            | there member =>
                have original := agrees member
                dsimp only [kept, result]
                split_ifs <;> exact original
          have read := ih next prefixed _ _ registry.weaken _ _ (offset + 1) tailCompiled
            (fun point => lift (.inr point)) (origin.revealTail fresh source unresolved next)
              kept after generation last rest addresses image tailAgrees later
                (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using length)
                  joint raw proposed
          simpa only [Nat.add_assoc, Nat.add_comm 1 count] using read

/-- A remembered focal commitment has an actual accepted snapshot before a
later unsent request, including a snapshot retained by a canceled attempt. -/
private theorem sourceReplayFocalEmissionSnapshot
    (_operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (who : Player) (requested : (serviceGraph setup .concurrent).EventId)
    (requestedPayload : L.Ty)
    (requestedBinding : (serviceGraph setup .concurrent).outputLayout requested =
      .binding who requestedPayload)
    (request : reference.execution.application.SeedRequest who
      ⟨reference.execution.application.attempt, requested⟩)
    (unsent : ∀ message ∈ (nativeApplication).outputs (reference.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨reference.execution.application.attempt, requested⟩)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (input : message ∈ reference.execution.network.inputs)
    (named : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding who payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle) :
    ∃ (before : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before))
      (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent)),
      TracePrefix prior referenceTrace ∧
      (snapshot = before.execution.application.current.native ∨
        snapshot = before.execution.application.entry.native ∨
        ∃ record ∈ before.execution.application.retired, snapshot = record.state) ∧
      snapshot.accepted (.inr named) = some handle := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq : nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
  obtain ⟨serial, opening, evidence, record, handleEq, _sender, recorded, _emitted,
    declared, _fresh, emissionAttempt, _meaning⟩ :=
    issued_binding_record setup implementation reference referenceTrace who named payload binding
      handle message input call
  let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment named (who, .prepared serial), opening⟩, evidence⟩
  have transmitted : record.action.transmission = some material := by rw [declared]
  have materialCall : material.call.packet = .commitment named handle := by rw [handleEq]
  obtain ⟨callback, callbackTrace, callbackKept, _acting, viewed, callbackRequest⟩ :=
    phase_recorded_binding_request implementation.runtime implementation.leaks
      implementation.bounds implementation.plan inputs implementation.horizon
        (serviceGraph_revealRelaxedOrdered setup .concurrent) implementation.scheduler
          (initialEq ▸ referenceTrace) who record recorded material transmitted named handle
            materialCall
  let callbackNativeTrace : (nativeProtocol).Trace (some callback) := initialEq.symm ▸ callbackTrace
  have callbackNativeKept : TracePrefix callbackNativeTrace referenceTrace := by
    have transportPrefix {first second : PMF (nativeApplication).State}
        (same : first = second) {left right : (nativeProtocol).State}
        (earlier : ((nativeMenu).protocol first implementation.horizon
          implementation.scheduler).Trace left)
        (later : ((nativeMenu).protocol second implementation.horizon
          implementation.scheduler).Trace right)
        (kept : TracePrefix earlier (same.symm ▸ later)) :
        TracePrefix (same ▸ earlier) later := by
      cases same
      exact kept
    exact transportPrefix initialEq.symm callbackTrace referenceTrace callbackKept
  have callbackOrdered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history nativeInitial implementation.horizon implementation.scheduler
      initialized ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler callbackNativeTrace)
  obtain ⟨phase, phaseInstalled, inside⟩ := callbackRequest.2.1
  have callbackNamespace : callback.execution.application.attempt = message.payload.attempt := by
    rw [viewed] at emissionAttempt
    exact emissionAttempt
  by_cases currentAttempt : message.payload.attempt = reference.execution.application.attempt
  · have same : callback.execution.application.attempt = reference.execution.application.attempt :=
      callbackNamespace.trans currentAttempt
    have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
      (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
        callback reference callbackNativeTrace referenceTrace
          callbackNativeKept callbackOrdered same
    have phaseAtReference : phase ∈ reference.execution.application.phases.head? := by
      have phases := congrArg Prod.fst metadata
      change callback.execution.application.phases =
        reference.execution.application.phases at phases
      exact phases ▸ phaseInstalled
    have lower : reference.execution.application.attempt.phase ≤ named.val := by
      have low : callback.execution.application.attempt.phase = phase.low := by
        simp only [PhaseRuntimeState.attempt, Option.mem_def.mp phaseInstalled,
          Option.map_some, Option.getD_some]
      rw [← same, low]
      exact ((phase.mem_events named).mp inside).1
    have earlier := phase_recorded_binding_rank_lt_of_unsent_request implementation.runtime
      implementation.leaks implementation.bounds implementation.plan inputs implementation.horizon
        (serviceGraph_revealRelaxedOrdered setup .concurrent) implementation.scheduler
          (initialEq ▸ referenceTrace) who record recorded material transmitted named handle
            materialCall (emissionAttempt.trans currentAttempt) requested request unsent
    have dependency := (serviceGraph_revealRelaxedOrdered setup .concurrent).keeps
      (barrierOrder_same_owner (serviceGraph setup .concurrent).outputLayout earlier (by
        rw [binding, requestedBinding]
        rfl))
      (Or.inl (by simp only [binding, EventField.IsPublication, not_false_eq_true]))
    have completed := request.2.2.1.2 dependency
    have accepted := PhaseCount.completed_recorded_binding_accepted implementation.runtime
      implementation.leaks implementation.bounds implementation.plan inputs implementation.horizon
        implementation.scheduler (initialEq ▸ referenceTrace) who named payload binding lower
          completed request.2.2.2.2 record recorded material transmitted handle materialCall
            (emissionAttempt.trans currentAttempt)
    exact ⟨reference, referenceTrace, reference.execution.application.current.native,
      .refl, Or.inl rfl, accepted⟩
  · obtain ⟨source, target, prior, joint, legal, realized, initial, final, original, exited⟩ :=
      attempt_exit_of_prefix setup implementation callback callbackNativeTrace referenceTrace
        callbackNativeKept (by
          simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact fun equal => currentAttempt (callbackNamespace.symm.trans equal.symm))
    obtain ⟨before, sourceEq, attemptEq⟩ := Option.map_eq_some_iff.mp original
    cases sourceEq
    obtain ⟨after, rfl, _recalled⟩ := (nativeApplication).transition_recall_prefix nativeInitial
      implementation.horizon implementation.scheduler before target joint realized
    have same : callback.execution.application.attempt = before.execution.application.attempt :=
      attemptEq.symm
    have changed : after.execution.application.attempt ≠ before.execution.application.attempt := by
      simpa only [Option.map_some, attemptEq, ne_eq, Option.some.injEq] using exited
    have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
      (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
        callback before callbackNativeTrace prior initial callbackOrdered same
    have phaseBefore : phase ∈ before.execution.application.phases.head? := by
      have phases := congrArg Prod.fst metadata
      change callback.execution.application.phases = before.execution.application.phases at phases
      exact phases ▸ phaseInstalled
    obtain ⟨remaining, installed⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp phaseBefore)
    have rawPrior := (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler prior
    obtain ⟨physical, _idle, normalized, finished, valid, coverage, exclusions,
      _receipts, _effect, stamp⟩ := phase_closed_transition_receipt_snapshot implementation.runtime
        implementation.leaks implementation.plan inputs implementation.horizon
          implementation.scheduler before after (initialEq ▸ rawPrior) joint
            (by rw [← initialEq]; exact realized) phase phaseBefore changed
    have survivesPrefix : ∀ {state} {history : (nativeProtocol).Trace state},
        TracePrefix (prior.extend joint legal realized) history →
        ∃ next : (nativeApplication).Control, state = some next ∧
          (who ∉ next.execution.application.current.excluded →
            who ∉ after.execution.application.current.excluded) := by
      intro state history retained
      induction retained with
      | refl => exact ⟨after, rfl, fun surviving => surviving⟩
      | @extend source target earlier retained actions offered moved ih =>
          obtain ⟨middle, rfl, previous⟩ := ih
          obtain ⟨next, rfl, _⟩ := (nativeApplication).transition_recall_prefix nativeInitial
            implementation.horizon implementation.scheduler middle target actions moved
          exact ⟨next, rfl, fun surviving => previous (fun excluded => surviving
            ((phaseApplication_exclusion_monotone
              implementation.runtime implementation.leaks).transition nativeInitial
                implementation.horizon implementation.scheduler
                middle next actions moved excluded))⟩
    obtain ⟨sameReference, referenceEq, survives⟩ := survivesPrefix final
    cases Option.some.inj referenceEq
    have active : who ∉ (phase.drain physical).excluded := by
      rw [exclusions]
      exact survives request.2.2.2.2
    have present : (phase.drain physical).native.accepted (.inr named) ≠ none := by
      intro missing
      exact active (RecoveryState.excluded_of_finished_unaccepted_binding
        (phase.drain physical) phase finished coverage named inside who payload binding missing)
    obtain ⟨accepted, associated⟩ := Option.ne_none_iff_exists'.mp present
    have owned : accepted.1 = who := by
      obtain ⟨kind, shape⟩ := valid.accepted_typed (.inr named) accepted associated
      exact (EventField.binding.inj (shape.symm.trans binding)).1
    have lower : before.execution.application.attempt.phase ≤ named.val := by
      have low : before.execution.application.attempt.phase = phase.low := by
        simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
          Option.map_some, Option.getD_some]
      rw [low]
      exact ((phase.mem_events named).mp inside).1
    obtain earlier | ⟨originalMessage, originalOutput, originalSender, originalCall,
      originalAttempt⟩ := stamp named accepted associated
    · omega
    have outputAtReference : originalMessage ∈
        (nativeApplication).outputs (reference.execution.recall who) := by
      rw [owned] at originalOutput
      have recalls := (nativeApplication).reaches_recall_prefix nativeInitial
        implementation.horizon implementation.scheduler
          ((nativeMenu).reaches_raw nativeInitial implementation.horizon implementation.scheduler
            ((TracePrefix.extend .refl joint legal realized).trans final).reachesWithin)
              before reference rfl rfl who
      obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp originalOutput
      exact List.mem_filterMap.mpr ⟨entry, recalls.subset member, emitted⟩
    have inputRecall := (nativeApplication).history_inputRecall nativeInitial
      implementation.horizon implementation.scheduler
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler referenceTrace) who
    have originalInput : originalMessage ∈ reference.execution.network.inputs := by
      rw [← inputRecall] at outputAtReference
      exact (List.mem_filter.mp outputAtReference).1
    have clean := (PhaseCount.onePacketMenu_countClean implementation.runtime
      implementation.leaks implementation.bounds implementation.scheduler).history
        nativeInitial implementation.horizon
          (fun state _ => PhaseCount.countClean_initial implementation.runtime
            implementation.leaks state) referenceTrace
    have sameMessage : originalMessage = message := PhaseCount.Permits.eq_of_same_event
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 originalMessage originalInput))
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)) originalInput input
      (fun first firstInput second secondInput ids =>
        (nativeApplication).input_identifier_injective_history nativeInitial implementation.horizon
          implementation.scheduler reference
            ((nativeMenu).toRawTrace nativeInitial implementation.horizon
              implementation.scheduler referenceTrace) first second firstInput secondInput ids)
      ((originalSender.trans owned).trans _sender.symm) (by
        simp only [PhaseCount.event?, originalCall, call, Payload.event?, Option.map_some,
          originalAttempt, ← same, callbackNamespace])
    have acceptedEq : accepted = handle := by
      have packets := congrArg (fun sent : Message Player
        (CommitAttemptPacket (serviceGraph setup .concurrent)) => sent.payload.packet.call)
          sameMessage
      rw [originalCall, call] at packets
      exact (Payload.commitment.inj packets).2
    subst accepted
    have read := valid.binding_read (⟨.inr named, binding⟩ :
      FieldRef (serviceGraph setup .concurrent).layout (.binding who payload)) named rfl
        (finished inside)
    rw [associated, Option.elim_some] at read
    have literal : (phase.drain physical).native.config.store (.inr named) =
        some (cast (congrArg EventField.Value binding.symm)
          ((phase.drain physical).native.bindingResult handle payload)) := by
      have castRead := congrArg
        (cast (congrArg (fun kind : EventField Player L => Option kind.Value) binding.symm)) read
      have castSome {α β : Type} (equal : α = β) (value : α) :
          cast (congrArg Option equal) (some value) = some (cast equal value) := by
        cases equal
        rfl
      simp only [FieldRef.get?, cast_cast, cast_eq] at castRead
      change (phase.drain physical).native.config.store (.inr named) =
        cast (congrArg Option (congrArg EventField.Value binding.symm))
          (some ((phase.drain physical).native.bindingResult handle payload)) at castRead
      rw [castSome] at castRead
      exact castRead
    have retained := completed_binding_retained setup phase remaining
      before.execution.application.generation before.execution.application.entry physical
        before.execution.application.retired finished (.inr named) handle _ associated literal
    have normalizedEq : after.execution.application = PhaseRuntimeState.settle
        (phase :: remaining) before.execution.application.generation
          before.execution.application.entry physical before.execution.application.retired := by
      simpa only [PhaseRuntimeState.normalize, installed] using normalized
    rw [← normalizedEq] at retained
    rcases retained with ⟨archived, member, image⟩ | ⟨acceptedAfter, _storedAfter⟩
    · exact ⟨after, prior.extend joint legal realized, (phase.drain physical).native,
        final, Or.inr (Or.inr ⟨archived, member, image.symm⟩), associated⟩
    · exact ⟨after, prior.extend joint legal realized, after.execution.application.entry.native,
        final, Or.inr (Or.inl rfl), acceptedAfter⟩

theorem sourceReplayAlignment
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
      (implementation := implementation) operational who reference referenceTrace
        g targetCurrent targetTrace)
    (completedVisits : SourceReplayCompletedVisit (setup := setup)
      (implementation := implementation) operational who reference referenceTrace
        g targetCurrent targetTrace) :
    SourceReplayAlignment (setup := setup) (values := values)
      (implementation := implementation) operational who reference referenceTrace event
        (entry.canonicalCut setup values implementation operational fullValues reference
          referenceTrace who acting event payload clean foreign)
            g choice targetCurrent targetTrace := by
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
  refine {
    canonical := canonicalEq
    sameInfo := sameInfo
    cutGood := cutGood
    good := good
    properChoice := properChoice
    supported := supported
    selectedAgreement := selectedAgreement
    completedVisit := completedVisits
    initialized := ?_
    images := ?_
    proper := ?_ }
  · intro lost restricted
    exact sourceReplayInitialFromCut setup values implementation operational who reference
      referenceTrace event cut g sameInfo choice targetCurrent targetTrace supported lost
  · intro lost restricted before prior retained
    have selected := selectedAgreement lost restricted before prior retained
    let swap := HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation G reference lost
        before.execution.application.current.native)
      (sourceHandlePairs setup implementation G reference lost)
    have focalHandles : ∀ slot, swap.raw (who, slot) = id := by
      intro slot
      change pairSwap (sourceHandlePairs setup implementation G reference lost
        (who, slot)) = id
      cases registered : reference.execution.application.current.native.candidates.lookup
          (who, slot) with
      | fresh => simp [sourceHandlePairs, registered, pairSwap]
      | unopenable => simp [sourceHandlePairs, registered, pairSwap]
      | openable raw =>
          have lostNone : lost (who, slot) = none := by
            cases selectedValue : lost (who, slot) with
            | none => rfl
            | some value =>
                exact False.elim ((restricted (who, slot) value
                  selectedValue).1 rfl)
          cases meaning : sourceHandleMeaning setup implementation G reference
              (who, slot) with
          | none =>
              simp [sourceHandlePairs, registered, meaning, lostNone, pairSwap]
          | some next =>
              have unchanged : next = raw := by
                cases slot with
                | initial input =>
                    have nativeInitialCandidate :=
                      sourceReplayReferenceInitialCatalogue setup implementation
                        operational reference referenceTrace cut.theta
                          cut.thetaSupported cut.originalInputs
                    have read :
                        (EventGraphRuntime.State.initial
                          (graph := serviceGraph setup .concurrent)
                          (encodeInputs (ProtocolState.base setup.program
                            targetCurrent.point))).candidates.lookup (who, .initial input) =
                              .openable next := by
                      simp only [sourceHandleMeaning, G, Option.bind_some] at meaning
                      split at meaning <;> cases meaning
                      assumption
                    have typed (kind : EventField Player L) (value : kind.Value)
                        (opened : EventGraphRuntime.State.candidateOfValue who kind value =
                          .openable next) :
                        ∃ payload, kind = .binding who payload := by
                      cases kind with
                      | publicData | privateInput | publication => cases opened
                      | binding owner payload =>
                          by_cases own : owner = who
                          · subst owner
                            exact ⟨payload, rfl⟩
                          · simp only [EventGraphRuntime.State.candidateOfValue,
                              own, ↓reduceIte] at opened
                            cases opened
                    have initialRead := read
                    rw [EventGraphRuntime.State.initial_candidate] at initialRead
                    obtain ⟨payload, shape⟩ := typed _ _ initialRead
                    have visible :
                        (serviceGraph setup .concurrent).fieldVisibleTo who (.inl input) := by
                      change ((serviceGraph setup .concurrent).inputLayout input).VisibleTo who
                      rw [shape]
                      rfl
                    have sameInput := sourceReplayTargetVisibleInputs setup values
                      implementation who reference referenceTrace event cut g sameInfo
                        choice targetCurrent targetTrace supported input visible
                    have sameCandidate :
                        (EventGraphRuntime.State.initial
                          (graph := serviceGraph setup .concurrent)
                          (encodeInputs cut.theta)).candidates.lookup (who, .initial input) =
                        (EventGraphRuntime.State.initial
                          (graph := serviceGraph setup .concurrent)
                          (encodeInputs (ProtocolState.base setup.program
                            targetCurrent.point))).candidates.lookup (who, .initial input) := by
                      rw [EventGraphRuntime.State.initial_candidate,
                        EventGraphRuntime.State.initial_candidate]
                      change EventGraphRuntime.State.candidateOfValue who _
                        (encodeInputs cut.theta input) = _
                      rw [sameInput]
                      rfl
                    have sameRaw : CommitmentCandidate.openable raw = .openable next :=
                      registered.symm.trans
                        ((nativeInitialCandidate input who payload shape).trans
                          (sameCandidate.trans read))
                    exact (CommitmentCandidate.openable.inj sameRaw).symm
                | prepared serial =>
                    have found := meaning
                    change (reference.execution.recall who).findSome? _ = some next at found
                    obtain ⟨record, recorded, located⟩ := List.exists_of_findSome?_eq_some found
                    cases emitted : record.emitted with
                    | none => simp only [emitted, Option.bind_none] at located; cases located
                    | some message =>
                        simp only [emitted, Option.bind_some] at located
                        cases call : message.payload.packet.call with
                        | malformed => simp only [call] at located; cases located
                        | opening => simp only [call] at located; cases located
                        | commitment named handle =>
                            simp only [call] at located
                            split at located
                            · rename_i sameHandle
                              subst handle
                              split at located
                              · rename_i owner domain binding
                                have messageInput :
                                    message ∈ reference.execution.network.inputs := by
                                  have authored : message ∈ (nativeApplication).outputs
                                      (reference.execution.recall who) :=
                                    List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
                                  rw [← (nativeApplication).history_inputRecall nativeInitial
                                    implementation.horizon implementation.scheduler
                                      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                                        implementation.scheduler referenceTrace) who] at authored
                                  exact (List.mem_filter.mp authored).1
                                obtain ⟨_serial, _opening, _evidence, _record, handleEq, _sender,
                                  _recorded, _emitted, _declared, _fresh, _namespace, _result⟩ :=
                                  issued_binding_record setup implementation
                                    reference referenceTrace
                                    owner named domain binding (who, .prepared serial) message
                                      messageInput call
                                have own : owner = who := (congrArg Prod.fst handleEq).symm
                                have bindingWho :
                                    (serviceGraph setup .concurrent).outputLayout named =
                                      .binding who domain := by rw [binding, own]
                                obtain ⟨acceptedBefore, acceptedPrior, snapshot, acceptedKept,
                                  selectedSnapshot, accepted⟩ :=
                                  sourceReplayFocalEmissionSnapshot setup implementation operational
                                    reference referenceTrace who event payload clean.binding
                                      cut.request cut.unsent message messageInput
                                        named domain bindingWho
                                        (who, .prepared serial) call
                                obtain ⟨valid, catalogue⟩ := accepted_snapshot_catalogue setup
                                  implementation reference referenceTrace
                                    acceptedBefore acceptedPrior
                                    acceptedKept snapshot selectedSnapshot who domain
                                      ⟨.inr named, bindingWho⟩ (who, .prepared serial) accepted
                                cases result :
                                    reference.execution.application.current.native.bindingResult
                                      (who, .prepared serial) domain with
                                | failure =>
                                    have absent := sourceHandleMeaning_of_focal_failure setup values
                                      implementation operational reference
                                        (sourceCutTrace setup implementation referenceTrace)
                                          who event cut
                                        g sameInfo choice G supported acceptedBefore
                                        (sourceCutTrace setup implementation acceptedPrior)
                                        (by
                                          unfold sourceCutTrace
                                          exact tracePrefix_initializer setup implementation _
                                            acceptedKept) snapshot selectedSnapshot
                                            domain named bindingWho
                                            (who, .prepared serial) accepted result
                                    rw [meaning] at absent
                                    cases absent
                                | success old =>
                                    have opened : snapshot.candidates.lookup
                                        (who, .prepared serial) =
                                        .openable (⟨domain, old⟩ : Raw L) := by
                                      rw [← catalogue]
                                      exact (State.bindingResult_eq_success_iff _ _ _ _).mp result
                                    have stored := valid.toAssociationInvariant.opening_stored
                                      (⟨.inr named, bindingWho⟩ : FieldRef
                                        (serviceGraph setup .concurrent).layout
                                          (.binding who domain))
                                          (who, .prepared serial) old accepted opened
                                    obtain ⟨new, registeredTyped, targetMeaning, focal⟩ :=
                                      sourceHandleMeaning_of_accepted_binding setup values
                                        implementation operational reference
                                          (sourceCutTrace setup implementation referenceTrace)
                                            who event
                                          cut g sameInfo good choice properChoice G supported
                                            acceptedBefore
                                            (sourceCutTrace setup implementation acceptedPrior)
                                            (by
                                              unfold sourceCutTrace
                                              exact tracePrefix_initializer setup implementation _
                                                acceptedKept) snapshot
                                              selectedSnapshot who domain named bindingWho
                                                (who, .prepared serial) old accepted stored
                                    have nextEq : next = (⟨domain, new⟩ : Raw L) :=
                                      Option.some.inj (meaning.symm.trans targetMeaning)
                                    have rawEq : raw = (⟨domain, old⟩ : Raw L) :=
                                      CommitmentCandidate.openable.inj
                                        (registered.symm.trans registeredTyped)
                                    rw [nextEq, rawEq, focal rfl]
                              · cases located
                            · cases located
              subst next
              simp [sourceHandlePairs, registered, meaning, pairSwap]
    have openingFixed : ∀ (message : Message Player
        (CommitAttemptPacket (serviceGraph setup .concurrent)))
        (named : (serviceGraph setup .concurrent).EventId)
        (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L),
        before.execution.network.lookup message.id = some message →
        message.payload.packet.call = .opening named handle raw →
        (message.payload.tokenValid before.execution.application.attempt &&
          before.execution.application.allows message.payload.packet.call &&
          !before.execution.application.current.excludedCall message.payload.packet.call) = true →
        before.execution.application.current.native.config.cut.Ready named →
        RevealFixed swap before.execution.application.current.native named := by
      intro message named handle raw lookup packet admitted _ready
      have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
          (PhaseRuntimeState.initial implementation.plan) := by
        simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
      have rawPrior := (nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler prior
      have origins := (nativeApplication).history_provenance nativeInitial implementation.horizon
        implementation.scheduler rawPrior
      have recalls := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
        implementation.scheduler rawPrior
      have input := ((nativeApplication).retained_envelopes_mem_inputs before.execution origins
        recalls).lookup message.id message lookup
      have proposed : PhaseProposal.packetProposal? message.payload =
          some (⟨message.payload.attempt, named⟩, raw) := by
        simp only [PhaseProposal.packetProposal?, packet]
      have sameAttempt : message.payload.attempt = before.execution.application.attempt := by
        have token := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).1
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp token).1
      obtain ⟨callback, callbackTrace, owner, domain, binding, checks, output, code, value,
        _callbackKept, _sender, _acting, _request, node, typed, _callbackStored⟩ :=
        PhaseProposal.submitted_proposal_binding_meaning implementation.runtime
          implementation.leaks implementation.bounds implementation.plan
            (serviceGraph_revealRelaxedOrdered setup .concurrent)
              (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
                before (initialEq ▸ prior) message input
                  ⟨message.payload.attempt, named⟩ raw proposed
      obtain ⟨actual, actualRaw, stored⟩ :=
        PhaseProposal.submitted_proposal_current_binding_meaning implementation.runtime
          implementation.leaks implementation.bounds implementation.plan
            (serviceGraph_revealRelaxedOrdered setup .concurrent)
              (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
                before (initialEq ▸ prior) message input ⟨message.payload.attempt, named⟩ raw
                  proposed sameAttempt owner domain binding checks output code
      have valueEq : value = actual := by
        exact eq_of_heq (Raw.mk.inj (typed.symm.trans actualRaw)).2
      subst actual
      obtain ⟨phase, phaseInstalled, inside⟩ : ∃ phase,
          before.execution.application.phases.head? = some phase ∧ named ∈ phase.events := by
        have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2
        unfold PhaseRuntimeState.allows at allowed
        rw [packet] at allowed
        cases installed : before.execution.application.phases.head? with
        | none => simp only [installed] at allowed; cases allowed
        | some phase =>
            simp only [installed, Payload.event?] at allowed
            exact ⟨phase, rfl, of_decide_eq_true allowed⟩
      have kind : phase.kind = .reveal := by
        have fields := phase.fields named ((phase.mem_events named).mp inside).1
          ((phase.mem_events named).mp inside).2
        cases kind : phase.kind with
        | commitment =>
            rw [kind] at fields
            obtain ⟨other, sort, shape⟩ := fields
            cases shape.symm.trans output
        | sample =>
            rw [kind] at fields
            obtain ⟨sort, shape⟩ := fields
            cases shape.symm.trans output
        | reveal => rfl
      let checkpoint := (checkpointSelection setup implementation operational prior).val.checkpoint
      have low : phase.low = before.execution.application.attempt.phase := by
        simp only [PhaseRuntimeState.attempt, phaseInstalled, Option.map_some, Option.getD_some]
      let count := named.val - phase.low
      have sourcePrefix : RevealPrefix checkpoint.residual.tail (count + 1) := by
        apply RevealPrefix.of_outputLayout (count + 1) checkpoint.residual.tail
        · have bounded := phase.bounded
          have total := checkpoint.compiled.countEq
          change phase.high ≤ eventCount setup.program at bounded
          have within := (phase.mem_events named).mp inside
          change before.execution.application.attempt.phase +
            eventCount checkpoint.residual.tail = eventCount setup.program at total
          rw [← low] at total
          dsimp only [count]
          omega
        · intro index bounded
          have within := (phase.mem_events named).mp inside
          have fields := phase.fields (checkpoint.embedding.event index)
            (by rw [checkpoint.compiled.rankEq, ← low]; omega)
            (by rw [checkpoint.compiled.rankEq, ← low]; dsimp only [count] at bounded; omega)
          rw [kind] at fields
          obtain ⟨sort, publication⟩ := fields
          change outputLayout setup.program (checkpoint.embedding.event index) =
            .publication sort at publication
          rw [checkpoint.embedding.layout_eq] at publication
          rw [publication]
          trivial
      have atIndex : named = checkpoint.embedding.event
          ⟨count, by
                  have bound := sourcePrefix.le_eventCount
                  omega⟩ := by
        apply Fin.ext
        rw [checkpoint.compiled.rankEq, ← low]
        dsimp only [count]
        have within := (phase.mem_events named).mp inside
        omega
      obtain ⟨compiledOwner, compiledPayload, cellName, member, compiledChecks,
        compiledOutput, compiledCode⟩ := checkpoint.compiled.reveal_binding_origin_at setup
          (count + 1) checkpoint.residual.tail sourcePrefix checkpoint.refs
            checkpoint.source.revelations checkpoint.registry checkpoint.embedding checkpoint.before
              before.execution.application.attempt.phase
                ⟨count, by
                  have bound := sourcePrefix.le_eventCount
                  omega⟩ (by change count < count + 1; omega)
      obtain ⟨compiledOutput, compiledCode, compiledView⟩ :
          ∃ (output : (serviceGraph setup .concurrent).outputLayout named =
              .publication compiledPayload)
            (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
              ((serviceGraph setup .concurrent).nodes named) =
                .resolve compiledOwner compiledPayload (checkpoint.refs.get member) compiledChecks),
            nodeView (serviceGraph setup .concurrent) named =
              .resolve compiledOwner compiledPayload (checkpoint.refs.get member) compiledChecks
                output code := by
        have moveNode {first second : (serviceGraph setup .concurrent).EventId}
            (equal : first = second)
            (firstOutput : (serviceGraph setup .concurrent).outputLayout first =
              .publication compiledPayload)
            (firstCode : cast (congrArg (EventCode (graphLayout setup.program)) firstOutput)
              ((serviceGraph setup .concurrent).nodes first) =
                .resolve compiledOwner compiledPayload (checkpoint.refs.get member)
                  compiledChecks) :
            ∃ (secondOutput : (serviceGraph setup .concurrent).outputLayout second =
                .publication compiledPayload)
              (secondCode : cast (congrArg (EventCode (graphLayout setup.program)) secondOutput)
                ((serviceGraph setup .concurrent).nodes second) =
                  .resolve compiledOwner compiledPayload (checkpoint.refs.get member)
                    compiledChecks),
              nodeView (serviceGraph setup .concurrent) second =
                .resolve compiledOwner compiledPayload (checkpoint.refs.get member) compiledChecks
                  secondOutput secondCode := by
          cases equal
          exact ⟨firstOutput, firstCode, nodeView_eq_resolve firstOutput firstCode⟩
        have nativeCode : cast (congrArg (EventCode (graphLayout setup.program)) compiledOutput)
            ((serviceGraph setup .concurrent).nodes _) =
              .resolve compiledOwner compiledPayload (checkpoint.refs.get member)
                compiledChecks := by
          simpa only [EventGraph.withMode_nodes, Setup.eventGraph] using compiledCode
        exact moveNode atIndex.symm compiledOutput nativeCode
      have samePayload : compiledPayload = domain :=
        EventField.publication.inj (compiledOutput.symm.trans output)
      subst compiledPayload
      have sameNode := node.symm.trans compiledView
      cases sameNode
      let binding := checkpoint.refs.get member
      have originalSaved := checkpoint.agrees member
      change binding.get? before.execution.application.entry.native.config.store =
        some (checkpoint.source.state.get member) at originalSaved
      have kept := phaseStoredCheckpoint_history implementation.runtime implementation.leaks
        implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
          implementation.scheduler (initialEq ▸ rawPrior)
      have savedAtCurrent := binding.get?_preserved _ _ kept _ originalSaved
      have sameOriginal : checkpoint.source.state.get member = .success value :=
        Option.some.inj (savedAtCurrent.symm.trans stored)
      rw [sameOriginal] at originalSaved
      have literalRead {kind : EventField Player L} (reference : FieldRef
            (serviceGraph setup .concurrent).layout kind) (store : Store _)
          (item : kind.Value) (read : reference.get? store = some item) :
          store reference.field =
            some (cast (congrArg EventField.Value reference.layout_eq.symm) item) := by
        cases reference with
        | mk field layout =>
            cases layout
            exact read
      have savedStore := literalRead binding _ (.success value) originalSaved
      have currentStore := literalRead binding _ (.success value) stored
      have valid := phaseBindingRecord_history implementation.runtime implementation.leaks
        implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
          implementation.scheduler (initialEq ▸ rawPrior)
      have acceptedKept := phaseAcceptedCheckpoint_history implementation.runtime
        implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
          implementation.horizon implementation.scheduler (initialEq ▸ rawPrior)
      have assignedStore := sourceReplayAssignedStoreCongr setup implementation G reference lost
        before.execution.application.entry.native before.execution.application.current.native
          binding.field (savedStore.trans currentStore.symm) (by
            intro actor sort layout val read
            have typedRead : (⟨binding.field, layout⟩ : FieldRef
                (serviceGraph setup .concurrent).layout (.binding actor sort)).get?
                  before.execution.application.entry.native.config.store = some (.success val) := by
              change cast (congrArg Option (congrArg EventField.Value layout))
                (before.execution.application.entry.native.config.store binding.field) = _
              rw [read]
              have castSome {α β : Type} (equal : α = β) (item : α) :
                  cast (congrArg Option equal) (some item) = some (cast equal item) := by
                cases equal
                rfl
              rw [castSome (congrArg EventField.Value layout)]
              simp only [cast_cast, cast_eq]
            obtain ⟨candidate, accepted, _owner, _registered⟩ :=
              valid.saved.success_provenance ⟨binding.field, layout⟩ val typedRead
            exact accepted.trans (acceptedKept binding.field candidate accepted).symm)
      obtain ⟨mapped, current, live, saved, mappedToG, mappedToTarget, mappedDepth,
        mappedInfo, mappedState, point, savedPoint, excluded, generation, agreement⟩ := selected
      rcases mapped with ⟨mappedEndpoint, mappedTrace⟩
      dsimp only at mappedState
      cases mappedState
      let mappedActual : setup.proposalRecoveryProtocol.Trace (some current) := mappedTrace
      have mappedToFull : TracePrefix mappedActual G.trace := mappedToTarget
      have notCommit : ProtocolState.atCommit setup.program current.point = false := by
        rw [point, checkpoint.atCommit]
        have prefixNotCommit {Γ : SourceCtx Player L} {O : Finset VarId}
            (program : SourceProgram Player L Γ O) (reveals : RevealPrefix program (count + 1))
            (source : SourceProgram.Config Player L Γ) :
            ProtocolState.atCommit program (ProtocolState.entry program source) = false := by
          cases program with
          | ret | sample | commit => exact reveals.elim
          | reveal => rfl
        exact prefixNotCommit checkpoint.residual.tail sourcePrefix live
      have savedEq := (setup.commitRecovery_blockFrontier
        (setup.proposalRecoveryEraseTrace mappedActual)).saved_eq_point_of_not_atCommit notCommit
      have sameConfig : saved = live := ProtocolState.entry_injective checkpoint.residual.tail
        (sourceReplaySuffixInjective setup checkpoint.origin
          (savedPoint.symm.trans (savedEq.trans point)))
      subst saved
      have rawArchive : (⟨PhaseProposal.sourceAddress ⟨message.payload.attempt, named⟩,
          domain, value⟩ : ProposalRecoveryProposal L) ∈
          PhaseProposal.sourceArchive reference.execution.network.inputs := by
        apply (PhaseProposal.mem_sourceArchive _ _).mpr
        refine ⟨(⟨message.payload.attempt, named⟩, raw), ?_, ?_⟩
        · apply (PhaseProposal.mem_archive _ _).mpr
          have original := (nativeApplication).reaches_recall_prefix nativeInitial
            implementation.horizon implementation.scheduler
              ((nativeMenu).reaches_raw nativeInitial implementation.horizon
                implementation.scheduler
                retained.reachesWithin) before reference rfl rfl message.sender
          obtain ⟨record, authored, material, transmitted, emitted, _packet⟩ :=
            origins.inputs message input
          have outputAtReference : message ∈ (nativeApplication).outputs
              (reference.execution.recall message.sender) :=
            List.mem_filterMap.mpr ⟨record, original.subset authored, emitted⟩
          rw [← (nativeApplication).history_inputRecall nativeInitial implementation.horizon
            implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
              implementation.scheduler referenceTrace) message.sender] at outputAtReference
          exact ⟨message, (List.mem_filter.mp outputAtReference).1, proposed⟩
        · rw [typed]
          exact PhaseProposal.sourceProposal?_publication _ domain output value
      let proposal : ProposalRecoveryProposal L :=
        ⟨PhaseProposal.sourceAddress ⟨message.payload.attempt, named⟩, domain, value⟩
      have targetArchive : proposal ∈ setup.proposalRecoveryArchive who
          (setup.proposalRecoveryModel.infoOf who g.trace) := by
        rw [sameInfo, (PhaseProposalCanonicalBindingCut.native_readback cut).2.2]
        exact rawArchive
      obtain ⟨proposalBefore, proposalAfter, proposalPrior, joint, legal, moved, proposalKept,
        decoded⟩ := setup.proposalRecovery_proposal_word_origin who g.trace proposal
          (List.mem_toFinset.mp targetArchive)
      cases proposalBefore with
      | none => cases decoded
      | some proposalCurrent =>
        have cursor := Option.some.inj
          (setup.proposalRecoveryProposalOf_cursor (some proposalCurrent) joint proposal decoded)
        have proposalGeneration : proposalCurrent.generation = current.generation := by
          have same := congrArg Prod.fst cursor
          dsimp only [proposal, PhaseProposal.sourceAddress] at same
          change message.payload.attempt.generation = proposalCurrent.generation at same
          rw [sameAttempt] at same
          exact same.symm.trans generation.symm
        have proposalRank : instructionCount setup.program -
            ProtocolState.remaining setup.program proposalCurrent.point = named.val := by
          have rank := congrArg Prod.snd cursor
          exact rank.symm
        have currentRank : instructionCount setup.program -
            ProtocolState.remaining setup.program current.point = phase.low := by
          rw [point, checkpoint.remaining, ProtocolState.remaining_entry]
          have savedRank := checkpoint.saved_position
          rw [checkpoint.remaining, ProtocolState.remaining_entry] at savedRank
          exact savedRank.trans low.symm
        have proposalToG : TracePrefix proposalPrior g.trace :=
          (TracePrefix.extend .refl joint legal moved).trans proposalKept
        have comparable : TracePrefix mappedActual proposalPrior ∨
            TracePrefix proposalPrior mappedActual := by
          by_cases shorter : mappedActual.length ≤ proposalPrior.length
          · exact Or.inl (mappedToG.reachesWithin.ancestor_comparable
              proposalToG.reachesWithin shorter).tracePrefix
          · exact Or.inr (proposalToG.reachesWithin.ancestor_comparable
              mappedToG.reachesWithin (by
                change proposalPrior.length ≤ mappedActual.length
                exact Nat.le_of_lt (Nat.lt_of_not_ge shorter))).tracePrefix
        have forward : TracePrefix mappedActual proposalPrior := by
          rcases comparable with forward | backward
          · exact forward
          · have clock := setup.commitRecovery_same_generation_length
              (setup.proposalRecoveryEraseTrace_prefix backward).reachesWithin
                proposalCurrent current rfl rfl proposalGeneration
            have bounded := ProtocolState.remaining_le_instructionCount setup.program current.point
            have nextBounded := ProtocolState.remaining_le_instructionCount setup.program
              proposalCurrent.point
            have within := (phase.mem_events named).mp inside
            simp only [setup.proposalRecoveryEraseTrace_length] at clock
            change ProtocolState.remaining setup.program current.point + mappedActual.length =
              ProtocolState.remaining setup.program proposalCurrent.point + proposalPrior.length
                at clock
            have remainingOrder : ProtocolState.remaining setup.program proposalCurrent.point ≤
                ProtocolState.remaining setup.program current.point := by omega
            have backwardsLength : proposalPrior.length ≤ mappedActual.length := backward.length_le
            have equalDepth : proposalPrior.length = mappedActual.length := by omega
            exact (mappedToG.reachesWithin.ancestor_comparable
              proposalToG.reachesWithin equalDepth.symm.le).tracePrefix
        obtain ⟨last, joints, addresses, stateEq, path, length, _word, _signals⟩ :=
          source_instruction_window setup
            (setup.initialConfig setup.initialLaw.support_nonempty.choose)
            current (setup.proposalRecoveryEraseTrace mappedActual)
              (setup.proposalRecoveryEraseTrace proposalPrior)
                (setup.proposalRecoveryEraseTrace_prefix forward)
        cases Option.some.inj stateEq
        have clock := setup.commitRecovery_same_generation_length
          (setup.proposalRecoveryEraseTrace_prefix forward).reachesWithin current proposalCurrent
            rfl rfl proposalGeneration.symm
        simp only [setup.proposalRecoveryEraseTrace_length] at clock length
        have rows : joints.length = count := by
          have bounded := ProtocolState.remaining_le_instructionCount setup.program current.point
          have nextBounded := ProtocolState.remaining_le_instructionCount setup.program
            proposalCurrent.point
          dsimp only [count]
          omega
        have entryMask : current.entryExcluded = current.excluded := by
          let original : setup.proposalRecoveryProtocol.History :=
            ⟨some (CommitRecoveryState.atPoint
              (checkpoint.residual.lift
                (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
                before.execution.application.entry.excluded
                  before.execution.application.generation),
              setup.proposalRecoveryLiftTrace
                (nativeArchiveLabels setup (PhaseProposal.sourceArchive
                  reference.execution.network.inputs)) checkpoint.trace⟩
          have info : setup.proposalRecoveryModel.infoOf who original.trace =
              setup.proposalRecoveryModel.infoOf who mappedActual := mappedInfo.symm
          have metadata := source_information_metadata setup who original
            ⟨some current, mappedActual⟩ info
          exact metadata.2.2.2.1.symm.trans metadata.2.2.1
        have initialPoint : current = CommitRecoveryState.atPoint
            (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail live))
              current.excluded current.generation := by
          rw [← point]
          cases current with
          | mk point saved excluded entryExcluded generation entered =>
            dsimp only at savedEq entryMask ⊢
            subst saved
            subst entryExcluded
            rfl
        have originalProposal : (ProtocolState.recoveryProposal setup.program proposalCurrent.point
            (fun actor => if actor ∈ proposalCurrent.excluded then none else joint actor)).map
              Prod.snd = some (⟨domain, value⟩ : Sigma L.Val) := by
          obtain ⟨pair, read, same⟩ := Option.map_eq_some_iff.mp decoded
          have rawEq := congrArg (fun item : ProposalRecoveryProposal L =>
            (⟨item.payload, item.value⟩ : Sigma L.Val)) same
          exact (congrArg (Option.map Prod.snd) read).trans (congrArg some rawEq)
        have assignedProposal := sourceReplayRevealProposalRead setup count checkpoint.residual.tail
          sourcePrefix checkpoint.refs checkpoint.source.revelations checkpoint.registry
            checkpoint.embedding checkpoint.before before.execution.application.attempt.phase
              checkpoint.compiled checkpoint.residual.lift checkpoint.origin live current.excluded
                current.generation proposalCurrent joints addresses
                  (sourceSnapshotState setup implementation G reference lost
                    before.execution.application.entry.native)
                    (fun member => agreement member) (initialPoint ▸ path) rows _ _ originalProposal
        have absolute : before.execution.application.attempt.phase + count = named.val := by
          rw [← low]
          dsimp only [count]
          have within := (phase.mem_events named).mp inside
          omega
        rw [absolute] at assignedProposal
        have assignedSaved : binding.get? (sourceSnapshotState setup implementation G reference
            lost before.execution.application.entry.native).config.store =
              some (.success value) := by
          have recover (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
              (reference : FieldRef (serviceGraph setup .concurrent).layout
                (.binding owner domain))
              (event : (serviceGraph setup .concurrent).EventId)
              (checks : List (GuardCheck (serviceGraph setup .concurrent).layout domain))
              (shape : (serviceGraph setup .concurrent).outputLayout event = .publication domain)
              (code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) shape)
                ((serviceGraph setup .concurrent).nodes event) =
                  .resolve owner domain reference checks)
              (proposal : nativeStoredProposal? image event.val =
                some (⟨domain, value⟩ : Sigma L.Val)) :
              reference.get? image.config.store = some (.success value) := by
            have viewed := nodeView_eq_resolve shape code
            cases read : reference.get? image.config.store with
            | none =>
                simp only [nativeStoredProposal?, event.isLt, dite_true, viewed, read] at proposal
                cases proposal
            | some result =>
                have decoded := nativeStoredProposal?_resolve image event reference checks shape
                  code result read
                rw [decoded] at proposal
                cases result with
                | failure => cases proposal
                | success actual =>
                    have same : actual = value :=
                      eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj proposal)).2
                    exact congrArg some (congrArg PublicationResult.success same)
          exact recover _ binding named checks output code assignedProposal
        have assignedCurrent : binding.get? (sourceSnapshotState setup implementation G reference
            lost before.execution.application.current.native).config.store =
              some (.success value) :=
          (binding.get?_congr _ _ assignedStore).symm.trans assignedSaved
        obtain ⟨candidate, associated, _owned, opened⟩ := valid.active.success_provenance
          binding value stored
        have referenceAt {kind : EventField Player L}
            (reference : FieldRef (serviceGraph setup .concurrent).layout kind)
            (field : (serviceGraph setup .concurrent).Field)
            (equal : reference.field = field)
            (layout : (serviceGraph setup .concurrent).layout field = kind) :
            reference = ⟨field, layout⟩ := by
          cases reference
          cases equal
          rfl
        cases field : binding.field with
        | inr bound =>
            have boundShape : (serviceGraph setup .concurrent).outputLayout bound =
                .binding owner domain := by
              change (serviceGraph setup .concurrent).layout (.inr bound) = _
              exact field ▸ binding.layout_eq
            have bindingEq : binding = (⟨.inr bound, boundShape⟩ : FieldRef
                (serviceGraph setup .concurrent).layout (.binding owner domain)) :=
              referenceAt binding _ field boundShape
            have boundStored : (⟨.inr bound, boundShape⟩ : FieldRef
                (serviceGraph setup .concurrent).layout (.binding owner domain)).get?
                  before.execution.application.current.native.config.store =
                    some (.success value) := by
              change binding.get? before.execution.application.current.native.config.store =
                some (.success value) at stored
              rw [bindingEq] at stored
              exact stored
            have boundAccepted : before.execution.application.current.native.accepted
                (.inr bound) = some candidate := by simpa only [field] using associated
            obtain ⟨next, meaning, assignedLiteral, _result, _focal⟩ :=
              assigned_accepted_binding_read setup values implementation operational reference
                (sourceCutTrace setup implementation referenceTrace)
                who event cut g sameInfo good choice properChoice G supported lost
                  before (sourceCutTrace setup implementation prior)
                  (tracePrefix_initializer setup implementation initialEq retained)
                    before.execution.application.current.native (Or.inl rfl)
                    owner domain bound boundShape candidate value boundAccepted boundStored
            have nextEq : next = value := by
              have assignedRead := assignedCurrent
              rw [bindingEq] at assignedRead
              have literal := literalRead (⟨.inr bound, boundShape⟩ : FieldRef
                (serviceGraph setup .concurrent).layout (.binding owner domain))
                  _ (.success value) assignedRead
              have equal := congrArg (cast (congrArg EventField.Value boundShape))
                (Option.some.inj (assignedLiteral.symm.trans literal))
              simpa only [cast_cast, cast_eq, PublicationResult.success.injEq] using equal
            subst next
            have registered := (accepted_snapshot_catalogue setup implementation reference
              referenceTrace before prior retained before.execution.application.current.native
                (Or.inl rfl) owner domain binding candidate associated).2.trans opened
            cases boundNode : nodeView (serviceGraph setup .concurrent) bound with
            | bind actualOwner actualPayload shape bindCode =>
                have ownerEq : actualOwner = owner :=
                  (EventField.binding.inj (shape.symm.trans boundShape)).1
                have payloadEq : actualPayload = domain :=
                  (EventField.binding.inj (shape.symm.trans boundShape)).2
                subst actualOwner
                subst actualPayload
                exact sourceSnapshot_reveal_fixed_output setup implementation G reference lost
                  before.execution.application.current.native named bound owner domain binding
                    checks output code node field boundShape bindCode boundNode candidate value
                      (literalRead _ _ _ boundStored) boundAccepted registered meaning
            | resolve _ _ _ _ shape _ => cases shape.symm.trans boundShape
            | sample _ _ shape _ => cases shape.symm.trans boundShape
        | inl input =>
            have inputShape : (serviceGraph setup .concurrent).inputLayout input =
                .binding owner domain := by
              change (serviceGraph setup .concurrent).layout (.inl input) = _
              exact field ▸ binding.layout_eq
            have bindingEq : binding = (⟨.inl input, inputShape⟩ : FieldRef
                (serviceGraph setup .concurrent).layout (.binding owner domain)) :=
              referenceAt binding _ field inputShape
            have initialHandle := phaseInputBinding_history implementation.runtime
              implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
                implementation.horizon implementation.scheduler (initialEq ▸ rawPrior)
                  input owner domain inputShape
            have associatedInput : before.execution.application.current.native.accepted
                (.inl input) = some candidate := by simpa only [field] using associated
            have candidateEq : candidate = (owner, .initial input) :=
              Option.some.inj (associatedInput.symm.trans initialHandle)
            subst candidate
            have registered := (accepted_snapshot_catalogue setup implementation reference
              referenceTrace before prior retained before.execution.application.current.native
                (Or.inl rfl) owner domain binding (owner, .initial input) associated).2.trans opened
            have initialStored := stored
            have initialAssigned := assignedCurrent
            change binding.get? before.execution.application.current.native.config.store =
              some (.success value) at initialStored
            rw [bindingEq] at initialStored initialAssigned
            have currentLiteral := literalRead (⟨.inl input, inputShape⟩ : FieldRef
              (serviceGraph setup .concurrent).layout (.binding owner domain))
                _ (.success value) initialStored
            have assignedLiteral := literalRead (⟨.inl input, inputShape⟩ : FieldRef
              (serviceGraph setup .concurrent).layout (.binding owner domain))
                _ (.success value) initialAssigned
            have hidden : ¬ (serviceGraph setup .concurrent).fieldPublic (.inl input) := by
              change ¬ ((serviceGraph setup .concurrent).inputLayout input).IsPublic
              rw [inputShape]
              exact not_false
            have targetInput : encodeInputs (ProtocolState.base setup.program targetCurrent.point)
                input = cast (congrArg EventField.Value inputShape.symm) (.success value) := by
              change (before.execution.application.current.native.config.store (.inl input)).map
                (pairSwap (sourceSnapshotPair setup implementation G reference lost
                  before.execution.application.current.native (.inl input))) = _ at assignedLiteral
              simp only [sourceSnapshotPair, hidden, ↓reduceIte, currentLiteral,
                Option.bind_some, G, Option.map_some, pairSwap,
                Equiv.swap_apply_left] at assignedLiteral
              exact Option.some.inj assignedLiteral
            exact sourceSnapshot_reveal_fixed_initial setup implementation G reference lost
              before.execution.application.current.native targetCurrent rfl named input owner domain
                binding checks output code node field inputShape value currentLiteral targetInput
                  initialHandle registered
    exact {
      handling := by
        intro id message lookup
        have lookupId : message.id = id := by
          have found : before.execution.network.pending.find?
              (fun packet => packet.id = id) = some message := lookup
          have selectedId := List.find?_some found
          exact of_decide_eq_true selectedId
        have ownLookup : before.execution.network.lookup message.id = some message := by
          rw [lookupId]
          exact lookup
        have rawPrior := (nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler prior
        have origins := (nativeApplication).history_provenance nativeInitial
          implementation.horizon implementation.scheduler rawPrior
        have inputRecall := (nativeApplication).history_inputRecall nativeInitial
          implementation.horizon implementation.scheduler rawPrior
        have beforeInput := ((nativeApplication).retained_envelopes_mem_inputs
          before.execution origins inputRecall).lookup id message lookup
        have recalled := (nativeApplication).reaches_recall_prefix nativeInitial
          implementation.horizon implementation.scheduler
            ((nativeMenu).reaches_raw nativeInitial implementation.horizon
              implementation.scheduler retained.reachesWithin) before reference rfl rfl
        have rawReference := (nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler referenceTrace
        have referenceRecall := (nativeApplication).history_inputRecall nativeInitial
          implementation.horizon implementation.scheduler rawReference
        have referenceClean := (PhaseCount.onePacketMenu_countClean implementation.runtime
          implementation.leaks implementation.bounds implementation.scheduler).history
            nativeInitial implementation.horizon
              (fun state _ => PhaseCount.countClean_initial implementation.runtime
                implementation.leaks state) referenceTrace
        cases packet : message.payload.packet.call with
        | malformed raw =>
            constructor
            · simp only [phaseApplication, PhaseRuntimeState.handle, packet,
                EventGraphRuntime.handle, Option.map_none, ite_self]
            · intro _
              simp only [EventGraphRuntime.handle, Option.map_none]
        | opening named handle raw =>
            constructor
            · exact sourceSnapshotAssignment_handle_opening setup implementation G reference lost
                implementation.runtime before.execution.application message named handle raw packet
                  (fun admitted ready => openingFixed message named handle raw ownLookup packet
                    admitted ready)
            · intro admitted
              simpa only [packet] using sourceSnapshot_handle_opening setup implementation G
                reference lost implementation.runtime before.execution.application.current.native
                  message.id named handle raw
                    (fun ready => openingFixed message named handle raw ownLookup packet
                      (by simpa only [packet] using admitted) ready)
        | commitment named handle =>
            cases handled : before.execution.application.handle implementation.runtime message with
            | none =>
                have replay := sourceSnapshotAssignment_rejected_binding setup implementation
                  G reference lost implementation.runtime before.execution.application message
                    named handle packet handled
                simpa only [phaseApplication, handled, Option.map_none, packet] using replay
            | some after =>
                have nativeAccepted : ∃ native,
                    EventGraphRuntime.handle implementation.runtime
                      before.execution.application.current.native
                        ⟨message.id, .commitment named handle⟩ = some native := by
                  unfold PhaseRuntimeState.handle at handled
                  split at handled
                  · obtain ⟨native, accepted, _⟩ := Option.map_eq_some_iff.mp handled
                    exact ⟨native, by simpa only [packet] using accepted⟩
                  · cases handled
                obtain ⟨native, accepted⟩ := nativeAccepted
                obtain ⟨_ready, _timely, owner, domain, binding, _code, _node, _sender,
                  handleOwner, _vacant, _unused⟩ := handle_commitment_conditions
                    implementation.runtime before.execution.application.current.native native
                      message.id named handle accepted
                obtain ⟨serial, opening, evidence, record, handleEq, sender, recorded, emitted,
                  declared, _fresh, _namespace, originalResult⟩ := issued_binding_record setup
                    implementation before prior owner named domain binding handle message
                      beforeInput packet
                have recordAtReference := (recalled owner).subset recorded
                have messageAtReference : message ∈ reference.execution.network.inputs := by
                  have authored : message ∈ (nativeApplication).outputs
                      (reference.execution.recall owner) :=
                    List.mem_filterMap.mpr ⟨record, recordAtReference, emitted⟩
                  rw [← referenceRecall owner] at authored
                  exact (List.mem_filter.mp authored).1
                have recordHandle : record ∈ reference.execution.recall handle.1 := by
                  rw [handleOwner]
                  exact recordAtReference
                have typedMeaning := sourceHandleMeaning_of_emission setup implementation
                  G reference referenceTrace handle record recordHandle message emitted named packet
                    owner domain binding
                      (sourceBindingAt setup message.payload.attempt named owner domain binding
                        G.trace) rfl
                have effective : ∃ next : Option (L.Val domain),
                    (sourceHandleMeaning setup implementation G reference handle).orElse
                      (fun _ => lost handle) =
                        next.map (fun value => (⟨domain, value⟩ : Raw L)) := by
                  rw [typedMeaning]
                  cases read : sourceBindingAt setup message.payload.attempt named owner domain
                      binding G.trace with
                  | some value => exact ⟨some value, rfl⟩
                  | none =>
                      cases lostValue : lost handle with
                      | none => exact ⟨none, rfl⟩
                      | some raw =>
                          obtain ⟨_foreign, _prepared, _noMeaning, lostRecord, lostMessage,
                            lostEvent, lostPayload, old, lostRecorded, lostEmitted, _lostSender,
                            lostCall, _historical, lostBinding, lostType, _preparedValue,
                            _noReceipt⟩ := restricted handle raw lostValue
                          have lostInput : lostMessage ∈ reference.execution.network.inputs := by
                            have authored : lostMessage ∈ (nativeApplication).outputs
                                (reference.execution.recall handle.1) :=
                              List.mem_filterMap.mpr ⟨lostRecord, lostRecorded, lostEmitted⟩
                            rw [← referenceRecall handle.1] at authored
                            exact (List.mem_filter.mp authored).1
                          have identical : lostMessage = message :=
                            PhaseCount.commitment_eq_of_handle reference.execution.network.inputs
                              lostMessage message
                                ((PhaseCount.permits_eq_true_iff _ _).mp
                                  (referenceClean.2 lostMessage lostInput))
                                ((PhaseCount.permits_eq_true_iff _ _).mp
                                  (referenceClean.2 message messageAtReference)) lostInput
                                messageAtReference
                                (fun first firstInput second secondInput ids =>
                                  (nativeApplication).input_identifier_injective_history
                                    nativeInitial implementation.horizon implementation.scheduler
                                      reference rawReference first second
                                        firstInput secondInput ids)
                                lostCall packet
                          have sameEvent : lostEvent = named := by
                            subst lostMessage
                            exact (Payload.commitment.inj (lostCall.symm.trans packet)).1
                          subst lostEvent
                          have sameType : lostPayload = domain :=
                            (EventField.binding.inj (lostBinding.symm.trans binding)).2
                          rcases raw with ⟨rawType, value⟩
                          dsimp only at lostType
                          have typeEq : rawType = domain := lostType.trans sameType
                          cases typeEq
                          exact ⟨some value, rfl⟩
                have suitable :
                    (∃ (old : L.Val domain) (next : Option (L.Val domain)),
                      before.execution.application.current.native.candidates.lookup handle =
                        .openable (⟨domain, old⟩ : Raw L) ∧
                      reference.execution.application.current.native.candidates.lookup handle =
                        .openable (⟨domain, old⟩ : Raw L) ∧
                      (sourceHandleMeaning setup implementation G reference handle).orElse
                        (fun _ => lost handle) =
                          next.map (fun value => (⟨domain, value⟩ : Raw L))) ∨
                    (before.execution.application.current.native.bindingResult handle domain =
                      .failure ∧ pairSwap (sourceHandlePairs setup implementation G reference
                        lost handle) = (fun value => value)) := by
                  cases result : before.execution.application.current.native.bindingResult
                      handle domain with
                  | success old =>
                      have original : before.execution.application.current.native.candidates.lookup
                          handle = .openable (⟨domain, old⟩ : Raw L) :=
                        (State.bindingResult_eq_success_iff _ _ _ _).mp result
                      let stable := phaseApplication_preservesFixedCandidates implementation.runtime
                        implementation.leaks
                      have fixed : (nativeApplication).Invariant (fun state =>
                          state.current.native.candidates.lookup handle =
                            .openable (⟨domain, old⟩ : Raw L)) := by
                        constructor
                        · intro state actor material known
                          exact (stable.submit state actor material handle
                            (by rw [known]; intro impossible; cases impossible)).trans known
                        · intro state packet next known accepted
                          exact (stable.handle state packet next accepted handle
                            (by rw [known]; intro impossible; cases impossible)).trans known
                        · intro state command next known reached
                          exact (stable.environment state command next reached handle
                            (by rw [known]; intro impossible; cases impossible)).trans known
                      have registered := fixed.tracePrefix (nativeMenu) nativeInitial
                        implementation.horizon implementation.scheduler before reference prior
                          referenceTrace retained original
                      obtain ⟨next, read⟩ := effective
                      exact Or.inl ⟨old, next, original, registered, read⟩
                  | failure =>
                      have own : owner = who := by
                        by_contra foreignOwner
                        obtain ⟨value, usable⟩ := phaseProposal_recalled_binding_preparation_value
                          implementation.runtime implementation.leaks implementation.bounds
                            nativeInitial implementation.horizon implementation.scheduler reference
                              referenceTrace owner (foreign owner foreignOwner) named domain binding
                                serial opening evidence record recordAtReference declared
                        rw [usable, Option.elim_some] at originalResult
                        rw [result] at originalResult
                        cases originalResult
                      refine Or.inr ⟨rfl, ?_⟩
                      have shape : handle = (who, handle.2) := Prod.ext (handleOwner.trans own) rfl
                      rw [shape]
                      exact focalHandles handle.2
                have replay := sourceSnapshotAssignment_handle_binding setup implementation
                  G reference lost implementation.runtime before.execution.application after message
                    named handle owner domain binding packet suitable handled
                refine ⟨?_, fun _ => by simpa only [packet] using replay.2⟩
                simpa only [phaseApplication, handled, Option.map_some] using replay.1
      openingFixed := openingFixed
      focalView := by
        intro recalls _focalRecall
        have initialEq : nativeInitial =
            (setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan) := by
          simp only [ReservedConcurrentImplementation.initial, PMF.map_comp,
            Function.comp_def]
        have rawPrior := (nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler prior
        obtain ⟨draw, native⟩ := phaseNativeInvariant_history implementation.runtime
          implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
            implementation.horizon implementation.scheduler
              (initialEq ▸ rawPrior)
        have referenceNative :=
          (phaseApplication_invariant implementation.runtime implementation.leaks draw).tracePrefix
            (nativeMenu) nativeInitial implementation.horizon implementation.scheduler
              before reference prior referenceTrace retained native
        have originalInputs :
            before.execution.application.current.native.config.inputs =
              encodeInputs cut.theta :=
          native.active.reachable.inputs_eq.trans
            (referenceNative.active.reachable.inputs_eq.symm.trans cut.originalInputs)
        have publicView := sourceSnapshotAssignment_public setup implementation G reference
          lost before.execution.application
        have privateView :
            (sourceSnapshotState setup implementation G reference lost
              before.execution.application.current.native).playerView who =
              before.execution.application.current.native.playerView who := by
          let swap := HiddenSwap.ofPairs
            (sourceSnapshotPairs setup implementation G reference lost
              before.execution.application.current.native)
            (sourceHandlePairs setup implementation G reference lost)
          have fields : ∀ field,
              (serviceGraph setup .concurrent).fieldVisibleTo who field →
                swap.values.value field = id := by
            intro field visible
            by_cases isPublic : (serviceGraph setup .concurrent).fieldPublic field
            · change pairSwap (sourceSnapshotPair setup implementation G reference lost
                before.execution.application.current.native field) = id
              simp only [sourceSnapshotPair, isPublic, ↓reduceIte]
              rfl
            · cases field with
              | inl input =>
                  have targetInput := sourceReplayTargetVisibleInputs setup values implementation
                    who reference referenceTrace event cut g sameInfo choice targetCurrent
                      targetTrace supported input visible
                  have stored :
                      before.execution.application.current.native.config.store (.inl input) =
                        some (encodeInputs cut.theta input) := by
                    rw [EventGraph.Config.store_input, originalInputs]
                  change pairSwap (sourceSnapshotPair setup implementation G reference lost
                    before.execution.application.current.native (.inl input)) = id
                  simp only [sourceSnapshotPair, isPublic, ↓reduceIte, stored,
                    Option.bind_some, G, Option.map_some, targetInput,
                    pairSwap, Equiv.swap_self]
                  rfl
              | inr named =>
                  change pairSwap (sourceSnapshotPair setup implementation G reference lost
                    before.execution.application.current.native (.inr named)) = id
                  cases descriptor : nodeView (serviceGraph setup .concurrent) named with
                  | resolve owner payload binding checks shape code =>
                      simp only [sourceSnapshotPair, isPublic, ↓reduceIte, descriptor]
                      cases before.execution.application.current.native.config.store
                        (.inr named) <;> rfl
                  | sample payload law shape code =>
                      simp only [sourceSnapshotPair, isPublic, ↓reduceIte, descriptor]
                      cases before.execution.application.current.native.config.store
                        (.inr named) <;> rfl
                  | bind owner payload shape code =>
                      have own : owner = who := by
                        change ((serviceGraph setup .concurrent).outputLayout named).VisibleTo
                          who at visible
                        rwa [shape] at visible
                      subst owner
                      cases stored : before.execution.application.current.native.config.store
                          (.inr named) with
                      | none =>
                          simp only [sourceSnapshotPair, isPublic, ↓reduceIte, stored,
                            Option.bind_none, pairSwap]
                      | some value =>
                          cases typed : cast (congrArg EventField.Value shape) value with
                          | failure =>
                              simp only [sourceSnapshotPair, isPublic, ↓reduceIte, stored,
                                Option.bind_some, descriptor, typed, pairSwap]
                          | success old =>
                              cases accepted :
                                  before.execution.application.current.native.accepted
                                    (.inr named) with
                              | none =>
                                  simp only [sourceSnapshotPair, isPublic, ↓reduceIte, stored,
                                    Option.bind_some, descriptor, typed, accepted,
                                    Option.bind_none, pairSwap]
                              | some handle =>
                                  have valueEq : value = cast
                                      (congrArg EventField.Value shape.symm) (.success old) := by
                                    have recovered := congrArg
                                      (cast (congrArg EventField.Value shape.symm)) typed
                                    simpa only [cast_cast, cast_eq] using recovered
                                  have literal :
                                      before.execution.application.current.native.config.store
                                        (.inr named) = some (cast
                                          (congrArg EventField.Value shape.symm)
                                            (.success old)) :=
                                    stored.trans (congrArg some valueEq)
                                  have read : (⟨.inr named, shape⟩ : FieldRef
                                      (serviceGraph setup .concurrent).layout
                                        (.binding who payload)).get?
                                          before.execution.application.current.native.config.store =
                                            some (.success old) := by
                                    change cast (congrArg
                                      (fun kind : EventField Player L => Option kind.Value) shape)
                                        (before.execution.application.current.native.config.store
                                          (.inr named)) = _
                                    rw [literal]
                                    have castSome {α β : Type} (same : α = β) (item : α) :
                                        cast (congrArg Option same) (some item) =
                                          some (cast same item) := by
                                      cases same
                                      rfl
                                    change cast (congrArg Option (congrArg EventField.Value shape))
                                      (some (cast (congrArg EventField.Value shape.symm)
                                        (.success old))) = _
                                    rw [castSome (congrArg EventField.Value shape)]
                                    simp only [cast_cast, cast_eq]
                                  obtain ⟨next, _registered, meaning, focalValue⟩ :=
                                    sourceHandleMeaning_of_accepted_binding setup values
                                      implementation operational reference
                                        (sourceCutTrace setup implementation referenceTrace) who
                                        event cut g sameInfo good choice properChoice G supported
                                          before
                                          (sourceCutTrace setup implementation prior)
                                          (by
                                            unfold sourceCutTrace
                                            exact tracePrefix_initializer setup implementation _
                                              retained)
                                            before.execution.application.current.native
                                              (Or.inl rfl) who payload named shape handle old
                                                accepted read
                                  have unchanged : next = old := focalValue rfl
                                  subst next
                                  rw [sourceSnapshotPair_binding_value setup implementation
                                    G reference lost before.execution.application.current.native
                                      named who payload shape code descriptor handle old old
                                        literal accepted meaning]
                                  simp only [pairSwap, Equiv.swap_self]
                                  rfl
          have actions : ∀ event,
              (serviceGraph setup .concurrent).actor? event = some who →
                swap.values.action event = id := by
            intro event acting
            change (sourceSnapshotPairs setup implementation G reference lost
              before.execution.application.current.native).action event = id
            unfold SwapPairs.action
            cases view : nodeView (serviceGraph setup .concurrent) event with
            | resolve => rfl
            | sample => rfl
            | bind owner payload outputEq codeEq =>
                have actorEq : (serviceGraph setup .concurrent).actor? event =
                    some owner :=
                  (EventCode.actor_cast outputEq
                    ((serviceGraph setup .concurrent).nodes event)).symm.trans
                      (congrArg EventCode.actor codeEq)
                rw [actorEq] at acting
                cases Option.some.inj acting
                have visible : (serviceGraph setup .concurrent).fieldVisibleTo who
                    (.inr event) := by
                  change ((serviceGraph setup .concurrent).outputLayout event).VisibleTo who
                  rw [outputEq]
                  rfl
                have fixed := fields (.inr event) visible
                change pairSwap (sourceSnapshotPair setup implementation G reference lost
                  before.execution.application.current.native (.inr event)) = id at fixed
                dsimp only [sourceSnapshotPairs]
                rw [fixed]
                funext original
                simp
          have handles := focalHandles
          change (before.execution.application.current.native.swap swap).playerView who = _
          rw [State.swap_playerView]
          unfold PlayerView.swap
          dsimp only [State.playerView]
          rw [PlayerObservation.swap_eq_self swap.values fields actions]
          congr 1
          funext slot
          rw [handles slot]
          cases before.execution.application.current.native.candidates.lookup (who, slot) <;> rfl
        have sameApplication :
            (sourceSnapshotAssignment setup implementation G reference lost
              before.execution.application).playerView who =
                before.execution.application.playerView who := Prod.ext privateView publicView
        exact congrArg (fun view =>
          (⟨before.execution.network.observe who, view, before.execution.receipts⟩ :
            (nativeApplication).PlayerView)) sameApplication
      focalAction := by
        intro _actionPrior _after joint legal _moved _kept action _acting chosen
        have offered := legal.2 who
        rw [chosen] at offered
        exact swap.phaseAction_eq_of_onePacket implementation.bounds who focalHandles
          (before.execution.recall who) (before.execution.observe nativeApplication who)
            action offered.2
      query := by
        exact sourceReplay_query_binding (setup := setup) (values := values)
          (implementation := implementation) operational fullValues who reference referenceTrace
            acting event payload clean foreign entry g sameInfo good choice properChoice
              targetCurrent targetTrace supported selectedAgreement completedVisits lost restricted
                before prior retained }
  · intro lost restricted before prior retained owner handle raw record message named
      payload old foreignOwner handleOwner fresh noLost recorded emitted sender call shape rawShape
      prepared
    have recordedHandle : record ∈ reference.execution.recall handle.1 := by
      rw [handleOwner]
      exact recorded
    cases read : sourceBindingAt setup message.payload.attempt named owner payload shape
        G.trace with
    | some next =>
        have meaning := sourceHandleMeaning_of_emission setup implementation G reference
          referenceTrace handle record recordedHandle message emitted named call owner payload
            shape (some next) read
        exact Or.inl ⟨next, meaning⟩
    | none =>
        have meaning := sourceHandleMeaning_of_emission setup implementation G reference
          referenceTrace handle record recordedHandle message emitted named call owner payload
            shape none read
        let rawTrace := (nativeMenu).toRawTrace nativeInitial
          implementation.horizon implementation.scheduler referenceTrace
        have inputRecall := (nativeApplication).history_inputRecall nativeInitial
          implementation.horizon implementation.scheduler rawTrace
        have messageInput : message ∈ reference.execution.network.inputs := by
          have authored : message ∈
              (nativeApplication).outputs (reference.execution.recall owner) :=
            List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
          rw [← inputRecall owner] at authored
          exact (List.mem_filter.mp authored).1
        have countClean := (PhaseCount.onePacketMenu_countClean implementation.runtime
          implementation.leaks implementation.bounds implementation.scheduler).history
            nativeInitial implementation.horizon
              (fun state _ => PhaseCount.countClean_initial implementation.runtime
                implementation.leaks state) referenceTrace
        have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
          (countClean.2 message messageInput)).2.1
        unfold CountCallCorrect at correct
        dsimp only [PhaseCount.nativeMessage] at correct
        rw [call] at correct
        obtain ⟨_owned, _evidence, _handleSender, preparedHandle, _unique⟩ := correct
        have historical : message.payload.attempt ≠
            reference.execution.application.attempt := by
          intro sameAttempt
          obtain ⟨material, transmitted, _preparedValue⟩ :=
            Option.bind_eq_some_iff.mp prepared
          have activeAtCut : owner ∉ cut.cursor.current.excluded := by
            let initial := (setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan)
            have initialEq : nativeInitial = initial := by
              simp only [initial, ReservedConcurrentImplementation.initial,
                PMF.map_comp, Function.comp_def]
            have countedTrace : ((nativeMenu).protocol initial
                implementation.horizon implementation.scheduler).Trace
                  (some reference) := by
              rw [← initialEq]
              exact referenceTrace
            have emittedPacket := PhaseCount.recalled_submission_emitted
              implementation.runtime implementation.leaks initial
                implementation.horizon implementation.scheduler
                  ((nativeMenu).toRawTrace initial implementation.horizon
                    implementation.scheduler countedTrace)
                      owner record recorded material transmitted
            obtain ⟨actualMessage, sent, _sender, packet⟩ := emittedPacket
            have actualMessageEq : actualMessage = message :=
              Option.some.inj (sent.symm.trans emitted)
            subst actualMessage
            obtain ⟨callback, callbackTrace, callbackKept, _acting, viewed,
              request⟩ := phase_recorded_binding_request implementation.runtime
                implementation.leaks implementation.bounds implementation.plan
                  (setup.initialLaw.map encodeInputs) implementation.horizon
                    (serviceGraph_revealRelaxedOrdered setup .concurrent)
                      implementation.scheduler countedTrace owner record recorded
                        material transmitted named handle (packet.symm.trans call)
            have emittedAttempt := phase_recalled_emission_attempt
              implementation.runtime implementation.leaks initial
                implementation.horizon implementation.scheduler
                  ((nativeMenu).toRawTrace initial implementation.horizon
                    implementation.scheduler countedTrace)
                      owner record recorded message emitted
            rw [viewed] at emittedAttempt
            have callbackAttempt : callback.execution.application.attempt =
                reference.execution.application.attempt :=
              emittedAttempt.symm.trans sameAttempt
            have initialized : ∀ state ∈ initial.support, state.Ordered := by
              intro state present
              obtain ⟨draw, _drawn, rfl⟩ := PMF.support_map .. ▸ present
              exact PhaseRuntimeState.initial_ordered implementation.plan draw
            have callbackOrdered := (phaseApplication_seedOrder implementation.runtime
              implementation.leaks).history initial implementation.horizon
                implementation.scheduler initialized
                  ((nativeMenu).toRawTrace initial implementation.horizon
                    implementation.scheduler callbackTrace)
            have sameEntry := (phase_attempt_progress_of_prefix
              implementation.runtime implementation.leaks (nativeMenu) initial
                initialized implementation.horizon implementation.scheduler callback
                  reference callbackTrace countedTrace callbackKept callbackOrdered).2.2
                    callbackAttempt
            have callbackOriginal : (nativeProtocol).Trace (some callback) := by
              rw [initialEq]
              exact callbackTrace
            have callbackWitness := (checkpointSelection setup implementation
              operational callbackOriginal).val
            have callbackActive : owner ∉
                callback.execution.application.current.excluded := request.2.2.2.2
            have savedActive : owner ∉
                callback.execution.application.entry.excluded :=
              fun member => callbackActive
                (callbackWitness.exclusions.coverage.inherited member)
            have finalSavedActive : owner ∉
                reference.execution.application.entry.excluded := by
              rw [← sameEntry]
              exact savedActive
            have finalSaved := clean.excluded_eq setup implementation reference
              (checkpointSelection setup implementation operational referenceTrace).val
                entry.phase entry.installed
            have cursorExcluded : cut.cursor.current.excluded =
                reference.execution.application.entry.excluded :=
              cut.cursor.excluded.trans (entry.excluded.symm.trans finalSaved)
            rw [cursorExcluded]
            exact finalSavedActive
          obtain ⟨value, currentMeaning⟩ :=
            sourceHandleMeaning_of_current_emission setup values implementation
              operational reference (sourceCutTrace setup implementation referenceTrace)
                who event cut g sameInfo good choice
                properChoice G supported owner activeAtCut record recorded material transmitted
                  message emitted sameAttempt named payload shape handle call
          rw [show sourceHandleMeaning setup implementation G reference handle = none by
            simpa only [Option.map_none] using meaning] at currentMeaning
          cases currentMeaning
        have noReceipt : ¬ PhaseService.BindingAccepted implementation.runtime
            implementation.leaks ⟨message.payload.attempt, named⟩ owner
              reference.execution := by
          intro accepted
          obtain ⟨other, otherInput, otherSender, otherAttempt, otherEvent,
            acceptedReceipt⟩ := accepted
          have samePacket : message = other := PhaseCount.Permits.eq_of_same_event
            ((PhaseCount.permits_eq_true_iff _ _).mp
              (countClean.2 message messageInput))
            ((PhaseCount.permits_eq_true_iff _ _).mp
              (countClean.2 other otherInput))
            messageInput otherInput
            (fun left leftInput right rightInput same =>
              (nativeApplication).input_identifier_injective_history nativeInitial
                implementation.horizon implementation.scheduler reference rawTrace
                  left right leftInput rightInput same)
            (sender.trans otherSender.symm)
            (by
              unfold PhaseCount.event?
              rw [call, otherEvent, otherAttempt]
              rfl)
          subst other
          have acceptedRow : (message.id, true) ∈ reference.execution.receipts →
              ∃ value : L.Val payload,
                sourceBindingAt setup message.payload.attempt named owner payload shape
                  G.trace = some value := by
            intro acceptedReceipt
            obtain ⟨acceptBefore, acceptAfter, acceptPrior, acceptJoint, acceptLegal,
              acceptMoved, acceptKept, absent, present, _idle, _afterIdle, included⟩ :=
              accepting_receipt_transition setup implementation message.id referenceTrace
                ⟨reference, rfl, acceptedReceipt⟩
            obtain ⟨actual, acceptedNative, lookup, acceptedAttempt, acceptedCall,
              handled, normalized⟩ := accepting_receipt_handler setup implementation
                acceptBefore acceptAfter acceptPrior message.id absent present included
            have acceptPriorKept : TracePrefix acceptPrior referenceTrace :=
              (TracePrefix.extend .refl acceptJoint acceptLegal acceptMoved).trans
                acceptKept
            have actualEq : actual = message := receipt_lookup_eq setup implementation
              reference acceptBefore referenceTrace acceptPrior acceptPriorKept
                message actual messageInput lookup
            subst actual
            have handledCommit : EventGraphRuntime.handle implementation.runtime
                acceptBefore.execution.application.current.native
                  ⟨message.id, .commitment named handle⟩ = some acceptedNative := by
              simpa only [call] using handled
            have acceptedAtInclude : acceptedNative.accepted (.inr named) =
                some handle := by
              have tables := handle_commitment_tables implementation.runtime
                acceptBefore.execution.application.current.native acceptedNative
                  message.id named handle handledCommit
              rw [tables.2.1, Function.update_self]
            let acceptedTrace : (nativeProtocol).Trace (some acceptAfter) :=
              acceptPrior.extend acceptJoint acceptLegal acceptMoved
            by_cases sameInclude : acceptBefore.execution.application.attempt =
                acceptAfter.execution.application.attempt
            · have initialOrdered : ∀ state ∈ (nativeInitial).support, state.Ordered := by
                intro state member
                obtain ⟨draw, _supported, equal⟩ := PMF.support_map .. ▸ member
                cases equal
                exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
              have beforeOrdered :=
                (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
                  nativeInitial implementation.horizon implementation.scheduler initialOrdered
                    ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                      implementation.scheduler acceptPrior)
              have acceptedAfter : acceptAfter.execution.application.current.native.accepted
                  (.inr named) = some handle := by
                rw [normalized]
                apply PhaseRuntimeState.normalize_preserves_accepted
                  ({ acceptBefore.execution.application with current :=
                    (acceptBefore.execution.application.current.inclusionResult
                      message.payload.packet.call acceptedNative) } :
                    PhaseRuntimeState (serviceGraph setup .concurrent))
                    beforeOrdered (by rw [← normalized]; exact sameInclude)
                      (.inr named) handle
                exact acceptedAtInclude
              have afterRetained : TracePrefix acceptedTrace referenceTrace := acceptKept
              have goodAfter : ¬ PhaseProposal.GeneratedUnusableBindingHistory
                  implementation.runtime implementation.leaks implementation.bounds
                    nativeInitial implementation.horizon implementation.scheduler owner
                      ⟨some acceptAfter, acceptedTrace⟩ := by
                rintro ⟨badRecord, badMember, unusable⟩
                apply foreign owner foreignOwner
                exact ⟨badRecord,
                  (((nativeMenu).information nativeInitial implementation.horizon
                    implementation.scheduler).ownPlay_isSuffix_of_reachesWithin owner
                      afterRetained.reachesWithin).subset badMember, unusable⟩
              obtain ⟨acceptedValue, acceptedResult⟩ :=
                accepted_snapshot_value_of_no_generated_unusable setup implementation
                  acceptAfter acceptedTrace
                    acceptAfter.execution.application.current.native (Or.inl rfl)
                      owner goodAfter named payload shape handle acceptedAfter
              have acceptedStore : (⟨.inr named, shape⟩ : EventGraph.FieldRef
                  (serviceGraph setup .concurrent).layout (.binding owner payload)).get?
                    acceptAfter.execution.application.current.native.config.store =
                      some (.success acceptedValue) := by
                let actualTrace := (nativeMenu).toRawTrace nativeInitial
                  implementation.horizon implementation.scheduler acceptedTrace
                have valid := (phaseBindingRecord_history implementation.runtime
                  implementation.leaks implementation.plan
                    (setup.initialLaw.map encodeInputs) implementation.horizon
                      implementation.scheduler
                        ((show nativeInitial = (setup.initialLaw.map encodeInputs).map
                          (PhaseRuntimeState.initial implementation.plan) from
                            (by simp only [ReservedConcurrentImplementation.initial,
                              PMF.map_comp, Function.comp_def])) ▸ actualTrace)).active
                exact valid.toAssociationInvariant.opening_stored ⟨.inr named, shape⟩
                  handle acceptedValue acceptedAfter
                    ((State.bindingResult_eq_success_iff _ _ _ _).mp acceptedResult)
              obtain ⟨value, _openable, currentMeaning, _focal⟩ :=
                sourceHandleMeaning_of_accepted_binding setup values implementation
                  operational reference (sourceCutTrace setup implementation referenceTrace)
                    who event cut g sameInfo good choice
                    properChoice G supported acceptAfter
                    (sourceCutTrace setup implementation acceptedTrace)
                    (by
                      unfold sourceCutTrace
                      exact tracePrefix_initializer setup implementation _ afterRetained)
                      acceptAfter.execution.application.current.native (Or.inl rfl)
                        owner payload named shape handle acceptedValue acceptedAfter
                          acceptedStore
              have noMeaning : sourceHandleMeaning setup implementation G reference handle =
                  none := by simpa only [Option.map_none] using meaning
              rw [noMeaning] at currentMeaning
              cases currentMeaning
            · obtain ⟨ready, _timely, _actualOwner, _actualPayload,
                _actualBinding, _code, _node, _sender, _owner, _vacant, _unused⟩ :=
                handle_commitment_conditions implementation.runtime
                  acceptBefore.execution.application.current.native acceptedNative
                    message.id named handle handledCommit
              obtain ⟨phase, remaining, installed, commitment, inside⟩ :=
                phase_ready_binding_phase implementation.runtime implementation.leaks
                  implementation.plan
                    (serviceGraph_revealRelaxedOrdered setup .concurrent)
                      operational.maximalPhases (setup.initialLaw.map encodeInputs)
                        implementation.horizon implementation.scheduler
                          (by
                            have initialEq : (setup.initialLaw.map encodeInputs).map
                                (PhaseRuntimeState.initial implementation.plan) =
                                nativeInitial := by
                              simp only [ReservedConcurrentImplementation.initial,
                                PMF.map_comp, Function.comp_def]
                            rw [initialEq]
                            exact (nativeMenu).toRawTrace nativeInitial
                              implementation.horizon implementation.scheduler acceptPrior)
                            owner named payload shape ready
              let physical := acceptBefore.execution.application.current.inclusionResult
                message.payload.packet.call acceptedNative
              let rawState : PhaseRuntimeState (serviceGraph setup .concurrent) :=
                { acceptBefore.execution.application with current := physical }
              have rawNormalized : acceptAfter.execution.application = rawState.normalize :=
                normalized
              have changedRaw : rawState.normalize.attempt ≠ rawState.attempt := by
                rw [← rawNormalized]
                exact Ne.symm sameInclude
              have finishedRaw : phase.Finished (phase.drain physical) :=
                PhaseRuntimeState.finished_of_normalize_attempt_ne rawState phase
                  (by rw [installed]; exact Option.mem_some_iff.mpr rfl) changedRaw
              have acceptedDrained : (phase.drain physical).native.accepted (.inr named) =
                  some handle := by
                rw [(phase.drain_tables physical).1]
                exact acceptedAtInclude
              have actualEffect : PhaseClosingEffect implementation.runtime
                  implementation.leaks acceptBefore.execution acceptAfter.execution
                    physical :=
                Or.inl ⟨message.id, message, acceptedNative, lookup, included,
                  (by simpa only [call] using handledCommit), rfl⟩
              have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
                  (PhaseRuntimeState.initial implementation.plan) := by
                simp only [ReservedConcurrentImplementation.initial, PMF.map_comp,
                  Function.comp_def]
              have rawAcceptPrior : ((nativeApplication).protocol
                  ((setup.initialLaw.map encodeInputs).map
                    (PhaseRuntimeState.initial implementation.plan))
                    implementation.horizon implementation.scheduler).Trace
                      (some acceptBefore) := by
                rw [← initialEq]
                exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
                  implementation.scheduler acceptPrior
              have validBefore := (phaseBindingRecord_history implementation.runtime
                implementation.leaks implementation.plan
                  (setup.initialLaw.map encodeInputs) implementation.horizon
                    implementation.scheduler rawAcceptPrior).active
              have drainedValid : (phase.drain physical).native.BindingInvariant := by
                have nativeValid := handle_bindingInvariant implementation.runtime
                  acceptBefore.execution.application.current.native acceptedNative
                    ⟨message.id, .commitment named handle⟩ validBefore handledCommit
                have physicalValid : physical.native.BindingInvariant := by
                  simpa only [physical, RecoveryState.inclusionResult, call] using nativeValid
                exact phase.drain_bindingInvariant physical physicalValid
              obtain ⟨stampedNative, stampedHandle, _stampedNormalized,
                _stampedReceipts, stamped⟩ :=
                phase_inclusion_snapshot_bindingAccepted implementation.runtime
                  implementation.leaks implementation.plan
                    (setup.initialLaw.map encodeInputs) implementation.horizon
                      implementation.scheduler rawAcceptPrior message.id message lookup
                        acceptAfter.execution.application acceptedCall
              have stampedEq : stampedNative = acceptedNative :=
                Option.some.inj (stampedHandle.symm.trans
                  (by simpa only [call] using handledCommit))
              subst stampedNative
              have rawStamp : BindingStamp (fun actor =>
                  (nativeApplication).outputs (acceptBefore.execution.recall actor))
                    acceptBefore.execution.application.attempt
                      (phase.drain physical).native := by
                apply BindingStamp.copy stamped
                rw [(phase.drain_tables physical).1]
                rfl
              have actualVisit := completedVisits lost restricted acceptBefore acceptAfter
                acceptPrior acceptedTrace
                  (by
                    dsimp only [acceptedTrace]
                    exact TracePrefix.extend
                      (show TracePrefix acceptPrior acceptPrior from .refl)
                      acceptJoint acceptLegal acceptMoved)
                    acceptKept phase remaining installed physical rawNormalized finishedRaw
                      commitment actualEffect (Ne.symm sameInclude) drainedValid rawStamp
              obtain ⟨sourceLast, closed, labeled, fuel, targetFirst, targetLast,
                targetPrior, targetEnd, attemptEntry, attemptFinished, attemptExcluded,
                targetAttempt, targetMonotone, sourcePath, sourceWord, closedSelected,
                labeledKept, closedErase, targetInterval, targetEndToG,
                targetEndToFull, targetPriorDepth, targetEndDepth, targetPoint,
                targetAtCommit, targetEndpoint, targetWord, targetClosed,
                targetImage, referenceStamp⟩ := actualVisit
              have sourceClosedCut : TracePrefix closed
                  (setup.proposalRecoveryEraseTrace sourceCut.trace) := by
                rw [← closedErase]
                exact setup.proposalRecoveryEraseTrace_prefix
                  (labeledKept.trans canonicalToCut)
              let first := (checkpointSelection setup implementation operational
                acceptPrior).val.checkpoint
              let segment := SourceProgram.commitPhase first.residual.tail
              let embedding := cast (congrArg (fun program => OutputEmbedding
                (inputLayout setup.context) (outputLayout setup.program) program)
                  segment.reconstruct.symm) first.embedding
              let firstWitness := (checkpointSelection setup implementation operational
                acceptPrior).val
              have firstInstalled : phase ∈
                  acceptBefore.execution.application.phases.head? := by
                rw [installed]
                rfl
              have firstOrder :=
                (sourceReplayCloseEvidence setup implementation reference acceptBefore
                  acceptAfter referenceTrace acceptPrior acceptPriorKept firstWitness
                    phase firstInstalled commitment physical actualEffect
                      (Ne.symm sameInclude) rawStamp).1
              have eventBounds := (phase.mem_events named).mp inside
              have geometry := first.commit_phase_geometry phase remaining installed
                commitment firstWitness.receipts.exclusion.frontier
                  (operational.maximalPhases.suffix firstWitness.suffix)
              have slotBound : named.val - phase.low < segment.block.length := by
                rw [geometry.1]
                omega
              have entryTransport : cast (congrArg ProtocolState segment.reconstruct)
                    (ProtocolState.entry
                      (segment.block.prepend segment.suffix) attemptEntry) =
                  ProtocolState.entry first.residual.tail attemptEntry := by
                have transport {Γ : SourceCtx Player L} {O : Finset VarId}
                    {left right : SourceProgram Player L Γ O} (equal : left = right)
                    (entry : SourceProgram.Config Player L Γ) :
                    cast (congrArg ProtocolState equal) (ProtocolState.entry left entry) =
                      ProtocolState.entry right entry := by
                  cases equal
                  rfl
                exact transport segment.reconstruct attemptEntry
              have phaseLow : acceptBefore.execution.application.attempt.phase = phase.low := by
                simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
                  Option.map_some, Option.getD_some]
              have sourceStartRank : instructionCount setup.program -
                  instructionCount first.residual.tail = phase.low := by
                have starting := first.saved_position
                rw [first.remaining, ProtocolState.remaining_entry] at starting
                exact starting.trans phaseLow
              have targetStartRank : instructionCount setup.program -
                  ProtocolState.remaining setup.program targetFirst.point = phase.low := by
                rw [targetPoint]
                change instructionCount setup.program -
                    ProtocolState.remaining setup.program
                      (first.residual.lift
                        (cast (congrArg ProtocolState segment.reconstruct)
                          (ProtocolState.entry
                            (segment.block.prepend segment.suffix) attemptEntry))) = _
                rw [first.remaining, entryTransport, ProtocolState.remaining_entry]
                exact sourceStartRank
              have committing : ProtocolState.atCommit setup.program
                  targetFirst.point = true := by
                rw [targetPoint, first.atCommit, entryTransport]
                exact first.compiled.atCommit_of_bindingPhase setup.program .concurrent
                  first.residual.tail first.refs first.source.revelations first.registry
                    first.embedding first.before acceptBefore.execution.application.attempt.phase
                      phase commitment phaseLow.symm attemptEntry
              have suffixEnd : instructionCount setup.program -
                  instructionCount segment.suffix = phase.high := by
                have sourceWidth : instructionCount first.residual.tail =
                    segment.block.length + instructionCount segment.suffix := by
                  exact (congrArg instructionCount segment.reconstruct).symm.trans
                    (segment.block.instructionCount_prepend segment.suffix)
                have sourceBound := first.origin.instructionCount_le
                have blockLength : segment.block.length = phase.high - phase.low := geometry.1
                omega
              have targetSlot : named.val - phase.low < targetAttempt.joints.length := by
                rw [targetAttempt.joints_length]
                exact slotBound
              have targetPosition : named.val = instructionCount setup.program -
                  ProtocolState.remaining setup.program targetFirst.point +
                    (named.val - phase.low) := by
                rw [targetStartRank]
                omega
              have targetWithin : named.val < instructionCount setup.program -
                  ProtocolState.commitEnd setup.program targetFirst.saved := by
                change ProtocolState.commitEnd setup.program targetFirst.saved ≤
                  instructionCount segment.suffix at targetEndpoint
                omega
              obtain ⟨targetBefore, targetAfter, targetRow, targetJoint, targetLegal,
                targetMoved, targetKept, targetDepth, targetSemantic, targetSaved,
                targetGeneration, targetRank⟩ :=
                source_commit_chunk_at_rank setup targetFirst targetPrior committing
                  ⟨some targetLast, targetEnd⟩ targetInterval targetAttempt.joints
                    targetWord (named.val - phase.low) targetSlot named.val
                      targetPosition targetWithin
              have targetRowKept : TracePrefix
                  (targetRow.extend targetJoint targetLegal targetMoved) g.trace :=
                targetKept.trans targetEndToG
              have priorLength : targetPrior.length = first.trace.length := targetPriorDepth
              have targetLower : first.trace.length ≤ targetRow.length := by
                rw [targetDepth, priorLength]
                omega
              have targetUpper : targetRow.length < closed.length := by
                have wordLength := congrArg List.length targetWord
                simp only [setup.recoveryJointRecall_length,
                  setup.proposalRecoveryEraseTrace_length, List.length_append,
                  List.length_reverse] at wordLength
                rw [targetEndDepth, priorLength] at wordLength
                rw [targetDepth, priorLength]
                omega
              obtain ⟨sourceBefore, sourceAfter, sourceRow, sourceJoint,
                sourceLegal, sourceMoved, sourceKept, sourceDepth, sourceBeforeInfo,
                sourceAfterInfo, sourceOwn, sourceSaved, sourceGeneration,
                sourcePhysical, transported, successful, failed⟩ :=
                sourceReplayPhysicalPairedRow setup first (phase.drain physical).native
                  ⟨some sourceLast, closed⟩ sourcePath sourceWord who sourceCut g
                    sourceClosedCut cutInfo cutGood good targetBefore targetAfter
                      targetRow targetJoint targetLegal targetMoved targetRowKept
                        named owner payload shape targetRank.symm targetLower targetUpper
              have sourceLower : first.trace.length ≤ sourceRow.length := by
                rw [sourceDepth]
                exact targetLower
              have sourceUpper : sourceRow.length < closed.length := by
                rw [sourceDepth]
                exact targetUpper
              obtain ⟨_decodedSaved, _decodedGeneration, decodedRow⟩ :=
                source_decoded_binding_row setup first (phase.drain physical).native
                  ⟨some sourceLast, closed⟩ sourcePath sourceWord sourceCut
                    sourceClosedCut sourceBefore sourceAfter sourceRow sourceJoint
                      sourceLegal sourceMoved sourceKept sourceLower sourceUpper
              dsimp only [segment] at decodedRow
              obtain ⟨decodedEvent, decodedOwner, decodedPayload, decodedBinding,
                decodedPosition, receiptActive, _decodedData⟩ := decodedRow
              have metadata := source_information_metadata setup who
                ⟨some sourceBefore, sourceRow⟩ ⟨some targetBefore, targetRow⟩
                  sourceBeforeInfo
              have controls := ProtocolState.MetadataEq.controls setup.program
                sourceBefore.point targetBefore.point metadata.1
              have sourceRank : named.val = instructionCount setup.program -
                  ProtocolState.remaining setup.program sourceBefore.point := by
                rw [controls.1]
                exact targetRank.symm
              have decodedEq : decodedEvent = named :=
                Fin.ext (decodedPosition.trans sourceRank.symm)
              have decodedOwnerEq : decodedOwner = owner :=
                (EventField.binding.inj (decodedBinding.symm.trans
                  (decodedEq.symm ▸ shape))).1
              have sourceActive : owner ∉ sourceBefore.excluded := by
                have acceptedDecoded : (phase.drain physical).native.accepted
                    (.inr decodedEvent) ≠ none := by
                  rw [decodedEq, acceptedDrained]
                  exact Option.some_ne_none handle
                rw [phaseLow] at receiptActive
                have active := receiptActive firstOrder acceptedDecoded
                rw [decodedOwnerEq] at active
                exact active
              have sourceData := sourcePhysical sourceActive
              rw [acceptedDrained] at sourceData
              simp only [Option.elim_some, Option.isNone_some] at sourceData
              have sourceAfterActive : owner ∉ sourceAfter.excluded := by
                intro omitted
                have missing := (source_binding_missing_iff setup sourceBefore
                  sourceAfter sourceJoint sourceLegal sourceMoved owner named payload
                    shape sourceRank sourceActive).mpr omitted
                rw [sourceData] at missing
                cases missing
              have sourceRowGood := source_good_prefix setup who
                (sourceRow.extend sourceJoint sourceLegal sourceMoved) sourceCut.trace
                  sourceKept cutGood
              obtain ⟨sourceValue, sourceSuccess⟩ :=
                source_foreign_binding_success setup who owner
                  foreignOwner named payload shape
                    sourceBefore sourceRow sourceJoint sourceLegal sourceAfter
                      sourceMoved sourceRank sourceActive sourceAfterActive sourceRowGood
              obtain ⟨value, _readAtG, targetData⟩ :=
                successful sourceActive sourceValue sourceSuccess
              have targetGenerationAt : targetBefore.generation =
                  acceptBefore.execution.application.attempt.generation := by
                rw [← metadata.2.2.2.2]
                simpa only [PhaseRuntimeState.attempt] using sourceGeneration
              have targetSavedAt : instructionCount setup.program -
                  ProtocolState.remaining setup.program targetBefore.saved =
                    acceptBefore.execution.application.attempt.phase := by
                rw [← (ProtocolState.MetadataEq.controls setup.program
                  sourceBefore.saved targetBefore.saved metadata.2.1).1,
                    sourceSaved, first.saved_position]
              have gToG : TracePrefix g.trace G.trace := by
                have support := supported
                unfold sourceForcedBlock at support
                obtain ⟨middle, firstStep, laterSteps⟩ :=
                  (PMF.mem_support_bind_iff ..).mp support
                exact (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
                  _ 1 g middle firstStep).tracePrefix.trans
                    (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
                      _ _ middle G laterSteps).tracePrefix
              refine ⟨value, ?_⟩
              rw [acceptedAttempt]
              exact sourceBindingAt_of_origin setup
                acceptBefore.execution.application.attempt named owner payload shape
                  targetBefore targetRow targetJoint targetLegal (some targetAfter)
                    targetMoved targetGenerationAt targetSavedAt targetRank
                      (.success value, false) targetData G.trace
                        (targetRowKept.trans gToG)
          obtain ⟨value, present⟩ := acceptedRow acceptedReceipt
          rw [read] at present
          cases present
        have noReceiptHandle : ¬ PhaseService.BindingAccepted implementation.runtime
            implementation.leaks ⟨message.payload.attempt, named⟩ handle.1
              reference.execution := by
          rw [handleOwner]
          exact noReceipt
        have noMeaning : sourceHandleMeaning setup implementation G reference handle =
            none := by
          simpa only [Option.map_none] using meaning
        refine Or.inr ⟨noMeaning, historical, ?_⟩
        intro other value selectedValue
        by_cases sameHandle : other = handle
        · subst other
          have sameRaw : raw = value := by
            simpa only [Function.update_self, Option.some.injEq] using selectedValue
          subst value
          refine ⟨?_, preparedHandle, noMeaning, record, message, named,
            payload, old, recordedHandle, emitted, ?_, call, historical,
              (by simpa only [handleOwner] using shape), rawShape, prepared, noReceiptHandle⟩
          · intro own
            exact foreignOwner (handleOwner.symm.trans own)
          · exact sender.trans handleOwner.symm
        · have oldValue : lost other = some value := by
            simpa only [Function.update_of_ne sameHandle] using selectedValue
          exact restricted other value oldValue


end Vegas.PhaseProposalQualifiedBinding

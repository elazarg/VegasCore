/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalQualifiedBinding
import Vegas.Game.PhaseCommitmentProposalArchive
import Vegas.Game.PhaseProposalAttemptArchive
import Vegas.Game.PhaseProposalCoupledQuery
import Vegas.EventGraph.ReadySemanticStability
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseReadyBindingDeclaration
import Vegas.Game.PhaseProposalBindingSettlement
import Vegas.Game.PhaseProposalArchiveBounds
import Vegas.Game.PhaseProposalBucket
import Interaction.ReactiveAnchoredStopped
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # Clean binding comparisons at the original native information

The native continuation uses the original scheduler and ordinary value table.
An owner waiting at a retained ready binding reads the same normalized source
query when offered that binding again. Foreign receipt opportunities are read
from the actual reserved-service word, independently of the inserted value.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan) inputs

private theorem closing_binding_frame
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some before))
    (phase : RuntimePhase (graph)) (raw : RecoveryState (graph))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt) :
    BindingStamp (fun owner => (app).outputs (before.execution.recall owner))
        before.execution.application.attempt (phase.drain raw).native ∧
      (∀ candidate payload, (phase.drain raw).native.bindingResult candidate payload =
        before.execution.application.current.native.bindingResult candidate payload) ∧
      (∀ field value, before.execution.application.current.native.config.store field = some value →
        (phase.drain raw).native.config.store field = some value) := by
  have rawTrace := (menu).toRawTrace initial horizon scheduler trace
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler
    rawTrace
  have frame : BindingStamp (fun owner => (app).outputs (before.execution.recall owner))
        before.execution.application.attempt raw.native ∧
      (∀ candidate payload, raw.native.bindingResult candidate payload =
        before.execution.application.current.native.bindingResult candidate payload) ∧
      (∀ field value, before.execution.application.current.native.config.store field = some value →
        raw.native.config.store field = some value) := by
    rcases effect with included | applied
    · obtain ⟨id, message, native, found, stepped, handled, rfl⟩ := included
      have accepted : ∃ next, before.execution.application.handle runtime message = some next := by
        cases selected : before.execution.application.handle runtime message with
        | some next => exact ⟨next, rfl⟩
        | none =>
            have literal := stepped
            simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at literal
            have equal := congrArg (fun execution : (app).Execution => execution.application)
              ((PMF.mem_support_pure_iff _ _).mp literal)
            have unchanged : ending.execution.application = before.execution.application := by
              simpa only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found,
                show (app).handle before.execution.application message = none from selected,
                Option.getD_none] using equal
            exact (changed (congrArg PhaseRuntimeState.attempt unchanged)).elim
      obtain ⟨next, accepted⟩ := accepted
      have current := PhaseRuntimeState.handle_attempt_eq runtime before.execution.application next
        message accepted
      have issued := ((app).history_provenance initial horizon scheduler rawTrace).lookup id message
        found
      exact ⟨raw_handle_bindingStamp runtime leaks before.execution native message stamped issued
        current handled, raw_handle_bindingResult runtime _ native _ handled,
        handle_store_of_some runtime _ native _ handled⟩
    · obtain ⟨command, native, _stepped, supported, rfl⟩ := applied
      refine ⟨stamped.copy (environmentStep_tables runtime _ native command supported).1, ?_,
        environmentStep_store_of_some runtime _ native command supported⟩
      intro candidate payload
      change native.bindingResult candidate payload = _
      unfold State.bindingResult
      rw [(environmentStep_tables runtime _ native command supported).2]
  refine ⟨frame.1.copy (phase.drain_tables raw).1, ?_, ?_⟩
  · intro candidate payload
    unfold State.bindingResult
    rw [(phase.drain_tables raw).2.1]
    exact frame.2.1 candidate payload
  · intro field value present
    exact phase.drain_keepsStore raw field value (frame.2.2 field value present)

private theorem closing_recorded_binding_material
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some before))
    (phase : RuntimePhase (graph)) (raw : RecoveryState (graph))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (owner : Player) (event : (graph).EventId) (inside : event ∈ phase.events)
    (payload : L.Ty) (binding : (graph).outputLayout event = .binding owner payload)
    (lower : before.execution.application.attempt.phase ≤ event.val)
    (surviving : owner ∉ (phase.drain raw).excluded)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest (graph))
    (entry : (app).PlayerEntry) (recorded : entry ∈ before.execution.recall owner)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (sameAttempt : entry.beforeView.application.2.attempt = before.execution.application.attempt) :
    (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
        (phase.drain raw).native.config.store =
      some ((opening.bind fun value => value.as? payload).elim .failure
        PublicationResult.success) := by
  let material : WitnessedSubmission (graph) :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
  have sent : entry.action.transmission = some material := by rw [declared]
  have rawTrace := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨_native, bindingRecord, _receipts, _stored, _remembered, coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending trace raw effect changed
  have bindings := phase.drain_bindingInvariant raw bindingRecord.active
  have covered := coverage.active.drain phase
  obtain ⟨stamp, results, _stores⟩ := closing_binding_frame setup mode runtime leaks bounds plan
    horizon scheduler before ending trace phase raw effect changed
  have present : (phase.drain raw).native.accepted (.inr event) ≠ none := by
    intro missing
    exact surviving (covered.covered event owner
      (actor?_of_outputLayout_binding (graph) binding) (Or.inl
        (((phase.drain raw).native.publicView_missedBinding event owner payload binding).mpr
          ⟨finished inside, missing⟩)))
  obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
  obtain ⟨otherPayload, candidateLayout⟩ := bindings.accepted_typed (.inr event) candidate accepted
  have owned : candidate.1 = owner :=
    (EventField.binding.inj (candidateLayout.symm.trans binding)).1
  rcases stamp event candidate accepted with earlier |
      ⟨original, originalOutput, originalSender, originalCall, originalAttempt⟩
  · omega
  · obtain ⟨message, emitted, messageOwner, messageCall⟩ :=
      PhaseCount.recalled_submission_emitted runtime leaks initial horizon scheduler rawTrace
        owner entry recorded material sent
    have attempt := phase_recalled_emission_attempt runtime leaks initial horizon scheduler
      rawTrace owner entry recorded message emitted
    have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
      initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
    have output : message ∈ (app).outputs (before.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
    rw [owned] at originalOutput
    change original ∈ (app).outputs (before.execution.recall owner) at originalOutput
    have originalInput : original ∈ before.execution.network.inputs := by
      rw [← clean.1.1 owner] at originalOutput
      exact (List.mem_filter.mp originalOutput).1
    have messageInput : message ∈ before.execution.network.inputs := by
      rw [← clean.1.1 owner] at output
      exact (List.mem_filter.mp output).1
    have sameEvent : PhaseCount.event? original.payload = PhaseCount.event? message.payload := by
      simp only [PhaseCount.event?, originalCall, messageCall, material, Payload.event?,
        Option.map_some, originalAttempt, attempt, sameAttempt]
    have same := PhaseCount.Permits.eq_of_same_event
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 original originalInput))
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message messageInput))
      originalInput messageInput
      (fun first firstInput second secondInput ids =>
        (app).input_identifier_injective_history initial horizon scheduler before rawTrace
          first second firstInput secondInput ids)
      ((originalSender.trans owned).trans messageOwner.symm) sameEvent
    have candidateEq : candidate = (owner, .prepared serial) := by
      have calls := congrArg (fun value : Message Player (CommitAttemptPacket (graph)) =>
        value.payload.packet.call) same
      rw [originalCall, messageCall] at calls
      exact (Payload.commitment.inj calls).2
    obtain ⟨origin, prior, _kept, _acting, viewed, offered, _past⟩ :=
      (menu).recorded_response_prefix initial horizon scheduler before trace owner entry recorded
    rw [declared] at offered
    have fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh :=
      viewed ▸ PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon
        scheduler prior owner event serial opening evidence offered
    have meaning := phase_recorded_material_binding_result runtime leaks menu initial horizon
      scheduler before trace owner event payload serial opening evidence entry recorded declared
        fresh
    have read := bindings.binding_read
      (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)) event rfl
      (finished inside)
    rw [accepted, Option.elim_some, candidateEq, results, meaning] at read
    exact read

private theorem closing_binding_declaration
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some before))
    (phase : RuntimePhase (graph)) (raw : RecoveryState (graph))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (owner : Player) (event : (graph).EventId) (inside : event ∈ phase.events)
    (payload : L.Ty) (binding : (graph).outputLayout event = .binding owner payload)
    (lower : before.execution.application.attempt.phase ≤ event.val)
    (surviving : owner ∉ (phase.drain raw).excluded) :
    ∃ (remaining : Nat) (execution : (app).Execution)
      (prior : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
      (record : (app).PlayerEntry)
      (post : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond app owner record.action⟩))
      (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest (graph)),
      TracePrefix prior post ∧ TracePrefix post trace ∧ post.length = prior.length + 1 ∧
      record ∈ (execution.respond app owner record.action).recall owner ∧
      record.beforeView = execution.observe app owner ∧
      record.action =
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      record.beforeView.application.2.attempt = before.execution.application.attempt ∧
      execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩ ∧
      (∀ message ∈ (app).outputs (execution.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) ∧
      (∃ later, before.execution.recall owner = execution.recall owner ++ record :: later) ∧
      (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
          (phase.drain raw).native.config.store =
        some ((opening.bind fun value => value.as? payload).elim .failure
          PublicationResult.success) := by
  have rawTrace := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨_native, records, _receipts, _stored, _remembered, coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending trace raw effect changed
  have bindings := phase.drain_bindingInvariant raw records.active
  obtain ⟨stamp, _results, _stores⟩ := closing_binding_frame setup mode runtime leaks bounds plan
    horizon scheduler before ending trace phase raw effect changed
  have present : (phase.drain raw).native.accepted (.inr event) ≠ none := by
    intro missing
    exact surviving ((coverage.active.drain phase).covered event owner
      (actor?_of_outputLayout_binding (graph) binding) (Or.inl
        (((phase.drain raw).native.publicView_missedBinding event owner payload binding).mpr
          ⟨finished inside, missing⟩)))
  obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
  obtain ⟨otherPayload, typed⟩ := bindings.accepted_typed (.inr event) candidate accepted
  have owned : candidate.1 = owner :=
    (EventField.binding.inj (typed.symm.trans binding)).1
  rcases stamp event candidate accepted with earlier |
      ⟨message, output, sender, named, attempted⟩
  · omega
  · rw [owned] at output
    have input : message ∈ before.execution.network.inputs := by
      change message ∈ (app).outputs (before.execution.recall owner) at output
      rw [← (app).history_inputRecall initial horizon scheduler rawTrace owner] at output
      exact (List.mem_filter.mp output).1
    obtain ⟨record, recorded, material, sent, emitted, state, known, packet⟩ :=
      ((app).history_provenance initial horizon scheduler rawTrace).inputs message input
    rw [sender.trans owned] at recorded
    have materialCall : material.call.packet = .commitment event candidate := by
      have exactCall := phase_emit_call state message.sender known material
      change state.emit message.sender known material = message.payload at packet
      exact exactCall.symm.trans
        ((congrArg (fun payload => payload.packet.call) packet).trans named)
    obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp recorded
    obtain ⟨remaining, execution, prior, post, kept, past, viewed, offered, beforePost, length⟩ :=
      (menu).recorded_response_after initial horizon scheduler before trace owner earlier record
        later recalled
    have action : record.action = (⟨some material⟩ : (app).Action) := by
      cases selected : record.action with
      | mk transmission =>
          rw [selected] at sent
          exact congrArg ReactiveApplication.Action.mk sent
    have allowed := offered
    rw [action] at allowed
    obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
      plan inputs horizon scheduler remaining owner execution prior material allowed
    have sameEvent := PhaseCount.onePacket_event_of_request runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
        execution prior coordinate request material allowed
    rw [materialCall] at sameEvent
    have eventEq : coordinate.event = event := (Option.some.inj sameEvent).symm
    have coordinateEq : coordinate = ⟨execution.application.attempt, event⟩ := by
      cases coordinate
      exact congrArg₂ CommitAttemptEvent.mk request.1 eventEq
    rw [coordinateEq] at request
    obtain ⟨serial, opening, evidence, materialEq, _bounded, _fresh⟩ :=
      PhaseCount.onePacket_binding_shape runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
        execution prior event payload binding request material allowed
    have declared := action.trans (congrArg (fun material =>
      (⟨some material⟩ : (app).Action)) materialEq)
    have sameAttempt := (phase_recalled_emission_attempt runtime leaks initial horizon scheduler
      rawTrace owner record recorded message emitted).symm.trans attempted
    have postMember : record ∈ (execution.respond app owner record.action).recall owner := by
      obtain ⟨actualEmitted, postRecall⟩ := (app).respond_recall_entry execution owner record.action
      have retained := (app).reaches_recall_prefix initial horizon scheduler
        ((menu).reaches_raw initial horizon scheduler kept.reachesWithin)
        ⟨remaining, none, execution.respond app owner record.action⟩ before rfl rfl owner
      rw [postRecall, past, recalled] at retained
      have heads := (List.prefix_append_right_inj earlier).mp retained
      obtain ⟨_rest, same, _tail⟩ := List.cons_prefix_iff.mp heads
      rw [postRecall, (List.cons.inj same).1]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    refine ⟨remaining, execution, prior, record, post, serial, opening, evidence,
      beforePost, kept, length, postMember, viewed, declared, sameAttempt, request, ?_, ?_, ?_⟩
    · exact PhaseCount.unsent_of_nonsilent runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
          execution prior _ request material allowed
    · exact ⟨later, by rwa [past]⟩
    · exact closing_recorded_binding_material setup mode runtime leaks bounds plan horizon scheduler
        before ending trace phase raw effect changed finished owner event inside payload binding
          lower surviving serial opening evidence record recorded declared sameAttempt

private theorem table_binding_preparation
    (covered : bounds.CoversOutputValues)
    (table : ∀ index : (who : Player) × setup.ProposalRecoveryComponent who,
      setup.CommitRecoveryValueChoice index.1 index.2.1)
    (scheduler : (app).Scheduler)
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((menu).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      (ReservedEpoch.executionHorizon runtime) scheduler).Trace
        (some ⟨remaining, some who, execution⟩))
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent who)
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event (execution.recall who)
      (execution.observe app who) = some key)
    (response : (app).Action)
    (supported : response ∈
      (PhaseProposalQualifiedBinding.baseAliasPolicy setup mode runtime leaks bounds plan
        (PhaseProposalQualifiedBinding.tableValues setup table) PhaseProposalRates.zero who
        (execution.recall who) (execution.observe app who)).support) :
    response.transmission.bind PhaseProposal.bindingPreparation =
      some (⟨payload, phaseRecoveryDomainValue setup mode event who payload binding
        (table ⟨who, key⟩).val.val⟩ : Raw L) := by
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  have counted : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime) scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := initialEq.symm ▸ trace
  obtain ⟨kernel, laws, prepared⟩ := PhaseProposalQualifiedBinding.baseAliasPolicy_binding_kernel
    setup mode runtime leaks bounds plan covered scheduler capacity remaining who execution counted
      event payload binding request unsent key queried
  have atCoordinate : response ∈ (kernel (table ⟨who, key⟩)).support := by
    rw [laws] at supported
    simpa only [PhaseProposalQualifiedBinding.tableValues, PMF.pure_bind] using supported
  obtain ⟨_covered, material, sent, meaning⟩ := prepared _ _ atCoordinate
  simpa only [sent, Option.bind_some] using meaning

private theorem table_stopped_consistent
    (table : ∀ index : (who : Player) × setup.ProposalRecoveryComponent who,
      setup.CommitRecoveryValueChoice index.1 index.2.1)
    (scheduler : (app).Scheduler) (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      scheduler).Trace (some anchor))
    (stopped : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      scheduler).History → Prop) :
    let horizon := ReservedEpoch.executionHorizon runtime
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let players := PhaseProposalQualifiedBinding.baseAliasPolicy setup mode runtime leaks bounds
      plan (PhaseProposalQualifiedBinding.tableValues setup table) PhaseProposalRates.zero
    ∀ final ∈ (model.runBehavioralUntil certificate
        (PhaseProposalQualifiedBinding.baseAliasStrategy setup mode runtime leaks bounds plan
          (PhaseProposalQualifiedBinding.tableValues setup table) scheduler PhaseProposalRates.zero)
        stopped ⟨some anchor, anchorTrace⟩).support,
      ReactiveApplication.executionInvariant
        (fun execution => ∀ who,
          (ReactiveApplication.anchoredPolicy anchor.execution players who).Consistent
            (execution.recall who)) final.state := by
  classical
  intro horizon model certificate players
  let anchored := ReactiveApplication.anchoredPolicy anchor.execution players
  let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (anchored who)
  let original := PhaseProposalQualifiedBinding.baseAliasStrategy setup mode runtime leaks bounds
    plan (PhaseProposalQualifiedBinding.tableValues setup table) scheduler PhaseProposalRates.zero
  have covered : ∀ who past view action, action ∈ (anchored who past view).support →
      action ∈ (menu).actions who past view := by
    intro who
    apply (menu).anchoredPolicy_covered initial horizon scheduler anchor anchorTrace players who
    intro past view action supported
    obtain ⟨response, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact response.property
  have same : model.runBehavioralUntil certificate profile stopped ⟨some anchor, anchorTrace⟩ =
      model.runBehavioralUntil certificate original stopped ⟨some anchor, anchorTrace⟩ := by
    apply model.runBehavioralUntil_congr certificate stopped ⟨some anchor, anchorTrace⟩
    intro later reached _running who
    obtain ⟨fuel, path⟩ := reached
    rcases later with ⟨state, laterTrace⟩
    have observed := (menu).info initial horizon scheduler who laterTrace
    change model.infoOf who laterTrace = (app).observe who state at observed
    cases state with
    | none => rw [observed]; rfl
    | some current =>
        by_cases active : current.actor = some who
        · have extendsRecall := (app).reaches_recall_prefix initial horizon scheduler
            ((menu).reaches_raw initial horizon scheduler path) anchor current rfl rfl who
          simp only [ReactiveApplication.observe, active, ite_true] at observed
          rw [observed]
          apply (menu).restrictPolicy_eq_of_law_eq initial horizon scheduler who
          exact ReactiveApplication.anchoredPolicy_of_extends anchor.execution players who _ _
            extendsRecall
        · simp only [ReactiveApplication.observe, active, ite_false] at observed
          rw [observed]
          rfl
  let predicate := fun execution : (app).Execution =>
    ∀ who, (anchored who).Consistent (execution.recall who)
  have invariant := ReactiveApplication.consistentRecall_policyInvariant anchored
  have preserved : ∀ history, ¬ stopped history →
      ¬ ((menu).protocol initial horizon scheduler).terminal history.state →
      ReactiveApplication.executionInvariant predicate history.state →
      ∀ next ∈ (model.runBehavioralFrom profile 1 history).support,
        ReactiveApplication.executionInvariant predicate next.state := by
    intro history _running _notTerminal faithful next supported
    have mapped := (menu).run_restrict_control_steps initial horizon scheduler anchored
      ((menu).admissible_of_covered initial horizon scheduler anchored covered) 1 history
    simp only [Function.iterate_one, PMF.pure_bind] at mapped
    have actual : next.state ∈
        ((model.runBehavioralFrom profile 1 history).map History.state).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨next, supported, rfl⟩
    rw [mapped] at actual
    exact invariant.controlStep initial horizon scheduler (fun _ _ _ => .nil)
      history.state next.state faithful actual
  have faithful : ReactiveApplication.executionInvariant predicate (some anchor) := by
    intro who
    exact ReactiveApplication.anchoredPolicy_consistent anchor.execution players who
  intro final supported
  rw [← same] at supported
  exact model.runBehavioralUntil_support_history_closed certificate profile stopped
    (fun history => ReactiveApplication.executionInvariant predicate history.state) preserved
      ⟨some anchor, anchorTrace⟩ faithful final supported

private theorem binding_waiting_semantics
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (readyBefore : before.execution.application.current.native.config.cut.Ready event)
    (readyAfter : after.execution.application.current.native.config.cut.Ready event) :
    (graph).playerStore who after.execution.application.current.native.config.store =
        (graph).playerStore who before.execution.application.current.native.config.store ∧
      (graph).ownCompletions who after.execution.application.current.native.config.history =
        (graph).ownCompletions who before.execution.application.current.native.config.history := by
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have rawBefore := (menu).toRawTrace initial horizon scheduler prior
  have rawAfter := (menu).toRawTrace initial horizon scheduler trace
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized rawBefore
  have progress := phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
    before after prior trace kept ordered same
  obtain ⟨first, firstValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler rawBefore
  obtain ⟨last, lastValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler rawAfter
  have inputEq : before.execution.application.current.native.config.inputs =
      after.execution.application.current.native.config.inputs := by
    funext input
    exact (Option.some.inj (progress.1 (.inl input)
      (before.execution.application.current.native.config.inputs input) rfl)).symm
  have firstReached : before.execution.application.current.native.config.Reachable
      before.execution.application.current.native.config.inputs := by
    simpa only [firstValid.active.reachable.inputs_eq] using firstValid.active.reachable
  have lastReached : after.execution.application.current.native.config.Reachable
      before.execution.application.current.native.config.inputs := by
    rw [inputEq]
    simpa only [lastValid.active.reachable.inputs_eq] using lastValid.active.reachable
  have notPublication : ¬ ((graph).outputLayout event).IsPublication := by
    change ¬ (setup.eventGraph.outputLayout event).IsPublication
    have semanticBinding : setup.eventGraph.outputLayout event = .binding who payload := binding
    rw [semanticBinding]
    exact id
  exact (serviceGraph_revealRelaxedOrdered setup mode).ready_semantics_eq_of_extension
    before.execution.application.current.native.config
    after.execution.application.current.native.config firstReached lastReached who event
    readyBefore readyAfter ((graph).actor?_of_outputLayout_binding binding) notPublication
      progress.1 progress.2

/-- At two actual offers of the same still-ready binding, every argument of
the ordinary source getter is unchanged. New in-attempt foreign misses are
normalized at the saved boundary, including misses learned between the offers.
No equality of raw recall, physical clocks or private catalogues is required. -/
theorem phaseProposal_query_eq_at_retained_binding
    (complete : leaks = MessageNetwork.completePendingObservation)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (activeBefore : before.actor = some who) (activeAfter : after.actor = some who)
    (requestBefore : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩)
    (requestAfter : after.execution.application.SeedRequest who
      ⟨after.execution.application.attempt, event⟩) :
    phaseProposalQuery? setup mode runtime leaks plan who event
        (after.execution.recall who) (after.execution.observe app who) =
      phaseProposalQuery? setup mode runtime leaks plan who event
        (before.execution.recall who) (before.execution.observe app who) := by
  classical
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have rawBefore := (menu).toRawTrace initial horizon scheduler prior
  have rawAfter := (menu).toRawTrace initial horizon scheduler trace
  have orderedBefore := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized rawBefore
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler before after prior trace kept orderedBefore same
  have retired := congrArg Prod.snd metadata
  change before.execution.application.retired = after.execution.application.retired at retired
  have saved := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler before after prior trace kept orderedBefore).2.2 same
  obtain ⟨phase, rest, installed, commitment, _inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler rawBefore
      who event payload binding requestBefore.2.2.1
  have frontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_frontier plan draw) rawBefore
  have savedPrefix : before.execution.application.entry.native.config.cut.IsPrefix phase.low := by
    have positioned := frontier.positioned
    rw [installed] at positioned
    exact positioned.1
  have low : before.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have failuresBefore := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler rawBefore
  have failuresAfter := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler rawAfter
  have failedPrefix : ∀ rank ≤ before.execution.application.attempt.phase,
      before.execution.application.current.native.failureOwnersBefore rank =
        after.execution.application.current.native.failureOwnersBefore rank := by
    intro rank bounded
    have first := failuresBefore.failureOwnersBefore_eq_below phase.low
      (fun event earlier => (savedPrefix.2 event).mpr earlier) rank (by omega)
    have second := failuresAfter.failureOwnersBefore_eq_below phase.low
      (fun event earlier => by rw [← saved]; exact (savedPrefix.2 event).mpr earlier)
      rank (by omega)
    rw [← first, ← second, ← saved]
  have semantics := binding_waiting_semantics setup mode runtime leaks bounds plan horizon
    scheduler before after prior trace kept same who event payload binding requestBefore.2.2.1
      requestAfter.2.2.1
  have archive := PhaseProposal.phase_commitment_prefix_sourceArchive runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before prior phase
      (by simp only [installed, List.head?_cons, Option.mem_some_iff]) commitment trace kept (by
        intro middle middleTrace first last _strict
        have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
          initialized ((menu).toRawTrace initial horizon scheduler middleTrace)
        have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler before middle prior middleTrace first orderedBefore
        have upper := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler middle after middleTrace trace last ordered
        have sameGeneration := congrArg CommitAttemptId.generation same
        have samePhase := congrArg CommitAttemptId.phase same
        cases firstAttempt : before.execution.application.attempt with
        | mk firstPhase firstGeneration =>
          cases middleAttempt : middle.execution.application.attempt with
          | mk middlePhase middleGeneration =>
            cases finalAttempt : after.execution.application.attempt with
            | mk finalPhase finalGeneration =>
              simp only [firstAttempt, middleAttempt, finalAttempt]
                at lower upper sameGeneration samePhase ⊢
              congr 1 <;> omega)
  obtain ⟨ending, endingEq, archiveEq⟩ := archive
  cases Option.some.inj endingEq
  have beforeArchive := PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete
    initial horizon scheduler before rawBefore who activeBefore
  have afterArchive := PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete
    initial horizon scheduler after rawAfter who activeAfter
  apply phaseProposalQuery?_eq_of_masked_prefix setup mode runtime leaks plan who event
    (after.execution.recall who) (before.execution.recall who)
    (after.execution.observe app who) (before.execution.observe app who) rfl rfl
  · exact semantics.1
  · exact same.symm
  · change after.execution.application.retired.map _ =
      before.execution.application.retired.map _
    rw [← retired]
  · intro rank bounded
    change rank ≤ after.execution.application.attempt.phase at bounded
    change after.execution.application.current.native.publicView.sourceFailureFootprint.1 rank =
      before.execution.application.current.native.publicView.sourceFailureFootprint.1 rank
    rw [State.sourceFailureFootprint_read, State.sourceFailureFootprint_read]
    exact (failedPrefix rank (by rw [same]; exact bounded)).symm
  · rw [beforeArchive, afterArchive, archiveEq]

/-- The later ordinary declaration uses the literal same value law as an
immediate declaration. Raw handle and certificate choices are retained on the
native side; this equality projects only the prepared typed value. -/
theorem phaseProposal_unflagged_value_law_at_retained_binding
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (activeBefore : before.actor = some who) (activeAfter : after.actor = some who)
    (requestBefore : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩)
    (requestAfter : after.execution.application.SeedRequest who
      ⟨after.execution.application.attempt, event⟩)
    (unsentBefore : ∀ message ∈ (app).outputs (before.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩)
    (unsentAfter : ∀ message ∈ (app).outputs (after.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨after.execution.application.attempt, event⟩) :
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
      (after.execution.recall who) (after.execution.observe app who)).map
        (fun response => response.transmission.bind PhaseProposal.bindingPreparation) =
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
        (before.execution.recall who) (before.execution.observe app who)).map
          (fun response => response.transmission.bind PhaseProposal.bindingPreparation) := by
  have beforeCallback : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some who, before.execution⟩) := by
    simpa only [← activeBefore] using prior
  have afterCallback : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨after.remaining, some who, after.execution⟩) := by
    simpa only [← activeAfter] using trace
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  obtain ⟨first, firstQuery, firstLaw⟩ := phaseProposalUnflaggedBinding_preparation_law setup mode
    runtime leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      before.remaining who before.execution (initialEq ▸ beforeCallback) event payload binding
        requestBefore unsentBefore
  obtain ⟨last, lastQuery, lastLaw⟩ := phaseProposalUnflaggedBinding_preparation_law setup mode
    runtime leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      after.remaining who after.execution (initialEq ▸ afterCallback) event payload binding
        requestAfter unsentAfter
  have query := phaseProposal_query_eq_at_retained_binding setup mode runtime leaks bounds plan
    complete maximal horizon scheduler before after prior trace kept same who event payload binding
      activeBefore activeAfter requestBefore requestAfter
  have keys : last = first := Option.some.inj
    (lastQuery.symm.trans (query.trans firstQuery))
  cases keys
  exact lastLaw.trans firstLaw.symm

/-- A common value table gives the same typed completed commitment word when
both actual first-close images retain precisely the original entry exclusions.
The comparison keeps the original pending packets and both raw closing effects. -/
private theorem table_closing_binding_values_eq
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (table : ∀ index : (who : Player) × setup.ProposalRecoveryComponent who,
      setup.CommitRecoveryValueChoice index.1 index.2.1)
    (scheduler : (app).Scheduler)
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (focal : Player) (execution : (app).Execution)
    (hTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime) scheduler).Trace
      (some ⟨remaining, some focal, execution⟩))
    (waitTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime) scheduler).Trace
      (some ⟨remaining, none, execution.respond app focal ⟨none⟩⟩))
    (waitKept : TracePrefix hTrace waitTrace)
    (phase : RuntimePhase (graph)) (installed : phase ∈ execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (leftBefore rightBefore leftEnding rightEnding : (app).Control)
    (leftPrior : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      scheduler).Trace (some leftBefore))
    (rightPrior : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      scheduler).Trace (some rightBefore))
    (leftKept : TracePrefix hTrace leftPrior) (rightKept : TracePrefix waitTrace rightPrior)
    (leftSame : leftBefore.execution.application.attempt = execution.application.attempt)
    (rightSame : rightBefore.execution.application.attempt = execution.application.attempt)
    (leftRaw rightRaw : RecoveryState (graph))
    (leftEffect : PhaseClosingEffect runtime leaks leftBefore.execution leftEnding.execution
      leftRaw)
    (rightEffect : PhaseClosingEffect runtime leaks rightBefore.execution rightEnding.execution
      rightRaw)
    (leftChanged : leftEnding.execution.application.attempt ≠
      leftBefore.execution.application.attempt)
    (rightChanged : rightEnding.execution.application.attempt ≠
      rightBefore.execution.application.attempt)
    (leftFinished : phase.Finished (phase.drain leftRaw))
    (rightFinished : phase.Finished (phase.drain rightRaw))
    (leftClean : (phase.drain leftRaw).excluded = execution.application.entry.excluded)
    (rightClean : (phase.drain rightRaw).excluded = execution.application.entry.excluded) :
    let players := PhaseProposalQualifiedBinding.baseAliasPolicy setup mode runtime leaks bounds
      plan (PhaseProposalQualifiedBinding.tableValues setup table) PhaseProposalRates.zero
    (∀ who, (ReactiveApplication.anchoredPolicy execution players who).Consistent
      (leftBefore.execution.recall who)) →
    (∀ who, (ReactiveApplication.anchoredPolicy (execution.respond app focal ⟨none⟩) players
      who).Consistent (rightBefore.execution.recall who)) →
    ∀ event ∈ phase.events, (phase.drain leftRaw).native.config.outputs event =
      (phase.drain rightRaw).native.config.outputs event := by
  classical
  intro players leftConsistent rightConsistent
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  let horizon := ReservedEpoch.executionHorizon runtime
  let anchor : (app).Control := ⟨remaining, some focal, execution⟩
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered (control : (app).Control)
      (trace : ((menu).protocol initial horizon scheduler).Trace (some control)) :=
    (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler initialized
      ((menu).toRawTrace initial horizon scheduler trace)
  have leftMetadata := phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
    plan horizon scheduler anchor leftBefore hTrace leftPrior leftKept leftSame.symm
  have rightMetadata := phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
    plan horizon scheduler anchor rightBefore hTrace rightPrior (waitKept.trans rightKept)
      rightSame.symm
  have leftInstalled : phase ∈ leftBefore.execution.application.phases.head? := by
    rwa [leftMetadata.1]
  have rightInstalled : phase ∈ rightBefore.execution.application.phases.head? := by
    rwa [rightMetadata.1]
  obtain ⟨_, leftRecords, leftReceipts, _, _, _⟩ := phaseClosingEffect_checkpoint_facts setup mode
    runtime leaks bounds plan horizon scheduler leftBefore leftEnding leftPrior leftRaw leftEffect
      leftChanged
  obtain ⟨_, rightRecords, rightReceipts, _, _, _⟩ := phaseClosingEffect_checkpoint_facts setup mode
    runtime leaks bounds plan horizon scheduler rightBefore rightEnding rightPrior rightRaw
      rightEffect rightChanged
  obtain ⟨_, _, leftStores⟩ := closing_binding_frame setup mode runtime leaks bounds plan horizon
    scheduler leftBefore leftEnding leftPrior phase leftRaw leftEffect leftChanged
  obtain ⟨_, _, rightStores⟩ := closing_binding_frame setup mode runtime leaks bounds plan horizon
    scheduler rightBefore rightEnding rightPrior phase rightRaw rightEffect rightChanged
  have prefixRecall (control : (app).Control)
      (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
      (kept : TracePrefix hTrace trace) (who : Player) :
      execution.recall who <+: control.execution.recall who :=
    (app).reaches_recall_prefix initial horizon scheduler
      ((menu).reaches_raw initial horizon scheduler kept.reachesWithin) anchor control rfl rfl who
  have oldRead (owner : Player) (event : (graph).EventId) (inside : event ∈ phase.events)
      (payload : L.Ty) (binding : (graph).outputLayout event = .binding owner payload)
      (active : owner ∉ execution.application.entry.excluded)
      (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest (graph))
      (record : (app).PlayerEntry) (recorded : record ∈ execution.recall owner)
      (declared : record.action =
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩)
      (same : record.beforeView.application.2.attempt = execution.application.attempt) :
      (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
          (phase.drain leftRaw).native.config.store =
        (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
          (phase.drain rightRaw).native.config.store := by
    have lower : execution.application.attempt.phase ≤ event.val := by
      have low : execution.application.attempt.phase = phase.low := by
        simp only [PhaseRuntimeState.attempt, Option.mem_def.mp installed, Option.map_some,
          Option.getD_some]
      rw [low]
      exact ((phase.mem_events event).mp inside).1
    exact (closing_recorded_binding_material setup mode runtime leaks bounds plan horizon scheduler
      leftBefore leftEnding leftPrior phase leftRaw leftEffect leftChanged leftFinished owner
        event inside payload binding (by rwa [leftSame]) (by rwa [leftClean]) serial opening
        evidence record ((prefixRecall _ _ leftKept owner).subset recorded) declared
        (same.trans leftSame.symm)).trans
      (closing_recorded_binding_material setup mode runtime leaks bounds plan horizon scheduler
        rightBefore rightEnding rightPrior phase rightRaw rightEffect rightChanged rightFinished
        owner event inside payload binding (by rwa [rightSame]) (by rwa [rightClean]) serial
        opening evidence record ((prefixRecall _ _ (waitKept.trans rightKept) owner).subset
          recorded) declared (same.trans rightSame.symm)).symm
  have archive (control : (app).Control)
      (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
      (kept : TracePrefix hTrace trace)
      (same : control.execution.application.attempt = execution.application.attempt) :
      PhaseProposal.sourceArchive control.execution.network.inputs =
        PhaseProposal.sourceArchive execution.network.inputs := by
    have metadata := phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
      plan horizon scheduler anchor control hTrace trace kept same.symm
    have head : phase ∈ control.execution.application.phases.head? := by rwa [metadata.1]
    have filtered (current : (app).Control)
        (currentTrace : ((menu).protocol initial horizon scheduler).Trace (some current))
        (head : phase ∈ current.execution.application.phases.head?) :
        (PhaseProposal.sourceArchive current.execution.network.inputs).filter
          (fun p => p.address.phase < current.execution.application.attempt.phase) =
            PhaseProposal.sourceArchive current.execution.network.inputs := by
      apply Finset.filter_eq_self.mpr
      intro proposal member
      have bound := PhaseProposal.sourceArchive_phase_le runtime leaks plan inputs horizon
        scheduler current ((menu).toRawTrace initial horizon scheduler currentTrace) proposal member
      have empty := PhaseProposal.sourceArchive_nonpublication_bucket_empty runtime leaks bounds
        plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler current
          currentTrace phase (Option.mem_def.mp head) (by rw [commitment]; decide)
      have different : proposal.address.phase ≠ current.execution.application.attempt.phase := by
        intro equal
        exact (Finset.eq_empty_iff_forall_notMem.mp empty proposal)
          (Finset.mem_filter.mpr ⟨member, equal⟩)
      omega
    have selected := metadata.2.2
    have controlFiltered := filtered control trace head
    rw [same] at controlFiltered
    rw [controlFiltered, filtered anchor hTrace installed] at selected
    exact selected
  suffices ∀ rank, ∀ event : (graph).EventId, event.val = rank → event ∈ phase.events →
      (phase.drain leftRaw).native.config.outputs event =
        (phase.drain rightRaw).native.config.outputs event by
    intro event inside
    exact this event.val event rfl inside
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
    intro event rankEq inside
    obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event
      ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
    let ref : FieldRef (graph).layout (.binding owner payload) := ⟨.inr event, binding⟩
    apply (Equiv.cast (congrArg (fun kind => Option kind.Value) binding)).injective
    change ref.get? (phase.drain leftRaw).native.config.store =
      ref.get? (phase.drain rightRaw).native.config.store
    by_cases inactive : owner ∈ execution.application.entry.excluded
    · have absent (before ending : (app).Control)
          (raw : RecoveryState (graph)) (records : ({before.execution.application with
            current := raw} : PhaseRuntimeState (graph)).BindingRecord)
          (receipts : ({before.execution.application with current := raw} :
            PhaseRuntimeState (graph)).ReceiptRecord)
          (head : phase ∈ before.execution.application.phases.head?)
          (entryEq : before.execution.application.entry = execution.application.entry)
          (finished : phase.Finished (phase.drain raw)) :
          ref.get? (phase.drain raw).native.config.store = some .failure := by
        have missing : (phase.drain raw).native.accepted (.inr event) = none := by
          cases found : (phase.drain raw).native.accepted (.inr event) with
          | none => rfl
          | some candidate =>
            rw [(phase.drain_tables raw).1] at found
            exact ((receipts.ordered phase head commitment event owner payload candidate
              ((phase.mem_events event).mp inside).1 binding found).1
                (by rwa [entryEq])).elim
        have read := (phase.drain_bindingInvariant raw records.active).binding_read ref event rfl
          (finished inside)
        simpa only [ref, missing, Option.elim_none] using read
      have leftEntry := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized
        horizon scheduler anchor leftBefore hTrace leftPrior leftKept (ordered anchor hTrace)).2.2
          leftSame.symm
      have rightEntry := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized
        horizon scheduler anchor rightBefore hTrace rightPrior (waitKept.trans rightKept)
          (ordered anchor hTrace)).2.2 rightSame.symm
      exact (absent leftBefore leftEnding leftRaw leftRecords leftReceipts leftInstalled
        leftEntry.symm leftFinished).trans (absent rightBefore rightEnding rightRaw rightRecords
          rightReceipts rightInstalled rightEntry.symm rightFinished).symm
    · have lower : execution.application.attempt.phase ≤ event.val := by
        have head := Option.mem_def.mp installed
        simpa only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some] using
          ((phase.mem_events event).mp inside).1
      obtain ⟨lr, le, lp, lrecord, lpost, ls, lo, lev, lpPost, lpostKept, llen, lmem, lview,
        ldecl, latt, lrequest, lunsent, llater, lread⟩ := closing_binding_declaration setup mode
          runtime leaks bounds plan horizon scheduler leftBefore leftEnding leftPrior phase leftRaw
          leftEffect leftChanged leftFinished owner event inside payload binding
          (by rwa [leftSame]) (by rwa [leftClean])
      obtain ⟨rr, re, rp, rrecord, rpost, rs, ro, rev, rpPost, rpostKept, rlen, rmem, rview,
        rdecl, ratt, rrequest, runsent, rlater, rread⟩ := closing_binding_declaration setup mode
          runtime leaks bounds plan horizon scheduler rightBefore rightEnding rightPrior phase
          rightRaw rightEffect rightChanged rightFinished owner event inside payload binding
          (by rwa [rightSame]) (by rwa [rightClean])
      by_cases lold : lpost.length ≤ hTrace.length
      · have path := lpostKept.reachesWithin.ancestor_comparable leftKept.reachesWithin lold
        have recalled := (app).reaches_recall_prefix initial horizon scheduler
          ((menu).reaches_raw initial horizon scheduler path)
          ⟨lr, none, le.respond app owner lrecord.action⟩ anchor rfl rfl owner
        exact oldRead owner event inside payload binding inactive ls lo lev lrecord
          (recalled.subset lmem) ldecl (latt.trans leftSame)
      by_cases rold : rpost.length ≤ waitTrace.length
      · have path := rpostKept.reachesWithin.ancestor_comparable rightKept.reachesWithin rold
        have recalled := (app).reaches_recall_prefix initial horizon scheduler
          ((menu).reaches_raw initial horizon scheduler path)
          ⟨rr, none, re.respond app owner rrecord.action⟩
          ⟨remaining, none, execution.respond app focal ⟨none⟩⟩ rfl rfl owner
        have old : rrecord ∈ execution.recall owner := by
          have member := recalled.subset rmem
          by_cases same : owner = focal
          · subst owner
            simp only [ReactiveApplication.Execution.respond, ite_true, List.mem_append,
              List.mem_singleton] at member
            rcases member with old | equal
            · exact old
            · have impossible := congrArg ReactiveApplication.PlayerEntry.action equal
              rw [rdecl] at impossible
              cases impossible
          · simpa only [ReactiveApplication.Execution.respond, same, ite_false] using member
        exact oldRead owner event inside payload binding inactive rs ro rev rrecord old rdecl
          (ratt.trans rightSame)
      have lprefix := (leftKept.reachesWithin.ancestor_comparable
        (lpPost.trans lpostKept).reachesWithin (by
          change hTrace.length ≤ lp.length
          omega)).tracePrefix
      have rprefixWait := (rightKept.reachesWithin.ancestor_comparable
        (rpPost.trans rpostKept).reachesWithin (by
          change waitTrace.length ≤ rp.length
          omega)).tracePrefix
      have rprefix := waitKept.trans rprefixWait
      have lcallback : le.application.attempt = execution.application.attempt := by
        have actual := latt.trans leftSame
        rw [lview] at actual
        change le.application.attempt = execution.application.attempt at actual
        exact actual
      have rcallback : re.application.attempt = execution.application.attempt := by
        have actual := ratt.trans rightSame
        rw [rview] at actual
        change re.application.attempt = execution.application.attempt at actual
        exact actual
      have lmeta := phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds plan
        horizon scheduler anchor ⟨lr, some owner, le⟩ hTrace lp lprefix lcallback.symm
      have rmeta := phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds plan
        horizon scheduler anchor ⟨rr, some owner, re⟩ hTrace rp rprefix rcallback.symm
      have lentry := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized
        horizon scheduler anchor ⟨lr, some owner, le⟩ hTrace lp lprefix
          (ordered anchor hTrace)).2.2 lcallback.symm
      have rentry := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized
        horizon scheduler anchor ⟨rr, some owner, re⟩ hTrace rp rprefix
          (ordered anchor hTrace)).2.2 rcallback.symm
      have lstored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
        ((menu).toRawTrace initial horizon scheduler lp)
      have rstored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
        ((menu).toRawTrace initial horizon scheduler rp)
      have lfail := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon scheduler
        ((menu).toRawTrace initial horizon scheduler lp)
      have rfail := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon scheduler
        ((menu).toRawTrace initial horizon scheduler rp)
      have lfrontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler
        (fun state supported => by
          obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact PhaseRuntimeState.initial_frontier plan draw)
        ((menu).toRawTrace initial horizon scheduler lp)
      have rfrontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler
        (fun state supported => by
          obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact PhaseRuntimeState.initial_frontier plan draw)
        ((menu).toRawTrace initial horizon scheduler rp)
      have ownEarlier : ∀ prior ∈ phase.events, prior.val < event.val →
          (graph).actor? prior = some owner →
          le.application.current.native.config.store (.inr prior) =
            re.application.current.native.config.store (.inr prior) := by
        intro prior insidePrior earlier owned
        obtain ⟨priorOwner, priorPayload, priorBinding⟩ := commitment ▸ phase.fields prior
          ((phase.mem_events prior).mp insidePrior).1 ((phase.mem_events prior).mp insidePrior).2
        have ownerEq : priorOwner = owner := Option.some.inj
          ((actor?_of_outputLayout_binding (graph) priorBinding).symm.trans owned)
        subst priorOwner
        have dependency := (serviceGraph_revealRelaxedOrdered setup mode).keeps
          (barrierOrder_same_owner (graph).outputLayout earlier (by
            rw [priorBinding, binding]; rfl))
          (Or.inl (by simp only [priorBinding, EventField.IsPublication, not_false_eq_true]))
        obtain ⟨lv, lvalue⟩ := Option.isSome_iff_exists.mp
          ((le.application.current.native.config.output_available prior).mpr
            (lrequest.2.2.1.2 dependency))
        obtain ⟨rv, rvalue⟩ := Option.isSome_iff_exists.mp
          ((re.application.current.native.config.output_available prior).mpr
            (rrequest.2.2.1.2 dependency))
        have lkeep := (phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
          ⟨lr, some owner, le⟩ leftBefore lp leftPrior (lpPost.trans lpostKept)
          (ordered _ lp) (lcallback.trans leftSame.symm)).1
        have rkeep := (phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
          ⟨rr, some owner, re⟩ rightBefore rp rightPrior (rpPost.trans rpostKept)
          (ordered _ rp) (rcallback.trans rightSame.symm)).1
        have leftValue := leftStores (.inr prior) lv (lkeep (.inr prior) lv lvalue)
        have rightValue := rightStores (.inr prior) rv (rkeep (.inr prior) rv rvalue)
        have equal := ih prior.val (by omega) prior rfl insidePrior
        change (phase.drain leftRaw).native.config.store (.inr prior) =
          (phase.drain rightRaw).native.config.store (.inr prior) at equal
        calc
          _ = some lv := lvalue
          _ = _ := leftValue.symm
          _ = _ := equal
          _ = some rv := rightValue
          _ = _ := rvalue.symm
      have queries := phaseProposalQuery?_eq_of_ready_saved setup mode runtime leaks plan complete
        initial horizon scheduler scheduler lr rr owner le re
        ((menu).toRawTrace initial horizon scheduler lp)
        ((menu).toRawTrace initial horizon scheduler rp) phase commitment
        (by rwa [lmeta.1]) (by rwa [rmeta.1]) lfrontier rfrontier lstored rstored lfail rfail
        (lentry.symm.trans rentry) (lcallback.trans rcallback.symm)
        (lmeta.2.1.trans rmeta.2.1.symm) event inside lrequest rrequest ownEarlier
        ((archive _ lp lprefix lcallback).trans (archive _ rp rprefix rcallback).symm)
      obtain ⟨_, _, _, _, _, lquery⟩ := phaseProposalQuery?_genuine_base setup mode runtime leaks
        complete plan maximal horizon scheduler (by
          rw [← initialEq]
          exact (menu).toRawTrace initial horizon scheduler lp)
        owner rfl event payload binding lrequest
      have rquery := queries.symm.trans lquery
      obtain ⟨ltail, lrecall⟩ := llater
      obtain ⟨rtail, rrecall⟩ := rlater
      have lsupport := leftConsistent owner
      have rsupport := rightConsistent owner
      rw [lrecall, ← List.singleton_append, ← List.append_assoc] at lsupport
      rw [rrecall, ← List.singleton_append, ← List.append_assoc] at rsupport
      have laction := (ReactiveApplication.Policy.consistent_snoc_iff
        (ReactiveApplication.anchoredPolicy execution players owner) _ _).mp
          (ReactiveApplication.Policy.Consistent.of_append lsupport)
      have raction := (ReactiveApplication.Policy.consistent_snoc_iff
        (ReactiveApplication.anchoredPolicy (execution.respond app focal ⟨none⟩) players owner)
          _ _).mp (ReactiveApplication.Policy.Consistent.of_append rsupport)
      rw [lview, ReactiveApplication.anchoredPolicy_of_extends execution players owner _ _
        (prefixRecall _ lp lprefix owner)] at laction
      rw [rview, ReactiveApplication.anchoredPolicy_of_extends
        (execution.respond app focal ⟨none⟩) players owner _ _
        ((app).reaches_recall_prefix initial horizon scheduler
          ((menu).reaches_raw initial horizon scheduler rprefixWait.reachesWithin) _ _ rfl rfl
            owner)] at raction
      have lprepared := table_binding_preparation setup mode runtime leaks bounds plan covered table
        scheduler capacity lr owner le (initialEq ▸ lp) event payload binding lrequest lunsent
          _ lquery lrecord.action laction.2
      have rprepared := table_binding_preparation setup mode runtime leaks bounds plan covered table
        scheduler capacity rr owner re (initialEq ▸ rp) event payload binding rrequest runsent
          _ rquery rrecord.action raction.2
      rw [ldecl] at lprepared
      rw [rdecl] at rprepared
      have openings : lo.bind (fun value => value.as? payload) =
          ro.bind (fun value => value.as? payload) := by
        have rawEqual := lprepared.trans rprepared.symm
        simpa only [PhaseProposal.bindingPreparation, Option.bind_some, binding, Option.bind_map,
          Function.comp_def, Raw.as?_mk, Option.bind_fun_some] using
          congrArg (fun value => value.bind fun raw => raw.as? payload) rawEqual
      exact lread.trans (by rw [openings]; exact rread.symm)

end Vegas

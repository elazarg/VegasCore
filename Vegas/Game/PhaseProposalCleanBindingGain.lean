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
import Vegas.Game.PhaseProposalOrdinaryBindingCheckpoint
import Vegas.Game.PhaseProposalBindingWitness
import Vegas.Game.CompiledCommitSurvivingView
import Vegas.Game.CompiledCommitPrefixExclusions
import Vegas.Game.RecoveryPublicClosingWitness
import Vegas.Source.CommitRecoveryCommitUnique
import Interaction.ReactiveAnchoredStopped
import Interaction.ReactiveStoppedState
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
    (starting : (app).Control)
    (startingTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      scheduler).Trace (some starting))
    (kept : TracePrefix anchorTrace startingTrace)
    (stopped : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      scheduler).History → Prop) :
    let horizon := ReservedEpoch.executionHorizon runtime
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let players := PhaseProposalQualifiedBinding.baseAliasPolicy setup mode runtime leaks bounds
      plan (PhaseProposalQualifiedBinding.tableValues setup table) PhaseProposalRates.zero
    (∀ who, (ReactiveApplication.anchoredPolicy anchor.execution players who).Consistent
      (starting.execution.recall who)) →
    ∀ final ∈ (model.runBehavioralUntil certificate
        (PhaseProposalQualifiedBinding.baseAliasStrategy setup mode runtime leaks bounds plan
          (PhaseProposalQualifiedBinding.tableValues setup table) scheduler PhaseProposalRates.zero)
        stopped ⟨some starting, startingTrace⟩).support,
      ReactiveApplication.executionInvariant
        (fun execution => ∀ who,
          (ReactiveApplication.anchoredPolicy anchor.execution players who).Consistent
            (execution.recall who)) final.state := by
  classical
  intro horizon model certificate players initially
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
  have same : model.runBehavioralUntil certificate profile stopped ⟨some starting, startingTrace⟩ =
      model.runBehavioralUntil certificate original stopped ⟨some starting, startingTrace⟩ := by
    apply model.runBehavioralUntil_congr certificate stopped ⟨some starting, startingTrace⟩
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
              ((menu).reaches_raw initial horizon scheduler
                (kept.trans path.tracePrefix).reachesWithin) anchor current rfl rfl who
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
  have faithful : ReactiveApplication.executionInvariant predicate (some starting) := initially
  intro final supported
  rw [← same] at supported
  exact model.runBehavioralUntil_support_history_closed certificate profile stopped
    (fun history => ReactiveApplication.executionInvariant predicate history.state) preserved
      ⟨some starting, startingTrace⟩ faithful final supported

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

omit [Fintype Player] in
private theorem filled_failed_binding_field
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (store : Store (graphLayout setup.program)) (entry : SourceProgram.Config Player L Γ),
      (Γ.map Prod.fst).Nodup →
      ∀ (who : Player) (payload : L.Ty)
        (index : Fin (eventCount (block.prepend suffix))), index.val < block.length →
        outputLayout (block.prepend suffix) index = .binding who payload →
        ∀ field : FieldRef (graphLayout setup.program) (.binding who payload),
          field.field = .inr (embedding.event index) → field.get? store = some .failure →
            (fillCommitPrefix setup.program block suffix embedding store entry).FailedBinding
              who P := by
  induction block with
  | nil =>
      intro suffix embedding store entry unique who payload index inside
      simp only [SourceProgram.CommitPrefix.length] at inside
      omega
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding store entry unique who ty index
      refine Fin.cases ?_ ?_ index
      · intro inside typed field named failed
        change EventField.binding owner payload = .binding who ty at typed
        cases typed
        let zero : Fin (eventCount
            ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
          ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
        let head : FieldRef (graphLayout setup.program) (.binding owner payload) :=
          ⟨.inr (embedding.event zero), embedding.layout_eq zero⟩
        have fields : head = field := by
          rcases field with ⟨actual, layout⟩
          change actual = .inr (embedding.event zero) at named
          subst actual; rfl
        let later := embedding.tail (rest.prepend suffix)
          (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
        have choice : (head.get? store).getD .failure = .failure := by
          rw [fields, failed]; rfl
        have debt := (fillCommitPrefix_attempt setup.program rest suffix later store
          (commitSuccessor name guard entry .failure)).preserves_failedBinding owner
            (SourceProgram.Config.failedBinding_commit entry unique fresh guard O)
        change (fillCommitPrefix setup.program rest suffix later store
          (commitSuccessor name guard entry ((head.get? store).getD .failure))).FailedBinding
            owner P
        rw [choice]
        exact debt
      · intro index inside typed field named failed
        dsimp only [fillCommitPrefix]
        exact ih suffix _ store _ (List.nodup_cons.mpr ⟨fresh, unique⟩) who ty index
          (by change index.val + 1 < rest.length + 1 at inside; omega) typed field named failed

private theorem current_prefix_no_failed_binding
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (noCurrent : ¬ phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (control.execution.observe app who))
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names
      Δ P)
    (reconstruct : earlier.prepend (.commit name who fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length) (named : checkpoint.embedding.event selected = event) :
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
        checkpoint.embedding
    ¬ (fillCommitPrefix setup.program earlier (.commit name who fresh guard next) embedding
      control.execution.application.current.native.config.store checkpoint.source).FailedBinding
        who P := by
  intro embedding failed
  let suffix := SourceProgram.commit name who fresh guard next
  let filled := fillCommitPrefix setup.program earlier suffix embedding
    control.execution.application.current.native.config.store checkpoint.source
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have filledRead := checkpoint.filled_prefix_view fresh guard next earlier reconstruct stored
    selected atEnd (named.symm ▸ request.2.2.1) (named.symm ▸ request.2.2.2.1)
      (by rw [named, binding]; exact id) (filled.history who) rfl
  rw [named] at filledRead
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  obtain ⟨current, sourceTrace, _excluded, _generation, _control, _acting, _played, decoded⟩ :=
    phaseSurvivingSourceView?_of_ready_binding setup mode runtime leaks plan maximal horizon
      scheduler (initialEq ▸ raw) who event payload binding request
  have originalRead := decoded
  rw [phaseSurvivingSourceView?_observed_of_history setup mode runtime leaks plan inputs horizon
    scheduler raw who event] at decoded
  have currentErased := congrArg (Option.map (ProtocolView.eraseHistory who setup.program)) decoded
  have filledErased := congrArg (Option.map (ProtocolView.eraseHistory who setup.program))
    filledRead
  rw [← decodeEventView?_eraseHistory] at currentErased filledErased
  have views := Option.some.inj (currentErased.symm.trans filledErased)
  let point := checkpoint.residual.lift (cast (congrArg ProtocolState reconstruct)
    (earlier.liftPoint suffix (ProtocolState.entry suffix filled)))
  have transport {first second : SourceProgram Player L checkpoint.residual.context
      checkpoint.residual.names} (eq : first = second)
      (lift : ProtocolState second → ProtocolState setup.program)
      (origin : ProtocolSuffix setup.program second lift) :
      ProtocolSuffix setup.program first (fun p => lift (cast (congrArg ProtocolState eq) p)) := by
    cases eq; exact origin
  have pointFailed : ProtocolState.FailedBinding who setup.program point :=
    (transport reconstruct checkpoint.residual.lift checkpoint.origin).failedBinding_lift who _
      (earlier.failedBinding_liftPoint suffix who _
        (ProtocolState.failedBinding_entry suffix filled failed))
  have erasedViews : ProtocolState.observe who setup.program
      (ProtocolState.withHistory setup.program current.point (fun _ => [])) =
      ProtocolState.observe who setup.program
        (ProtocolState.withHistory setup.program point (fun _ => [])) := by
    simpa only [ProtocolView.eraseHistory_observe] using views
  have currentFailed := (ProtocolState.failedBinding_withHistory who setup.program current.point
    (fun _ => [])).mp
      ((ProtocolState.failedBinding_iff_of_observe_eq who setup.program _ _ erasedViews).mpr
        ((ProtocolState.failedBinding_withHistory who setup.program point (fun _ => [])).mpr
          pointFailed))
  exact noCurrent ((phaseProposalCurrentBindingFailure_iff_of_readback setup mode runtime leaks
    who event _ current.point originalRead).mpr currentFailed)

private theorem table_closing_binding_values_success
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
    (witness : RecoverySourceWitness setup mode plan execution.application)
    (phase : RuntimePhase (graph)) (rest : List (RuntimePhase (graph)))
    (installed : execution.application.phases = phase :: rest) (kind : phase.kind = .commitment)
    (current : (graph).EventId) (currentPayload : L.Ty)
    (currentBinding : (graph).outputLayout current = .binding focal currentPayload)
    (request : execution.application.SeedRequest focal ⟨execution.application.attempt, current⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall focal),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, current⟩)
    (noCurrent : ¬ phaseProposalCurrentBindingFailure setup mode runtime leaks focal current
      (execution.observe app focal))
    (foreign : ∀ owner, owner ≠ focal → owner ∉ execution.application.entry.excluded →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial
        (ReservedEpoch.executionHorizon runtime) scheduler owner
          ⟨some ⟨remaining, some focal, execution⟩, hTrace⟩)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      scheduler).Trace (some before))
    (kept : TracePrefix waitTrace prior)
    (same : before.execution.application.attempt = execution.application.attempt)
    (raw : RecoveryState (graph))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (clean : (phase.drain raw).excluded = execution.application.entry.excluded) :
    let players := PhaseProposalQualifiedBinding.baseAliasPolicy setup mode runtime leaks bounds
      plan (PhaseProposalQualifiedBinding.tableValues setup table) PhaseProposalRates.zero
    (∀ owner, (ReactiveApplication.anchoredPolicy (execution.respond app focal ⟨none⟩) players
      owner).Consistent (before.execution.recall owner)) →
    ∀ event ∈ phase.events, ∀ owner payload,
      ∀ binding : (graph).outputLayout event = .binding owner payload,
      owner ∉ execution.application.entry.excluded →
      ∃ value : L.Val payload,
        (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
          (phase.drain raw).native.config.store = some (.success value) := by
  classical
  intro players consistent event inside owner payload binding active
  let horizon := ReservedEpoch.executionHorizon runtime
  let anchor : (app).Control := ⟨remaining, some focal, execution⟩
  let waiting : (app).Control := ⟨remaining, none, execution.respond app focal ⟨none⟩⟩
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  have frontier := witness.order.frontier
  have geometry := witness.checkpoint.commit_phase_geometry phase rest installed kind frontier
    (maximal.suffix witness.suffix)
  have lower : execution.application.attempt.phase ≤ event.val := by
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using ((phase.mem_events event).mp inside).1
  obtain ⟨steps, previous, previousTrace, record, post, serial, opening, evidence,
    priorPost, postKept, length, recorded, viewed, declared, atAttempt, offered, _notSent,
    recalled, result⟩ := closing_binding_declaration setup mode runtime leaks bounds plan horizon
      scheduler before ending prior phase raw effect changed finished owner event inside payload
        binding (by rwa [same]) (by rwa [clean])
  have atOriginal : record.beforeView.application.2.attempt = execution.application.attempt :=
    atAttempt.trans same
  suffices prepared : ∃ value : L.Val payload,
      opening.bind (fun value => value.as? payload) = some value by
    obtain ⟨value, decoded⟩ := prepared
    exact ⟨value, by simpa only [decoded, Option.elim_some] using result⟩
  by_cases old : post.length ≤ waitTrace.length
  · have path := postKept.reachesWithin.ancestor_comparable kept.reachesWithin old
    have retained := (app).reaches_recall_prefix initial horizon scheduler
      ((menu).reaches_raw initial horizon scheduler path)
        ⟨steps, none, previous.respond app owner record.action⟩ waiting rfl rfl owner
    have oldRecord : record ∈ execution.recall owner := by
      have member := retained.subset recorded
      by_cases owned : owner = focal
      · subst owner
        simp only [waiting, ReactiveApplication.Execution.respond, ite_true, List.mem_append,
          List.mem_singleton] at member
        rcases member with member | equal
        · exact member
        · have impossible := congrArg ReactiveApplication.PlayerEntry.action equal
          rw [declared] at impossible
          cases impossible
      · simpa only [waiting, ReactiveApplication.Execution.respond, owned, ite_false] using member
    by_cases owned : owner = focal
    · subst owner
      have earlier := phase_recorded_binding_rank_lt_of_unsent_request runtime leaks bounds plan
        inputs horizon (serviceGraph_revealRelaxedOrdered setup mode) scheduler hTrace focal record
          oldRecord ⟨⟨.commitment event (focal, .prepared serial), opening⟩, evidence⟩
            (by rw [declared]) event (focal, .prepared serial) rfl atOriginal current request unsent
      have dependency := (serviceGraph_revealRelaxedOrdered setup mode).keeps
        (barrierOrder_same_owner (graph).outputLayout earlier
          (by rw [binding, currentBinding]; rfl))
        (Or.inl (by simp only [binding, EventField.IsPublication, not_false_eq_true]))
      have completed := request.2.2.1.2 dependency
      have originalRead := phaseProposal_completed_binding_material runtime leaks bounds plan
        inputs horizon scheduler anchor hTrace focal event payload binding lower completed
          request.2.2.2.2 serial opening evidence record oldRecord declared atOriginal
      cases decoded : opening.bind (fun value => value.as? payload) with
      | some value => exact ⟨value, rfl⟩
      | none =>
        have failedRead : (⟨.inr event, binding⟩ :
            FieldRef (graph).layout (.binding focal payload)).get?
              execution.application.current.native.config.store = some .failure := by
          simpa only [decoded, Option.elim_none] using originalRead
        generalize decomposition :
          commitPhase witness.checkpoint.residual.tail = segment at geometry
        rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
        dsimp only at geometry
        have high : phase.high = phase.low + block.length := by
          have positive := phase.nonempty
          omega
        have currentInside : current ∈ phase.events := by
          obtain ⟨selected, member, present⟩ := request.2.1
          have selectedEq : selected = phase :=
            (by simpa only [installed, List.head?_cons, Option.mem_some_iff]
              using member : phase = selected).symm
          exact selectedEq ▸ present
        obtain ⟨selected, named, Ξ, Q, name, fresh, guard, keptRecall, later, size,
          _sameBlock, prefixEq⟩ := witness.checkpoint.fixed_binding_prefix block suffix reconstruct
            frontier phase rest installed high current currentInside request.2.2.1 focal
              currentPayload currentBinding
        have notFailed := current_prefix_no_failed_binding setup mode runtime leaks bounds plan
          maximal horizon scheduler anchor hTrace witness.checkpoint focal current currentPayload
            currentBinding request noCurrent fresh guard (later.prepend suffix) keptRecall prefixEq
              selected size.symm named
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) prefixEq.symm)
            witness.checkpoint.embedding
        have rankTransport {first second : SourceProgram Player L
            witness.checkpoint.residual.context witness.checkpoint.residual.names}
            (eq : first = second) (e : OutputEmbedding (inputLayout setup.context)
              (outputLayout setup.program) second)
            (r : ∀ i, (e.event i).val = execution.application.attempt.phase + i.val) :
            ∀ i, ((cast (congrArg (fun p => OutputEmbedding (inputLayout setup.context)
              (outputLayout setup.program) p) eq.symm) e).event i).val =
                execution.application.attempt.phase + i.val := by cases eq; exact r
        have ranks := rankTransport prefixEq witness.checkpoint.embedding
          witness.checkpoint.compiled.rankEq
        have currentRank := witness.checkpoint.compiled.rankEq selected
        rw [named, ← size] at currentRank
        let index : Fin (eventCount (keptRecall.prepend
            (.commit name focal fresh guard (later.prepend suffix)))) :=
          ⟨event.val - execution.application.attempt.phase, by
            have bound := keptRecall.eventCount_prepend
              (.commit name focal fresh guard (later.prepend suffix))
            omega⟩
        have indexed : embedding.event index = event := Fin.ext (by
          change (embedding.event index).val = event.val
          rw [ranks]
          dsimp only [index]
          omega)
        have typed : outputLayout
            (keptRecall.prepend (.commit name focal fresh guard (later.prepend suffix))) index =
              .binding focal payload :=
          (embedding.layout_eq index).symm.trans (indexed.symm ▸ binding)
        exact (notFailed (filled_failed_binding_field setup keptRecall
          (.commit name focal fresh guard (later.prepend suffix)) embedding
            execution.application.current.native.config.store witness.checkpoint.source
              witness.checkpoint.unique focal payload index (by dsimp only [index]; omega) typed
                ⟨.inr event, binding⟩ (congrArg Sum.inr indexed.symm) failedRead)).elim
    · exact phaseProposal_recalled_binding_preparation_value runtime leaks bounds initial horizon
        scheduler anchor hTrace owner (foreign owner owned active) event payload binding serial
          opening evidence record oldRecord declared
  · have keptRecall := (kept.reachesWithin.ancestor_comparable
        (priorPost.trans postKept).reachesWithin (by
          change waitTrace.length ≤ previousTrace.length
          omega)).tracePrefix
    obtain ⟨tail, recalled⟩ := recalled
    have action := consistent owner
    rw [recalled, ← List.singleton_append, ← List.append_assoc] at action
    have supported := (ReactiveApplication.Policy.consistent_snoc_iff
      (ReactiveApplication.anchoredPolicy waiting.execution players owner) _ _).mp
        (ReactiveApplication.Policy.Consistent.of_append action)
    have extendsRecall := (app).reaches_recall_prefix initial horizon scheduler
      ((menu).reaches_raw initial horizon scheduler keptRecall.reachesWithin)
        waiting ⟨steps, some owner, previous⟩ rfl rfl owner
    rw [viewed, ReactiveApplication.anchoredPolicy_of_extends waiting.execution players owner _ _
      extendsRecall] at supported
    obtain ⟨_, _, _, _, _, query⟩ := phaseProposalQuery?_genuine_base setup mode runtime leaks
      complete plan maximal horizon scheduler (by
        rw [← initialEq]
        exact (menu).toRawTrace initial horizon scheduler previousTrace) owner rfl event payload
          binding offered
    have prepared := table_binding_preparation setup mode runtime leaks bounds plan covered table
      scheduler capacity steps owner previous (initialEq ▸ previousTrace) event payload binding
        offered _notSent _ query record.action supported.2
    rw [declared] at prepared
    have decoded := congrArg (fun value : Option (Raw L) =>
      value.bind fun raw => raw.as? payload) prepared
    simp only [PhaseProposal.bindingPreparation, Option.bind_some, binding, Option.bind_map,
      Function.comp_def, Raw.as?_mk, Option.bind_fun_some] at decoded
    exact ⟨_, decoded⟩

private theorem completed_binding_source_values
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (state : PhaseRuntimeState (graph))
    (witness : RecoverySourceWitness setup mode plan state)
    (phase : RuntimePhase (graph)) (rest : List (RuntimePhase (graph)))
    (installed : state.phases = phase :: rest) (kind : phase.kind = .commitment)
    (finished : phase.Finished (phase.drain state.current))
    (clean : (phase.drain state.current).excluded = state.entry.excluded)
    (coverage : state.FailureCoverage)
    (oldValues : ∀ owner, owner ∉ state.entry.excluded →
      witness.checkpoint.source.BindingsHoldValues owner)
    (values : ∀ event ∈ phase.events, ∀ owner payload,
      ∀ binding : (graph).outputLayout event = .binding owner payload,
      owner ∉ state.entry.excluded → ∃ value : L.Val payload,
        (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
          (phase.drain state.current).native.config.store = some (.success value)) :
    ∀ owner, owner ∉ state.entry.excluded →
      ProtocolState.BindingsHoldValues owner setup.program
        (witness.checkpoint.commitResultPoint (phase.drain state.current)) := by
  classical
  have fillValues {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      (block : SourceProgram.CommitPrefix Γ O Δ P) :
      ∀ (suffix : SourceProgram Player L Δ P)
        (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          (block.prepend suffix))
        (store : Store (graphLayout setup.program)) (entry : SourceProgram.Config Player L Γ)
        (owner : Player), entry.BindingsHoldValues owner →
        (∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          ∀ payload (binding : outputLayout setup.program (embedding.event index) =
            .binding owner payload), ∃ value : L.Val payload,
              (⟨.inr (embedding.event index), binding⟩ :
                FieldRef (graphLayout setup.program) (.binding owner payload)).get? store =
                  some (.success value)) →
        (fillCommitPrefix setup.program block suffix embedding store entry).BindingsHoldValues
          owner := by
    induction block with
    | nil => intro suffix embedding store entry owner proper _values; exact proper
    | @commit Γ O Δ P name who payload fresh guard rest ih =>
      intro suffix embedding store entry owner proper available
      let zero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name who fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout setup.program) (.binding who payload) :=
        ⟨.inr (embedding.event zero), embedding.layout_eq zero⟩
      let next := commitSuccessor name guard entry ((field.get? store).getD .failure)
      have nextProper : next.BindingsHoldValues owner := by
        intro subject ty cell
        cases cell with
        | there cell => exact proper cell
        | here =>
          obtain ⟨value, stored⟩ := available zero
            (by simp only [zero, SourceProgram.CommitPrefix.length]; omega) payload
              (embedding.layout_eq zero)
          refine ⟨value, ?_⟩
          change (field.get? store).getD .failure = .success value
          rw [stored]
          rfl
      let later := embedding.tail (rest.prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      change (fillCommitPrefix setup.program rest suffix later store next).BindingsHoldValues owner
      exact ih suffix later store next owner nextProper (fun index inside ty binding =>
        available (Fin.succ index) (by change index.val + 1 < rest.length + 1; omega) ty binding)
  intro owner active
  have geometry := witness.checkpoint.commit_phase_geometry phase rest installed kind
    witness.order.frontier (maximal.suffix witness.suffix)
  unfold RecoverySourceCheckpoint.commitResultPoint
  generalize decomposition : commitPhase witness.checkpoint.residual.tail = segment at geometry ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  dsimp only at geometry ⊢
  let embedding := cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
      witness.checkpoint.embedding
  let image := phase.drain state.current
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding image.native
    witness.checkpoint.source state.entry.excluded
  have rankTransport {first second : SourceProgram Player L
      witness.checkpoint.residual.context witness.checkpoint.residual.names} (eq : first = second)
      (e : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) second)
      (r : ∀ i, (e.event i).val = state.attempt.phase + i.val) :
      ∀ i, ((cast (congrArg (fun p => OutputEmbedding (inputLayout setup.context)
        (outputLayout setup.program) p) eq.symm) e).event i).val =
          state.attempt.phase + i.val := by cases eq; exact r
  have ranked := rankTransport reconstruct witness.checkpoint.embedding
    witness.checkpoint.compiled.rankEq
  have after : decoded.2.1 = state.entry.excluded := by
    rw [decodeCommitAttempt_excluded_eq_public_prefix setup.program mode block suffix embedding
      state.attempt.phase ranked image.native
        (fun index inside => finished (geometry.2 index inside))]
    apply Finset.union_eq_left.mpr
    intro other member
    obtain ⟨event, _lower, _upper, acting, failed⟩ := (Finset.mem_filter.mp member).2
    rw [← clean]
    exact (coverage.active.drain phase).covered event other acting failed
  have observed := decodeCommitAttempt_surviving_view_eq_fill setup.program mode block suffix
    embedding image.native (phase.drain_bindingInvariant state.current witness.binding.active)
      owner witness.checkpoint.source witness.checkpoint.source state.entry.excluded rfl
        (fun index inside _owned => finished (geometry.2 index inside)) (after.symm ▸ active)
  have filledProper : (fillCommitPrefix setup.program block suffix embedding
      image.native.config.store witness.checkpoint.source).BindingsHoldValues owner :=
    fillValues block suffix embedding image.native.config.store
      witness.checkpoint.source owner (oldValues owner active) (by
      intro index inside payload binding
      exact values _ (geometry.2 index inside) owner payload binding active)
  have proper : decoded.1.BindingsHoldValues owner := by
    intro name payload cell
    obtain ⟨value, successful⟩ := filledProper cell
    exact ⟨value, (sourceObserve_ownCommitment_eq
      (congrArg Prod.fst observed) cell).trans successful⟩
  have transport {first second : SourceProgram Player L witness.checkpoint.residual.context
      witness.checkpoint.residual.names} (eq : first = second)
      (lift : ProtocolState second → ProtocolState setup.program)
      (origin : ProtocolSuffix setup.program second lift) :
      ProtocolSuffix setup.program first (fun p => lift (cast (congrArg ProtocolState eq) p)) := by
    cases eq; exact origin
  have origin := transport reconstruct witness.checkpoint.residual.lift witness.checkpoint.origin
  exact (origin.bindingsHoldValues_lift owner _).mpr
    ((block.bindingsHoldValues_liftPoint suffix owner _).mpr
      ((ProtocolState.bindingsHoldValues_entry owner suffix decoded.1).mpr proper))

open Classical in
/-- At an authentic clean unsent binding, waiting has no larger ordinary finish value. -/
theorem phaseProposal_unflagged_wait_finish_le
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (wellFormed : setup.WellFormed)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (fullValues : ∀ owner key, FullSupport (values owner key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    [Finite ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).History]
    [Finite setup.proposalRecoveryProtocol.History]
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, some who, execution⟩))
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (noSaved : ¬ phaseProposalSavedBindingFailure setup mode runtime leaks who event
      (execution.observe app who))
    (noCurrent : ¬ phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (execution.observe app who))
    (sameExcluded : execution.application.current.excluded = execution.application.entry.excluded)
    (foreign : ∀ owner, owner ≠ who → owner ∉ execution.application.current.excluded →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial
        (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape) owner
          ⟨some ⟨remaining, some who, execution⟩, trace⟩)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ bound)
    (excludedBound : |excludedPayoff who| ≤ bound)
    (defaultFloor : excludedPayoff who ≤ 0)
    (terminalFloor : ∀ terminal, excludedPayoff who ≤ utility terminal who) :
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let payoff := fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
      state who
    expect ((app).finish initial (ReservedEpoch.executionHorizon runtime) scheduler players
        (some ⟨remaining, none, execution.respond app who ⟨none⟩⟩)) payoff ≤
      expect ((app).finish initial (ReservedEpoch.executionHorizon runtime) scheduler players
        (some ⟨remaining, some who, execution⟩)) payoff := by
  classical
  intro scheduler players payoff
  let horizon := ReservedEpoch.executionHorizon runtime
  let _ := Fintype.ofFinite (((menu).protocol initial horizon scheduler).History)
  let _ := Fintype.ofFinite setup.proposalRecoveryProtocol.History
  let model := (menu).information initial horizon scheduler
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  let anchor : (app).Control := ⟨remaining, some who, execution⟩
  let waiting : (app).Control := ⟨remaining, none, execution.respond app who ⟨none⟩⟩
  let firstExit := fun attempt (history : ((menu).protocol initial horizon scheduler).History) =>
    match history.state with
    | none => False
    | some current => current.execution.application.attempt ≠ attempt
  let stopped := firstExit execution.application.attempt
  let profile := PhaseProposalQualifiedBinding.baseAliasStrategy setup mode runtime leaks bounds
    plan values scheduler PhaseProposalRates.zero
  let value := fun state => expect ((app).finish initial horizon scheduler players state) payoff
  have bounded : ∀ state, |payoff state| ≤ bound := by
    intro state
    have interval := phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
      (fun _ => -bound) (fun _ => bound)
      (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).1)
      (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).2) state who
    have lower := (abs_le.mp excludedBound).1
    have upper := (abs_le.mp excludedBound).2
    exact abs_le.mpr (by simpa only [min_eq_right lower,
      (min_eq_right (neg_nonpos.mpr nonnegative)), max_eq_right upper, max_eq_right nonnegative,
        Set.mem_Icc] using interval)
  have valueBound : ∀ state, |value state| ≤ bound := fun _ =>
    expect_abs_le_of_bounded nonnegative bounded
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler (initialEq ▸ trace)
  have proper := witness.bindingsHoldValues_of_no_saved_failure_and_foreign_good setup mode
    wellFormed runtime leaks bounds plan maximal horizon scheduler anchor trace who event payload
      binding request noSaved foreign
  obtain ⟨phase, rest, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks plan
    (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
      ((menu).toRawTrace initial horizon scheduler trace) who event payload binding request.2.2.1
  change execution.application.phases = phase :: rest at installed
  obtain ⟨waitTrace⟩ := (menu).trace_respond initial horizon scheduler remaining execution who
    ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds who _ _)
  have profileEq : profile = fun owner => (menu).restrictPolicy initial horizon scheduler owner
      (players owner) := by
    funext owner; dsimp only [profile, PhaseProposalQualifiedBinding.baseAliasStrategy]
    rw [PhaseProposalQualifiedBinding.baseAliasPolicy_zero]
  have terminalValue (history : ((menu).protocol initial horizon scheduler).History) :
      expect (model.runBehavioralTerminalFrom certificate profile history)
          (fun final => payoff final.state) = value history.state := by
    have physical := (menu).terminal_run_restrict_eq_finish initial horizon scheduler certificate
      players ((menu).admissible_of_covered initial horizon scheduler players
        (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values)) history
    rw [← profileEq] at physical
    simpa only [expect_map, Function.comp_def] using
      congrArg (fun distribution => expect distribution payoff) physical
  have split (history : ((menu).protocol initial horizon scheduler).History) :
      value history.state = expect (model.runBehavioralUntil certificate profile stopped history)
        (fun final => value final.state) := by
    rw [← terminalValue history,
      model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate profile stopped,
      expect_bind_tower_bounded _ _ _
        (fun final : ((menu).protocol initial horizon scheduler).History => bounded final.state)]
    simp_rw [terminalValue]
  have reanchor (start : (app).Control)
      (startingTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
      (laws : Player → (app).Policy) :
      model.runBehavioralUntil certificate
          (fun owner => (menu).restrictPolicy initial horizon scheduler owner
            (ReactiveApplication.anchoredPolicy start.execution laws owner)) stopped
          ⟨some start, startingTrace⟩ =
        model.runBehavioralUntil certificate
          (fun owner => (menu).restrictPolicy initial horizon scheduler owner (laws owner)) stopped
          ⟨some start, startingTrace⟩ := by
    apply model.runBehavioralUntil_congr certificate stopped ⟨some start, startingTrace⟩
    intro later reached _running owner
    obtain ⟨fuel, path⟩ := reached
    rcases later with ⟨state, laterTrace⟩
    have observed := (menu).info initial horizon scheduler owner laterTrace
    change model.infoOf owner laterTrace = (app).observe owner state at observed
    cases state with
    | none => rw [observed]; rfl
    | some current =>
      by_cases active : current.actor = some owner
      · have keptRecall := (app).reaches_recall_prefix initial horizon scheduler
          ((menu).reaches_raw initial horizon scheduler path) start current rfl rfl owner
        simp only [ReactiveApplication.observe, ite_eq_left active] at observed
        rw [observed]
        exact (menu).restrictPolicy_eq_of_law_eq initial horizon scheduler owner _ _ _ _
          (ReactiveApplication.anchoredPolicy_of_extends start.execution laws owner _ _ keptRecall)
      · simp only [ReactiveApplication.observe, ite_eq_right active] at observed
        rw [observed]
        rfl
  let evaluate := fun law : PMF (((menu).protocol initial horizon scheduler).History) =>
    expect law (fun final => value final.state)
  have evaluateBound : ∀ law, |evaluate law| ≤ bound := fun _ =>
    expect_abs_le_of_bounded nonnegative (fun final => valueBound final.state)
  have sampledLaw (start : (app).Control)
      (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
      (head : phase ∈ start.execution.application.phases.head?)
      (same : start.execution.application.attempt = execution.application.attempt) :
      PhaseProposalQualifiedBinding.sampledStopped setup mode runtime leaks bounds plan values
          scheduler PhaseProposalRates.zero stopped ⟨some start, startTrace⟩ =
        model.runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩ := by
    have law := PhaseProposalQualifiedBinding.sampled_base_stopped_marginal setup mode runtime
      leaks bounds plan values scheduler complete covered maximal capacity start startTrace phase
        head kind
    convert law using 1 <;> congr 1 <;>
      first
      | rfl
      | funext history
        dsimp only [stopped, firstExit]
        rw [same]
        cases history.state <;> rfl
  have phaseHead : phase ∈ execution.application.phases.head? := by rw [installed]; rfl
  have sampleLaw := sampledLaw anchor trace phaseHead rfl
  have waitingMarginal := sampledLaw waiting waitTrace phaseHead rfl
  change value (some waiting) ≤ value (some anchor)
  rw [split ⟨some waiting, waitTrace⟩, split ⟨some anchor, trace⟩]
  refine Eq.mp (congrArg₂ (fun first second => evaluate first ≤ evaluate second)
    waitingMarginal sampleLaw) ?_
  dsimp only [evaluate, PhaseProposalQualifiedBinding.sampledStopped]
  rw [expect_bind_tower_bounded _ _ _
      (fun final : ((menu).protocol initial horizon scheduler).History => valueBound final.state),
    expect_bind_tower_bounded _ _ _
      (fun final : ((menu).protocol initial horizon scheduler).History => valueBound final.state)]
  apply expect_mono
  · intro table tableSupported
    let tablePlayers := PhaseProposalQualifiedBinding.baseAliasPolicy setup mode runtime leaks
      bounds plan (PhaseProposalQualifiedBinding.tableValues setup table) PhaseProposalRates.zero
    let tableProfile := PhaseProposalQualifiedBinding.baseAliasStrategy setup mode runtime leaks
      bounds plan (PhaseProposalQualifiedBinding.tableValues setup table) scheduler
        PhaseProposalRates.zero
    let stops := model.runBehavioralUntil certificate tableProfile stopped
    have tableCovered : ∀ owner past view response,
        response ∈ (tablePlayers owner past view).support →
          response ∈ (menu).actions owner past view := by
      intro owner past view response supported
      obtain ⟨chosen, _drawn, rfl⟩ := PMF.support_map .. ▸ supported
      exact chosen.property
    have tableDecoded : (menu).decodeProfile initial horizon scheduler tableProfile =
        tablePlayers := by
      funext owner
      exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler owner _
        (tableCovered owner)
    erw [model.runBehavioralUntil_of_running certificate tableProfile
      (history := ⟨some anchor, trace⟩) (by simp [stopped, firstExit, anchor])
      (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal, anchor]),
      expect_bind_tower_bounded _ _ _
      (fun final : ((menu).protocol initial horizon scheduler).History => valueBound final.state)]
    have order : ∀ next ∈ (model.runBehavioralFrom tableProfile 1 ⟨some anchor, trace⟩).support,
        expect (stops ⟨some waiting, waitTrace⟩) (fun final => value final.state) ≤
          expect (stops next) (fun final => value final.state) := by
      intro next reached
      have projected : next.state ∈
        ((model.runBehavioralFrom tableProfile 1 ⟨some anchor, trace⟩).map History.state).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨next, reached, rfl⟩
      erw [(menu).run_one_response initial horizon scheduler tableProfile
        ⟨some anchor, trace⟩ who remaining execution rfl, tableDecoded] at projected
      obtain ⟨response, drawn, nextState⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
      obtain ⟨_, _, _, _, _, query⟩ := phaseProposalQuery?_genuine_base setup mode runtime leaks
        complete plan maximal horizon scheduler (by
          rw [← initialEq]
          exact (menu).toRawTrace initial horizon scheduler trace) who rfl event payload binding
            request
      have prepared := table_binding_preparation setup mode runtime leaks bounds plan covered table
        scheduler capacity remaining who execution (initialEq ▸ trace) event payload binding
          request
          unsent _ query response drawn
      have sends : response.transmission ≠ none := by
        intro silent
        rw [silent] at prepared
        cases prepared
      have frameEq (action : (app).Action) :
          (execution.respond app who action).application.phases = execution.application.phases ∧
          (execution.respond app who action).application.attempt =
            execution.application.attempt := by
        rcases action with ⟨transmission⟩
        cases transmission <;> exact ⟨rfl, rfl⟩
      obtain ⟨leftTrace, rightTrace, leftResponsePrefix, rightResponsePrefix, closed⟩ :=
        phaseProposalUnflagged_available_send_reset_boundary setup mode runtime leaks bounds plan
          complete covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values fullValues
            tape activationGap processingGap gaps margin capacity remaining execution who response
              ⟨none⟩ trace (tableCovered who _ _ response drawn)
                (PhaseCount.silence_onePacket runtime leaks bounds who _ _) sends phase phaseHead
                  kind witness.checkpoint
      dsimp only at closed
      have byState := (menu).expect_runBehavioralUntil_eq_of_state_eq initial horizon scheduler
        tableProfile certificate stopped (by
          intro first second equal
          dsimp only [stopped, firstExit]
          rw [equal]) value valueBound
      rw [byState ⟨some waiting, waitTrace⟩ ⟨_, rightTrace⟩ rfl,
        byState next ⟨_, leftTrace⟩ nextState.symm]
      let leftLaw := stops ⟨_, leftTrace⟩
      let rightLaw := stops ⟨_, rightTrace⟩
      have pairOrder : ∀ leftFinal ∈ leftLaw.support, ∀ rightFinal ∈ rightLaw.support,
          value rightFinal.state ≤ value leftFinal.state := by
        intro leftFinal leftSupported rightFinal rightSupported
        have liftSupport (start : (app).Control)
            (startingTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
            (head : phase ∈ start.execution.application.phases.head?)
            (attempt : start.execution.application.attempt = execution.application.attempt)
            (final : ((menu).protocol initial horizon scheduler).History)
            (supported : final ∈ (stops ⟨some start, startingTrace⟩).support) :
            final ∈ (model.runBehavioralUntil certificate
              (fun owner => (menu).restrictPolicy initial horizon scheduler owner
                (ReactiveApplication.anchoredPolicy start.execution players owner))
                (firstExit start.execution.application.attempt)
                ⟨some start, startingTrace⟩).support := by
          have stopEq : firstExit start.execution.application.attempt = stopped := by rw [attempt]
          rw [stopEq, reanchor, ← profileEq]
          have member : final ∈ (PhaseProposalQualifiedBinding.sampledStopped setup mode runtime
              leaks bounds plan values scheduler PhaseProposalRates.zero stopped
                ⟨some start, startingTrace⟩).support :=
            (PMF.mem_support_bind_iff _ _ _).mpr ⟨table, tableSupported, supported⟩
          exact (congrArg (fun law : PMF
            (((menu).protocol initial horizon scheduler).History) => final ∈ law.support)
              (sampledLaw start startingTrace head attempt)).mp member
        obtain ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior,
          leftJoint, rightJoint, leftLegal, rightLegal, leftRealized, rightRealized,
          leftRaw, rightRaw, leftState, rightState, leftPrefix, rightPrefix,
          leftEndPrefix, rightEndPrefix, leftSame, rightSame, leftEffect, rightEffect,
          _leftHead, _rightHead, leftFinished, rightFinished, leftIdle, rightIdle,
          leftChanged, rightChanged, leftNormalized, rightNormalized,
          leftCoverage, rightCoverage, leftExcluded, rightExcluded, archiveEq,
          _leftAcceptance, _rightAcceptance, _foreignAcceptance, survival⟩ :=
            closed leftFinal (by
              have member := liftSupport _ leftTrace ((frameEq response).1.symm ▸ phaseHead)
                (frameEq response).2 _ leftSupported
              convert member using 1
              dsimp only [firstExit, model, certificate, horizon, players, scheduler]
              congr 2
              funext history
              cases history.state <;> rfl)
              rightFinal (by
                have member := liftSupport _ rightTrace ((frameEq ⟨none⟩).1.symm ▸ phaseHead)
                  (frameEq ⟨none⟩).2 _ rightSupported
                convert member using 1
                dsimp only [firstExit, model, certificate, horizon, players, scheduler]
                congr 2
                funext history
                cases history.state <;> rfl)
        by_cases excluded : who ∈ rightEnding.execution.application.current.excluded
        · have fixed := phase_excluded_expected_payoff setup mode runtime leaks utility
            excludedPayoff menu initial horizon scheduler certificate profile who rightFinal
              (by simpa only [PhaseExcluded, rightState] using excluded)
          rw [← terminalValue rightFinal, fixed]
          have floor : ∀ state, excludedPayoff who ≤ payoff state := by
            intro state
            cases state with
            | none => exact defaultFloor
            | some control =>
              change excludedPayoff who ≤ if who ∈ control.execution.application.current.excluded
                then excludedPayoff who else (phaseSourceReadout setup mode runtime leaks
                  (some control)).elim 0 (fun terminal => utility terminal who)
              split_ifs
              · exact le_rfl
              · cases phaseSourceReadout setup mode runtime leaks (some control) with
                | none => exact defaultFloor
                | some terminal => exact terminalFloor terminal
          simpa only [expect_constant] using expect_mono
            (μ := (app).finish initial horizon scheduler players leftFinal.state)
            (f := fun _ => excludedPayoff who) (g := payoff) (fun state _ => floor state)
            (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _ bounded)
        obtain ⟨leftSurvives, _rightAccepted, _leftAccepted, _footprintEq, excludedEq,
          _retiredEq, resetSources⟩ := survival excluded
        let before : Bool → (app).Control := fun side => if side then rightBefore else leftBefore
        let ending : Bool → (app).Control := fun side => if side then rightEnding else leftEnding
        let raw : Bool → RecoveryState (graph) := fun side => if side then rightRaw else leftRaw
        have rawFalse : raw false = leftRaw := by simp [raw]
        have rawTrue : raw true = rightRaw := by simp [raw]
        have endingFalse : ending false = leftEnding := by simp [ending]
        have endingTrue : ending true = rightEnding := by simp [ending]
        let priors : ∀ side, ((menu).protocol initial horizon scheduler).Trace
            (some (before side)) := fun side => match side with
          | false => leftPrior | true => rightPrior
        let traces : ∀ side, ((menu).protocol initial horizon scheduler).Trace
            (some (ending side)) := fun side => match side with
          | false => leftState ▸ leftFinal.trace | true => rightState ▸ rightFinal.trace
        have kept : ∀ side, TracePrefix trace (priors side) := by
          intro side; cases side
          · exact leftResponsePrefix.trans leftPrefix
          · exact rightResponsePrefix.trans rightPrefix
        have same : ∀ side, (before side).execution.application.attempt =
            execution.application.attempt := by intro side; cases side <;> assumption
        have effects : ∀ side, PhaseClosingEffect runtime leaks (before side).execution
            (ending side).execution (raw side) := by intro side; cases side <;> assumption
        have changed : ∀ side, (ending side).execution.application.attempt ≠
            (before side).execution.application.attempt := by
          intro side; cases side
          · exact fun equal => leftChanged (equal.trans leftSame)
          · exact fun equal => rightChanged (equal.trans rightSame)
        have normalized : ∀ side, (ending side).execution.application =
            ({ (before side).execution.application with current := raw side } :
              PhaseRuntimeState (graph)).normalize := by intro side; cases side <;> assumption
        have finished : ∀ side, phase.Finished (phase.drain (raw side)) := by
          intro side; cases side <;> assumption
        have entries : ∀ side, (before side).execution.application.entry =
            execution.application.entry := by
          intro side
          have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon
            scheduler initialized ((menu).toRawTrace initial horizon scheduler trace)
          exact ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
            scheduler anchor (before side) trace (priors side) (kept side) ordered).2.2
              (same side).symm).symm
        have beforeInstalled :
            ∀ side, (before side).execution.application.phases = phase :: rest := by
          intro side
          exact (phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds plan
            horizon scheduler anchor (before side) trace (priors side) (kept side)
              (same side).symm).1.trans installed
        have imageE : ∀ side, (phase.drain (raw side)).excluded =
            (ending side).execution.application.current.excluded := by
          intro side; cases side <;> assumption
        have coverage := fun side => phaseClosingEffect_checkpoint_facts setup mode runtime leaks
          bounds plan horizon scheduler (before side) (ending side) (priors side) (raw side)
            (effects side) (changed side)
        have inherited : ∀ side, execution.application.current.excluded ⊆
            (ending side).execution.application.current.excluded := by
          intro side
          rw [sameExcluded, ← entries side, ← imageE side, phase.drain_excluded]
          exact (coverage side).2.2.2.2.2.inherited
        have idle : ∀ side, (ending side).actor = none := by
          intro side; cases side <;> assumption
        let endpointProfile := fun side owner => (menu).restrictPolicy initial horizon scheduler
          owner (ReactiveApplication.anchoredPolicy (ending side).execution players owner)
        have endpointValue (side : Bool) :
            expect (model.runBehavioralTerminalFrom certificate (endpointProfile side)
              ⟨some (ending side), traces side⟩) (fun final => payoff final.state) =
                value (some (ending side)) := by
          have law := (menu).terminal_run_restrict_eq_finish initial horizon scheduler certificate
            (ReactiveApplication.anchoredPolicy (ending side).execution players)
              ((menu).admissible_of_covered initial horizon scheduler _
                (fun owner => (menu).anchoredPolicy_covered initial horizon scheduler (ending side)
                  (traces side) players owner
                    (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan
                      values owner))) ⟨some (ending side), traces side⟩
          simpa only [model, endpointProfile, value, expect_map, Function.comp_def,
            ReactiveApplication.finish, ReactiveApplication.resume, idle side, PMF.pure_bind,
            ReactiveApplication.runRounds_anchoredPolicy] using
              congrArg (fun law => expect law payoff) law
        rw [rightState, leftState]
        by_cases reset :
            ((phase.drain rightRaw).excluded \ execution.application.entry.excluded).Nonempty
        · have missed : ∀ side, (((phase.drain (raw side)).excluded \
              (before side).execution.application.entry.excluded) ∩ phase.owners).Nonempty := by
            intro side
            have failure : ((phase.drain (raw side)).excluded \
                (before side).execution.application.entry.excluded).Nonempty := by
              rw [entries side]
              cases side
              · rw [rawFalse]; exact excludedEq.symm ▸ reset
              · rw [rawTrue]; exact reset
            obtain ⟨owner, member⟩ := failure
            have receipts := (coverage side).2.2.1
            have record := (receipts.exclusion.installed phase (by
              simp only [beforeInstalled side, List.head?_cons, Option.mem_some_iff])).phase_drain
                phase
            rcases (record.excluded owner).mp (Finset.mem_sdiff.mp member).1 with
              old | ⟨failedEvent, lower, acting, failed⟩
            · exact ((Finset.mem_sdiff.mp member).2 old).elim
            · have within := receipts.exclusion.frontier.positioned
              change PhaseRuntimeState.Positioned _ _ _ at within
              rw [show ({ (before side).execution.application with current := raw side } :
                PhaseRuntimeState (graph)).phases = phase :: rest from beforeInstalled side]
                at within
              exact ⟨owner, Finset.mem_inter.mpr ⟨member, Finset.mem_biUnion.mpr
                ⟨failedEvent, (phase.mem_events _).mpr
                  ⟨lower, (phase.drain_within (raw side) within.2).2 _ failed.completed⟩,
                    by simpa only [Option.mem_toFinset, Option.mem_def] using acting⟩⟩⟩
          have own : who ∈ phase.owners := Finset.mem_biUnion.mpr
            ⟨event, inside, by simpa only [Option.mem_toFinset, Option.mem_def] using
              (graph).actor?_of_outputLayout_binding binding⟩
          have survivors :
              ∀ side, (phase.owners \ (phase.drain (raw side)).excluded).Nonempty := by
            intro side
            refine ⟨who, Finset.mem_sdiff.mpr ⟨own, ?_⟩⟩
            rw [imageE side]
            cases side
            · exact leftSurvives
            · exact excluded
          have laws := phaseProposal_original_reset_payoff_law_eq setup mode runtime leaks bounds
            plan complete covered maximal values fullValues tape activationGap processingGap gaps
              margin capacity utility excludedPayoff anchor trace witness archived proper
                phase rest
                installed kind before ending priors traces kept same idle changed raw effects
                  normalized finished missed survivors inherited archiveEq (resetSources reset) who
          have averaged := congrArg (fun law : PMF ℝ => expect law id) laws
          simp only [expect_map, Function.comp_def, id_eq] at averaged
          rw [endpointValue false, endpointValue true] at averaged
          exact averaged.symm.le
        have clean : ∀ side, (phase.drain (raw side)).excluded =
            execution.application.entry.excluded := by
          have right := Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp
            (Finset.not_nonempty_iff_eq_empty.mp reset))
              (by simpa only [endingTrue, ← sameExcluded, rightExcluded] using inherited true)
          intro side; cases side
          · rw [rawFalse]; exact excludedEq.trans right
          · rw [rawTrue]; exact right
        have leftInitial := (ReactiveApplication.consistentRecall_policyInvariant
          (ReactiveApplication.anchoredPolicy execution tablePlayers)).respond execution who
            response
            (ReactiveApplication.anchoredPolicy_consistent execution tablePlayers) (by
              rw [ReactiveApplication.anchoredPolicy_of_extends execution tablePlayers who _ _
                (List.prefix_refl _)]
              exact drawn)
        have leftFaithful := table_stopped_consistent setup mode runtime leaks bounds plan table
          scheduler anchor trace ⟨remaining, none, execution.respond app who response⟩ leftTrace
            leftResponsePrefix stopped leftInitial leftFinal leftSupported
        have rightFaithful := table_stopped_consistent setup mode runtime leaks bounds plan table
          scheduler waiting rightTrace waiting rightTrace .refl stopped
            (ReactiveApplication.anchoredPolicy_consistent waiting.execution tablePlayers)
              rightFinal rightSupported
        have leftConsistent : ∀ owner,
            (ReactiveApplication.anchoredPolicy execution tablePlayers owner).Consistent
              (leftBefore.execution.recall owner) := by
          intro owner
          have keptRecall := (app).reaches_recall_prefix initial horizon scheduler
            ((menu).reaches_raw initial horizon scheduler
              ((TracePrefix.extend .refl leftJoint leftLegal leftRealized).trans
                leftEndPrefix).reachesWithin) leftBefore leftEnding rfl leftState owner
          obtain ⟨tail, equality⟩ := keptRecall
          simp only [ReactiveApplication.executionInvariant, leftState] at leftFaithful
          exact ReactiveApplication.Policy.Consistent.of_append (equality ▸ leftFaithful owner)
        have rightConsistent : ∀ owner,
            (ReactiveApplication.anchoredPolicy waiting.execution tablePlayers owner).Consistent
              (rightBefore.execution.recall owner) := by
          intro owner
          have keptRecall := (app).reaches_recall_prefix initial horizon scheduler
            ((menu).reaches_raw initial horizon scheduler
              ((TracePrefix.extend .refl rightJoint rightLegal rightRealized).trans
                rightEndPrefix).reachesWithin) rightBefore rightEnding rfl rightState owner
          obtain ⟨tail, equality⟩ := keptRecall
          simp only [ReactiveApplication.executionInvariant, rightState] at rightFaithful
          exact ReactiveApplication.Policy.Consistent.of_append (equality ▸ rightFaithful owner)
        have outputs := table_closing_binding_values_eq setup mode runtime leaks bounds plan
          complete
          covered maximal table scheduler capacity remaining who execution trace rightTrace
            rightResponsePrefix
            phase (by simp only [installed, List.head?_cons, Option.mem_some_iff]) kind
              leftBefore rightBefore leftEnding rightEnding leftPrior rightPrior
                (kept false) rightPrefix leftSame rightSame
                  leftRaw rightRaw leftEffect rightEffect (changed false) (changed true)
                    leftFinished rightFinished (clean false) (clean true) leftConsistent
                      rightConsistent
        have successes := table_closing_binding_values_success setup mode runtime leaks bounds plan
          complete covered maximal table scheduler capacity remaining who execution trace rightTrace
            witness phase rest installed kind event payload binding request
              unsent noCurrent
              (by simpa only [sameExcluded] using foreign) rightBefore rightEnding rightPrior
                rightPrefix rightSame rightRaw rightEffect
                  (changed true) rightFinished (clean true) rightConsistent
        let q0 := setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
        let sourceLaw := setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0
        let completedState := fun side => (⟨rest, (before side).execution.application.generation,
          phase.drain (raw side), phase.drain (raw side),
            (before side).execution.application.retired⟩ : PhaseRuntimeState (graph))
        have joins (side : Bool) : ∃ completed : RecoverySourceWitness setup mode plan
            (completedState side),
            (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
              ⟨_, witness.checkpoint.trace⟩ ⟨_, completed.checkpoint.trace⟩) ∧
            setup.recoveryJointRecall completed.checkpoint.trace =
              (witness.checkpoint.commitInstructionWord (phase.drain (raw side)).native).reverse ++
                setup.recoveryJointRecall witness.checkpoint.trace ∧
            (match commitPhase witness.checkpoint.residual.tail with
            | ⟨_, _, suffix, block, reconstruct, _⟩ => phaseProposalBindingWord setup.program block
                suffix (cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
                  (outputLayout setup.program) program) reconstruct.symm)
                    witness.checkpoint.embedding)
                  execution.application.entry.excluded (phase.drain (raw side)).native.config.store
                    witness.checkpoint.source) =
                witness.checkpoint.commitInstructionWord (phase.drain (raw side)).native ∧
            value (some (ending side)) = expect (sourceLaw ⟨_, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup (PhaseProposal.sourceArchive
                (ending side).execution.network.inputs)) completed.checkpoint.trace⟩)
                  (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
          obtain ⟨beforeW, beforeArchive, beforeHistory, saved, checkpointEq⟩ :=
            RecoverySourceWitness.prefix_at_same_attempt setup mode runtime leaks bounds plan
              maximal
              scheduler anchor (before side) trace (priors side) (kept side) (same side) witness
                archived
          obtain ⟨rawW, rawCheckpoint, rawHistory⟩ := RecoverySourceWitness.raw_closing_checkpoint
            setup mode runtime leaks plan (before side) (ending side) beforeW (raw side)
              (effects side) (changed side)
          have cleanBefore := (clean side).trans (congrArg RecoveryState.excluded saved).symm
          have committing := beforeW.checkpoint.compiled.atCommit_of_bindingPhase setup.program
            mode
            beforeW.checkpoint.residual.tail beforeW.checkpoint.refs
              beforeW.checkpoint.source.revelations beforeW.checkpoint.registry
                beforeW.checkpoint.embedding beforeW.checkpoint.before
                  (before side).execution.application.attempt.phase phase kind (by
                    simp only [PhaseRuntimeState.attempt, beforeInstalled side, List.head?_cons,
                      Option.map_some, Option.getD_some]) beforeW.checkpoint.source
          obtain ⟨_cp, _point, _path, _settled, readout⟩ :=
            beforeW.checkpoint.ordinary_closing_binding_checkpoint setup mode runtime leaks bounds
              plan maximal horizon scheduler (before side) (ending side) (priors side) committing
                phase rest (beforeInstalled side) kind (raw side) (effects side) (changed side)
                  (normalized side) (finished side) cleanBefore
          rw [checkpointEq] at readout
          obtain ⟨completed, point, ⟨fuel, path, instructions⟩, delta, settled⟩ :=
            rawW.completed_binding_history maximal phase rest (beforeInstalled side) kind
              (finished side) (by rw [cleanBefore]; simp)
          have rawRead := beforeW.checkpoint.transfer_binding_readback
            (other := { (before side).execution.application with current := raw side })
              rfl rfl rfl (phase.drain (raw side))
          have beforeRead := witness.checkpoint.transfer_binding_readback saved
            (congrArg CommitAttemptId.generation (same side))
              (congrArg CommitAttemptId.phase (same side)) (phase.drain (raw side))
          have wordRead := readout
          rw [beforeRead.2] at wordRead
          simp only [RecoverySourceCheckpoint.transfer, saved] at wordRead
          have wordEq : rawW.checkpoint.commitInstructionWord (phase.drain (raw side)).native =
              witness.checkpoint.commitInstructionWord (phase.drain (raw side)).native := by
            rw [rawCheckpoint, rawRead.2, checkpointEq, beforeRead.2]
          have historyEq := rawHistory.trans beforeHistory
          have recallEq := congrArg (fun h : setup.commitRecoveryProtocol.History =>
            setup.recoveryJointRecall h.trace) historyEq
          rw [wordEq, recallEq] at instructions
          have allValues := completed_binding_source_values setup mode plan maximal _ rawW phase
            rest (beforeInstalled side) kind (finished side) cleanBefore
              (coverage side).2.2.2.2.2 (by
                intro owner active
                rw [rawCheckpoint, checkpointEq]
                apply proper owner
                change owner ∉ execution.application.current.excluded
                rw [sameExcluded]
                simpa only [entries side] using active) (by
                intro current member owner ty typed active
                have value := successes current member owner ty typed (by
                  simpa only [entries side] using active)
                cases side
                · rcases value with ⟨v, read⟩
                  refine ⟨v, (FieldRef.get?_congr _ _ _ ?_).trans read⟩
                  change (phase.drain (raw false)).native.config.outputs current =
                    (phase.drain rightRaw).native.config.outputs current
                  rw [rawFalse]; exact outputs current member
                · exact value)
          have completedProper : ∀ owner, owner ∉ (phase.drain (raw side)).excluded →
              completed.checkpoint.source.BindingsHoldValues owner := by
            intro owner active
            apply (ProtocolState.bindingsHoldValues_entry owner completed.checkpoint.residual.tail
              _).mp
            apply (completed.checkpoint.origin.bindingsHoldValues_lift owner _).mp
            rw [point]
            exact allValues owner (cleanBefore ▸ active)
          have settledEq := (normalized side).trans settled
          obtain ⟨next, nextPath, sourceKernel, _delta, nextArchived⟩ :=
            RecoverySourceWitness.completed_normalized_archived_source setup mode runtime leaks
              bounds plan maximal horizon scheduler (before side) (ending side) (priors side)
                beforeW beforeArchive (raw side) (effects side) rawW rawCheckpoint phase rest
                  (beforeInstalled side) (finished side) (normalized side) settledEq completed
                    delta
                    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0
          let finalW : RecoverySourceWitness setup mode plan (ending side).execution.application :=
            settledEq.symm ▸ next
          have castFacts {state other : PhaseRuntimeState (graph)} (equal : state = other)
              (w : RecoverySourceWitness setup mode plan state) :
              ((equal ▸ w).checkpoint.ArchivedProposals (ending side).execution.network.inputs ↔
                w.checkpoint.ArchivedProposals (ending side).execution.network.inputs) ∧
              (∀ owner, (equal ▸ w).checkpoint.source.BindingsHoldValues owner ↔
                w.checkpoint.source.BindingsHoldValues owner) ∧
              ((⟨_, (equal ▸ w).checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
                ⟨_, w.checkpoint.trace⟩) := by cases equal; exact ⟨Iff.rfl, fun _ => Iff.rfl, rfl⟩
          have transported := castFacts settledEq.symm next
          have finalArchive : finalW.checkpoint.ArchivedProposals
              (ending side).execution.network.inputs := transported.1.mpr nextArchived
          have preserved := (completed.checkpoint.fresh_normalization_source_law mode rest
            (before side).execution.application.generation (phase.drain (raw side))
              (before side).execution.application.retired completed.order.frontier next.checkpoint
                (Classical.choose_spec nextPath) q0
                  (nativeArchiveLabels setup (PhaseProposal.sourceArchive
                    (ending side).execution.network.inputs))).2
          have finalProper :
              ∀ owner, owner ∉ (ending side).execution.application.current.excluded →
              finalW.checkpoint.source.BindingsHoldValues owner := by
            intro owner active
            have value : next.checkpoint.source.BindingsHoldValues owner :=
              preserved owner ((imageE side).symm ▸ active)
                (completedProper owner ((imageE side).symm ▸ active))
            change (settledEq.symm ▸ next).checkpoint.source.BindingsHoldValues owner
            apply (transported.2.1 owner).mpr
            intro name payload cell
            exact value cell
          have fresh : ∀ owner, ∀ record ∈ (ending side).execution.recall owner,
              record.beforeView.application.2.attempt ≠
                (ending side).execution.application.attempt := by
            rcases effects side with ⟨id, message, result, _found, moved, _handled, _rawEq⟩ |
              ⟨command, result, moved, _supported, _rawEq⟩ <;>
              exact phase_ownRecall_fresh_after_environment runtime leaks initial initialized
                horizon scheduler (before side)
                  ((menu).toRawTrace initial horizon scheduler (priors side))
                    (ending side).execution _ moved (Ne.symm (changed side))
          have finalLaw := phaseProposal_fresh_finish_payoff_law setup mode runtime leaks bounds
            plan
            complete covered maximal values fullValues tape activationGap processingGap gaps margin
              capacity utility excludedPayoff (ending side) (idle side) (traces side)
                (by rw [normalized side]
                    apply PhaseRuntimeState.normalize_entry_excluded_of_changed
                    rw [← normalized side]; exact changed side) fresh finalW finalArchive
                      finalProper who
          have lifted := congrArg (fun h : setup.commitRecoveryProtocol.History =>
            (⟨h.state, setup.proposalRecoveryLiftTrace (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive (ending side).execution.network.inputs)) h.trace⟩ :
                setup.proposalRecoveryProtocol.History)) transported.2.2
          rw [lifted, ← sourceKernel] at finalLaw
          refine ⟨completed, ⟨fuel, historyEq ▸ path⟩, instructions, ?_, ?_⟩
          · have pack {Γ : SourceCtx Player L} {O : Finset VarId}
                (program : SourceProgram Player L Γ O)
                (embedding : OutputEmbedding (inputLayout setup.context)
                  (outputLayout setup.program) program) (entry : SourceProgram.Config Player L Γ)
                (excluded : Finset Player) (store : Store (graphLayout setup.program))
                (word : List (Player → Option (CommitRecoveryMove Player L))) :
                (match commitPhase program with
                | ⟨_, _, suffix, block, reconstruct, _⟩ =>
                  phaseProposalBindingWord setup.program block suffix
                    (cast (congrArg (fun p => OutputEmbedding (inputLayout setup.context)
                      (outputLayout setup.program) p) reconstruct.symm) embedding)
                    excluded store entry = word) →
                (match commitPhase program with
                | ⟨_, _, suffix, block, reconstruct, _⟩ =>
                  phaseProposalBindingWord setup.program block suffix
                    (cast (congrArg (fun p => OutputEmbedding (inputLayout setup.context)
                      (outputLayout setup.program) p) reconstruct.symm) embedding)
                    excluded store entry) = word := by
              generalize _decomposition : commitPhase program = segment; cases segment; exact id
            apply pack; simpa only [anchor, entries side] using wordRead
          · simpa only [expect_map, Function.comp_def, id_eq] using
              congrArg (fun law : PMF ℝ => expect law id) finalLaw
        choose completed paths words readouts laws using joins
        have instructionEq :
            witness.checkpoint.commitInstructionWord (phase.drain (raw false)).native =
            witness.checkpoint.commitInstructionWord (phase.drain (raw true)).native := by
          have geometry := witness.checkpoint.commit_phase_geometry phase rest installed kind
            witness.order.frontier (maximal.suffix witness.suffix)
          rw [← readouts false, ← readouts true]
          generalize decomposition :
          commitPhase witness.checkpoint.residual.tail = segment at geometry ⊢
          rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
          apply phaseProposalBindingWord_congr setup.program block suffix _
            execution.application.entry.excluded _ _ witness.checkpoint.source
          intro owner active index member owned
          apply FieldRef.get?_congr
          change (phase.drain (raw false)).native.config.outputs _ =
            (phase.drain (raw true)).native.config.outputs _
          rw [rawFalse, rawTrue]; exact outputs _ (geometry.2 index member)
        have committing := witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
          witness.checkpoint.residual.tail witness.checkpoint.refs
            witness.checkpoint.source.revelations
            witness.checkpoint.registry witness.checkpoint.embedding witness.checkpoint.before
              execution.application.attempt.phase phase kind (by
                simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
                  Option.getD_some]) witness.checkpoint.source
        have historyEq : (⟨_, (completed false).checkpoint.trace⟩ :
            setup.commitRecoveryProtocol.History) = ⟨_, (completed true).checkpoint.trace⟩ := by
          obtain ⟨leftFuel, leftPath⟩ := paths false
          obtain ⟨rightFuel, rightPath⟩ := paths true
          apply setup.commitRecovery_history_eq_of_commit_window _ witness.checkpoint.trace
            ((witness.checkpoint.atCommit _).trans committing) _ _ leftPath rightPath
          · rw [words false, words true, instructionEq]
          · have length := congrArg List.length (words false)
            simp only [setup.recoveryJointRecall_length, List.length_append, List.length_reverse]
              at length
            have window := witness.checkpoint.commit_instruction_word_window
              (phase.drain (raw false)).native
            change (completed false).checkpoint.trace.length + ProtocolState.commitEnd setup.program
                (witness.checkpoint.residual.lift (ProtocolState.entry
                  witness.checkpoint.residual.tail witness.checkpoint.source)) ≤
              witness.checkpoint.trace.length + ProtocolState.remaining setup.program
                (witness.checkpoint.residual.lift (ProtocolState.entry
                  witness.checkpoint.residual.tail witness.checkpoint.source))
            omega
        change value (some (ending true)) ≤ value (some (ending false))
        rw [laws false, laws true]
        have lifted := congrArg (fun h : setup.commitRecoveryProtocol.History =>
          (⟨h.state, setup.proposalRecoveryLiftTrace (nativeArchiveLabels setup
            (PhaseProposal.sourceArchive leftEnding.execution.network.inputs)) h.trace⟩ :
              setup.proposalRecoveryProtocol.History)) historyEq
        simpa only [endingFalse, endingTrue, archiveEq] using (congrArg
          (fun h => expect (sourceLaw h) (setup.proposalRecoveryPayoff utility excludedPayoff who))
            lifted).symm.le
      have averaged := expect_mono (μ := leftLaw)
        (f := fun _ => expect rightLaw (fun final => value final.state))
        (g := fun final => value final.state)
        (fun left member => expect_le_const rightLaw _
          (payoffIntegrable_of_bounded _ _ (fun final => valueBound final.state)) _
            (pairOrder left member)) (payoffIntegrable_constant _ _)
          (payoffIntegrable_of_bounded _ _ (fun final => valueBound final.state))
      simpa only [expect_constant] using averaged
    have averaged := expect_mono
      (μ := model.runBehavioralFrom tableProfile 1 ⟨some anchor, trace⟩)
      (f := fun _ => expect (stops ⟨some waiting, waitTrace⟩) (fun final => value final.state))
      (g := fun next => expect (stops next) (fun final => value final.state)) order
      (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _ (fun _ => evaluateBound _))
    simpa only [expect_constant] using averaged
  · exact payoffIntegrable_of_bounded _ _ (fun _ => evaluateBound _)
  · exact payoffIntegrable_of_bounded _ _ (fun _ => evaluateBound _)

end Vegas

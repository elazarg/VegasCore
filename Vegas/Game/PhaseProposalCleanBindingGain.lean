/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalQualifiedBinding
import GameTheoryExtensions.Math.Probability.ConditioningCost
import Vegas.Game.PhaseCommitmentProposalArchive
import Vegas.Game.PhaseProposalAttemptArchive
import Vegas.Game.PhaseProposalCoupledQuery
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.PhaseFiniteNature
import Interaction.ReactiveFiniteAssessment
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
import GameTheoryExtensions.Math.Probability.PresentConditional
import GameTheoryExtensions.Math.Probability.RetainedGain
import Vegas.Game.AsyncDeviationForeign
import Vegas.Game.ProposalRecoveryFutureFlags

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

omit runtime leaks bounds in
/-- A newly failed current-block field is unresolved at the completed source
point. This uses the actual decoded attempt, including inherited exclusions. -/
private theorem completed_binding_failed_field
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (state : PhaseRuntimeState (graph))
    (witness : RecoverySourceWitness setup mode plan state)
    (phase : RuntimePhase (graph)) (rest : List (RuntimePhase (graph)))
    (installed : state.phases = phase :: rest) (kind : phase.kind = .commitment)
    (finished : phase.Finished (phase.drain state.current))
    (clean : (phase.drain state.current).excluded = state.entry.excluded)
    (coverage : state.FailureCoverage)
    (who : Player) (active : who ∉ state.entry.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (failed : (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding who payload)).get?
      (phase.drain state.current).native.config.store = some .failure) :
    ProtocolState.FailedBinding who setup.program
      (witness.checkpoint.commitResultPoint (phase.drain state.current)) := by
  classical
  have geometry := witness.checkpoint.commit_phase_geometry phase rest installed kind
    witness.order.frontier (maximal.suffix witness.suffix)
  apply witness.checkpoint.commitResultPoint_failedBinding (phase.drain state.current) who
  generalize decomposition : commitPhase witness.checkpoint.residual.tail = segment at geometry ⊢
  rcases segment with ⟨Δ, names, suffix, block, reconstruct, boundary⟩
  dsimp only at geometry ⊢
  let embedding := cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
      witness.checkpoint.embedding
  let image := phase.drain state.current
  let decoded := decodeCommitAttempt setup.program mode block suffix embedding image.native
    witness.checkpoint.source state.entry.excluded
  have rankTransport {first second : SourceProgram Player L
      witness.checkpoint.residual.context witness.checkpoint.residual.names}
      (eq : first = second)
      (e : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) second)
      (rank : ∀ i, (e.event i).val = state.attempt.phase + i.val) :
      ∀ i, ((cast (congrArg (fun p => OutputEmbedding (inputLayout setup.context)
        (outputLayout setup.program) p) eq.symm) e).event i).val =
          state.attempt.phase + i.val := by cases eq; exact rank
  have ranks := rankTransport reconstruct witness.checkpoint.embedding
    witness.checkpoint.compiled.rankEq
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have interval := (phase.mem_events event).mp inside
  let index : Fin (eventCount (block.prepend suffix)) :=
    ⟨event.val - state.attempt.phase, by
      have bound := block.eventCount_prepend suffix
      omega⟩
  have indexed : embedding.event index = event := Fin.ext (by
    rw [ranks]
    dsimp only [index]
    omega)
  have typed : outputLayout (block.prepend suffix) index = .binding who payload :=
    (embedding.layout_eq index).symm.trans (indexed.symm ▸ binding)
  have debt := filled_failed_binding_field setup block suffix embedding
    image.native.config.store witness.checkpoint.source witness.checkpoint.unique who payload
      index (by dsimp only [index]; omega) typed ⟨.inr event, binding⟩
        (congrArg Sum.inr indexed.symm) failed
  have after : decoded.2.1 = state.entry.excluded := by
    rw [decodeCommitAttempt_excluded_eq_public_prefix setup.program mode block suffix embedding
      state.attempt.phase ranks image.native (fun i hi => finished (geometry.2 i hi))]
    apply Finset.union_eq_left.mpr
    intro owner member
    obtain ⟨selected, _lower, _upper, actor, missing⟩ := (Finset.mem_filter.mp member).2
    rw [← clean]
    exact (coverage.active.drain phase).covered selected owner actor missing
  have same := decodeCommitAttempt_surviving_view_eq_fill setup.program mode block suffix
    embedding image.native (phase.drain_bindingInvariant state.current witness.binding.active)
      who witness.checkpoint.source witness.checkpoint.source state.entry.excluded rfl
        (fun i hi _ => finished (geometry.2 i hi)) (after.symm ▸ active)
  exact debt.of_sourceObserve_eq (congrArg Prod.fst same).symm

omit mode runtime leaks bounds plan in
open Classical in
/-- Removing source flags keeps the same installed local law on both sides;
all other focal and foreign future responses retain their ordinary values. -/
private theorem source_flags_after_same_local_law
    (scale bad : Set.Icc (0 : ℝ) 1)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (law : PMF (setup.proposalRecoveryModel.Choice who information))
    (history : setup.proposalRecoveryProtocol.History) (fuel : Nat) :
    let ordinary := PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values
    let flagged := setup.proposalRecoveryNormalizedTrembledProfile
      scale.val scale.property.1 scale.property.2 bad.val bad.property.1 bad.property.2
      scale.val scale.property.1 scale.property.2 values
    PMF.WithinTV ((Fintype.card Player * fuel : Nat) * (2 * scale.val + bad.val))
      (setup.proposalRecoveryModel.runBehavioralFrom
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who
          ((ordinary who).withLaw information law)) fuel history)
      (setup.proposalRecoveryModel.runBehavioralFrom
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) flagged who
          ((flagged who).withLaw information law)) fuel history) := by
  intro ordinary flagged
  let keep := (1 - scale.val) * (1 - bad.val) * (1 - scale.val)
  have firstNonnegative : 0 ≤ (1 - scale.val) * (1 - bad.val) :=
    mul_nonneg (sub_nonneg.mpr scale.property.2) (sub_nonneg.mpr bad.property.2)
  have firstSmall : (1 - scale.val) * (1 - bad.val) ≤ 1 :=
    (mul_le_of_le_one_right (sub_nonneg.mpr scale.property.2)
      (by linarith [bad.property.1])).trans (by linarith [scale.property.1])
  have keepNonnegative : 0 ≤ keep :=
    mul_nonneg firstNonnegative (sub_nonneg.mpr scale.property.2)
  have keepSmall : keep ≤ 1 :=
    (mul_le_of_le_one_right firstNonnegative
      (by linarith [scale.property.1])).trans firstSmall
  have missing : 1 - keep ≤ 2 * scale.val + bad.val := by
    have second := mul_le_of_le_one_left bad.property.1
      (by linarith [scale.property.1] : 1 - scale.val ≤ 1)
    have third := mul_le_of_le_one_left scale.property.1 firstSmall
    dsimp only [keep]
    nlinarith [second, third]
  have lower (owner : Player)
      (info : setup.proposalRecoveryModel.InfoState owner)
      (choice : setup.proposalRecoveryModel.Choice owner info) :
      keep * ((ordinary owner info) choice).toReal ≤ ((flagged owner info) choice).toReal :=
    setup.proposalRecoveryNormalizedTrembledProfile_ordinary_lower
      scale.val scale.property.1 scale.property.2 bad.val bad.property.1 bad.property.2
      scale.val scale.property.1 scale.property.2 values owner info choice
  have close := setup.proposalRecoveryModel.runBehavioralFrom_withinTV_of_supported_choices
    (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who
      ((ordinary who).withLaw information law))
    (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) flagged who
      ((flagged who).withLaw information law)) keep keepNonnegative keepSmall history (by
        intro _ next _ owner choice
        by_cases own : owner = who
        · subst owner
          simp only [Profile.update_same]
          by_cases current : setup.proposalRecoveryModel.infoOf who next.trace = information
          · have same : (ordinary who).withLaw information law
                (setup.proposalRecoveryModel.infoOf who next.trace) =
              (flagged who).withLaw information law
                (setup.proposalRecoveryModel.infoOf who next.trace) := by
              rw [current, InformationModel.BehavioralPolicy.withLaw_self,
                InformationModel.BehavioralPolicy.withLaw_self]
            rw [same]
            exact mul_le_of_le_one_left ENNReal.toReal_nonneg keepSmall
          · rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ current,
              InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ current]
            exact lower who _ choice
        · simp only [Profile.update_of_ne _ _ own]
          exact lower owner _ choice) fuel
  apply close.mono
  exact (one_sub_pow_le_mul keepNonnegative (Fintype.card Player * fuel)).trans
    (mul_le_mul_of_nonneg_left missing (Nat.cast_nonneg _))

omit mode runtime leaks bounds plan in
open Classical in
private theorem conditioned_gain_le [Fintype setup.proposalRecoveryProtocol.History]
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (source : setup.proposalRecoveryModel.BehavioralAssessment)
    (present : ∃ history ∈
        {history : setup.proposalRecoveryModel.InformationHistory who site.1 |
          setup.proposalRecoveryForeignGood who history.val},
      history ∈ (source.belief who site).support)
    (gain : setup.proposalRecoveryModel.InformationHistory who site.1 → ℝ)
    (bound : ℝ) (bounded : ∀ history, |gain history| ≤ 2 * bound) :
    expect ((source.belief who site).filter
        {history | setup.proposalRecoveryForeignGood who history.val} present)
        gain ≤ expect (source.belief who site) gain +
      4 * bound * (∑ history : setup.proposalRecoveryModel.InformationHistory who site.1 with
        (∃ owner : Player, who ≠ owner ∧ setup.GeneratedPreparationHistory owner history.val),
        (source.belief who site history).toReal) := by
  let belief := source.belief who site
  let good : Set (setup.proposalRecoveryModel.InformationHistory who site.1) :=
    {history | setup.proposalRecoveryForeignGood who history.val}
  have compared := abs_expect_filter_sub_le belief good present gain (-2 * bound) (4 * bound)
    (fun history _ => by
      have interval := abs_le.mp (bounded history)
      constructor <;> linarith)
  have comparison := (abs_le.mp compared).2
  have negated (history) : history ∉ good ↔
      ∃ owner : Player, who ≠ owner ∧ setup.GeneratedPreparationHistory owner history.val := by
    simp only [good, Set.mem_ofPred_eq, Setup.proposalRecoveryForeignGood]
    push Not
    simp only [ne_comm]
  have complement : (belief.toOuterMeasure goodᶜ).toReal =
      ∑ history : setup.proposalRecoveryModel.InformationHistory who site.1 with
        (∃ owner : Player, who ≠ owner ∧ setup.GeneratedPreparationHistory owner history.val),
        (belief history).toReal := by
    rw [← expect_indicator]
    unfold expect
    rw [tsum_fintype, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro history _
    simp only [Set.mem_compl_iff, negated, mul_ite, mul_one, mul_zero]
  rw [complement] at comparison
  dsimp only [belief, good] at comparison
  linarith

omit mode runtime leaks bounds plan in
open Classical in
private theorem source_unflagged_gain_le
    (scale bad : Set.Icc (0 : ℝ) 1)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (source : setup.proposalRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      source.strategy owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2 bad.val bad.property.1 bad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (law : PMF (setup.proposalRecoveryModel.Choice who site.1))
    (payoff : setup.proposalRecoveryProtocol.History → Player → ℝ)
    (bound : ℝ) (payoffBound : ∀ history, |payoff history who| ≤ bound) (fuel : Nat) :
    let ordinary : setup.proposalRecoveryModel.BehavioralAssessment :=
      ⟨PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values, source.belief⟩
    setup.proposalRecoveryModel.localGain fuel id payoff ordinary site law ≤
      setup.proposalRecoveryModel.localGain fuel id payoff source site law +
        4 * bound * ((Fintype.card Player * fuel : Nat) * (2 * scale.val + bad.val)) := by
  intro ordinary
  let flagged := setup.proposalRecoveryNormalizedTrembledProfile
    scale.val scale.property.1 scale.property.2 bad.val bad.property.1 bad.property.2
    scale.val scale.property.1 scale.property.2 values
  let error : ℝ := (Fintype.card Player * fuel : Nat) * (2 * scale.val + bad.val)
  have actual (history : setup.proposalRecoveryProtocol.History) :
      setup.proposalRecoveryModel.runBehavioralFrom flagged fuel history =
        setup.proposalRecoveryModel.runBehavioralFrom source.strategy fuel history := by
    apply setup.proposalRecoveryModel.runBehavioralFrom_congr
    intro later _ running owner
    exact (prescribed owner later running).symm
  have alternative (history : setup.proposalRecoveryProtocol.History) :
      setup.proposalRecoveryModel.runBehavioralFrom
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) flagged who
          ((flagged who).withLaw site.1 law)) fuel history =
      setup.proposalRecoveryModel.runBehavioralFrom
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
          source.strategy who ((source.strategy who).withLaw site.1 law)) fuel history := by
    apply setup.proposalRecoveryModel.runBehavioralFrom_congr
    intro later _ running owner
    by_cases own : owner = who
    · subst owner
      simp only [Profile.update_same]
      by_cases selected : setup.proposalRecoveryModel.infoOf who later.trace = site.1
      · rw [selected, InformationModel.BehavioralPolicy.withLaw_self,
          InformationModel.BehavioralPolicy.withLaw_self]
      · rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ selected,
          InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ selected]
        exact (prescribed who later running).symm
    · simp only [Profile.update_of_ne _ _ own]
      exact (prescribed owner later running).symm
  have closeAlternative : PMF.WithinTV error
      (setup.proposalRecoveryModel.localRun fuel ordinary site law)
      (setup.proposalRecoveryModel.localRun fuel source site law) := by
    rw [InformationModel.localRun_eq_bind, InformationModel.localRun_eq_bind]
    apply PMF.WithinTV.bind_right (source.belief who site)
    intro history _
    change PMF.WithinTV error
      (setup.proposalRecoveryModel.runBehavioralFrom _ fuel history.val)
      (setup.proposalRecoveryModel.runBehavioralFrom _ fuel history.val)
    rw [← alternative]
    exact source_flags_after_same_local_law setup scale bad values who site.1 law history.val fuel
  have closeBaseline : PMF.WithinTV error
      (setup.proposalRecoveryModel.localRun fuel ordinary site (ordinary.strategy who site.1))
      (setup.proposalRecoveryModel.localRun fuel source site (source.strategy who site.1)) := by
    change PMF.WithinTV error
      ((source.belief who site).bind fun history => setup.proposalRecoveryModel.runBehavioralFrom
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary.strategy
          who ((ordinary.strategy who).withLaw site.1
            (ordinary.strategy who site.1))) fuel history.val)
      ((source.belief who site).bind fun history => setup.proposalRecoveryModel.runBehavioralFrom
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) source.strategy
          who ((source.strategy who).withLaw site.1
            (source.strategy who site.1))) fuel history.val)
    simp only [InformationModel.BehavioralPolicy.withLaw_eq_self,
      Profile.update_eq_self]
    apply PMF.WithinTV.bind_right (source.belief who site)
    intro history _
    rw [← actual]
    change PMF.WithinTV error
      (setup.proposalRecoveryModel.runBehavioralFrom
        (PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values) fuel history.val)
      (setup.proposalRecoveryModel.runBehavioralFrom flagged fuel history.val)
    simpa only [error, PhaseProposalQualifiedBinding.sourceUnflaggedStrategy, flagged,
      two_mul, add_assoc, add_comm, add_left_comm] using
      setup.proposalRecovery_future_flags_withinTV scale.val scale.property.1 scale.property.2
        bad.val bad.property.1 bad.property.2 scale.val scale.property.1 scale.property.2
          values history.val fuel
  have interval : ∀ history : setup.proposalRecoveryProtocol.History,
      -bound ≤ payoff history who ∧ payoff history who ≤ -bound + 2 * bound := by
    intro history
    have limited := abs_le.mp (payoffBound history)
    constructor <;> linarith
  have first := closeAlternative.expect_sub_le (payoff · who) (-bound) (2 * bound)
    (fun history _ => interval history)
  have second := closeBaseline.symm.expect_sub_le (payoff · who) (-bound) (2 * bound)
    (fun history _ => interval history)
  simp only [InformationModel.localGain_eq_sub,
    InformationModel.localValue_eq_expect_localRun, id_eq] at first second ⊢
  dsimp only [error] at first second
  linarith

omit mode runtime leaks bounds plan in
open Classical in
private theorem source_causal_gain_le [Fintype setup.proposalRecoveryProtocol.History]
    (scale bad : Set.Icc (0 : ℝ) 1)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (source : setup.proposalRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      source.strategy owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2 bad.val bad.property.1 bad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (positive : ∃ history ∈
        {history : setup.proposalRecoveryModel.InformationHistory who site.1 |
          setup.proposalRecoveryForeignGood who history.val},
      history ∈ (source.belief who site).support)
    (choice : setup.proposalRecoveryModel.Choice who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (payoffBound : ∀ history,
      |setup.proposalRecoveryPayoff utility excludedPayoff who history| ≤ bound) :
    let ordinary := PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values
    let causal := fun selected => PhaseProposalQualifiedBinding.sourceCausalPayoff setup values
      source who site selected positive utility excludedPayoff
    expect (causal choice) (fun result => result.getD 0) -
        expect ((ordinary who site.1).bind causal) (fun result => result.getD 0) ≤
      setup.proposalRecoveryModel.localGain
        ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) id
        (fun history owner => setup.proposalRecoveryPayoff utility excludedPayoff owner history)
        source site (PMF.pure choice) +
      4 * bound * ((∑ history : setup.proposalRecoveryModel.InformationHistory who site.1 with
          (∃ owner : Player, who ≠ owner ∧ setup.GeneratedPreparationHistory owner history.val),
          (source.belief who site history).toReal) +
        (Fintype.card Player * ((Fintype.card Player + 1) *
          (instructionCount setup.program + 1)) : Nat) * (2 * scale.val + bad.val)) := by
  intro ordinary causal
  let certificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  let fuel := (Fintype.card Player + 1) * (instructionCount setup.program + 1)
  let payoff := setup.proposalRecoveryPayoff utility excludedPayoff who
  let belief := (source.belief who site).filter
    {history | setup.proposalRecoveryForeignGood who history.val} positive
  let mean := fun history : setup.proposalRecoveryModel.InformationHistory who site.1 =>
    expect (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate ordinary history.val)
      payoff
  let selected := fun (history : setup.proposalRecoveryModel.InformationHistory who site.1)
      (move : setup.proposalRecoveryModel.Choice who site.1) =>
    expect (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who
        ((ordinary who).commit site.1 move)) history.val) payoff
  have meanBound (history) : |mean history| ≤ bound :=
    expect_abs_le_of_bounded nonnegative payoffBound
  have selectedBound (history) (move) : |selected history move| ≤ bound :=
    expect_abs_le_of_bounded nonnegative payoffBound
  have causalLaw (move) : causal move =
      (belief.bind fun history => setup.proposalRecoveryModel.runBehavioralTerminalFrom
        certificate (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
          ordinary who ((ordinary who).commit site.1 move)) history.val).map
            (fun terminal => some (payoff terminal)) := by
    change (belief.bind fun history =>
      ((setup.proposalRecoveryModel.runBehavioralFrom _ 1 history.val).bind
        (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate ordinary)).map
          (fun terminal => some (payoff terminal))) = _
    rw [PMF.map_bind]
    apply bind_congr_on_support
    intro history _
    have consumed := setup.proposalRecoveryModel.runBehavioralTerminalFrom_commit_eq_bind
      certificate (setup.proposalRecoveryModel.actsOnceWhereItMatters_of_perfectRecall
        setup.proposalRecoveryModel_perfectRecall) ordinary who history.val
          (history.property.symm ▸ move)
    have commitCast {first second : setup.proposalRecoveryModel.InfoState who}
        (same : first = second) (selected : setup.proposalRecoveryModel.Choice who second) :
        (ordinary who).commit first (same.symm ▸ selected) =
          (ordinary who).commit second selected := by
      cases same
      rfl
    rw [commitCast history.property move] at consumed
    exact congrArg (PMF.map fun terminal => some (payoff terminal)) consumed.symm
  have causalBound (move) (result) (member : result ∈ (causal move).support) :
      |result.getD 0| ≤ bound := by
    rw [causalLaw] at member
    obtain ⟨terminal, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact payoffBound terminal
  have causalMean (move) : expect (causal move) (fun result => result.getD 0) =
      expect belief (fun history => selected history move) := by
    rw [causalLaw, expect_map]
    exact expect_bind_tower_bounded _ _ _ payoffBound
  have baseline (history : setup.proposalRecoveryModel.InformationHistory who site.1) :
      expect (ordinary who site.1) (selected history) = mean history := by
    by_cases ended : setup.proposalRecoveryProtocol.terminal history.val.state
    · have fixed (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner) :
          setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile history.val =
            PMF.pure history.val := by
          exact setup.proposalRecoveryProtocol.randomizedBackwardLaw_of_terminal ended
      simp only [selected, mean, fixed, expect_pure, expect_constant]
    · have affine := setup.proposalRecoveryModel.runBehavioralTerminalFrom_update_withLaw_eq_bind
        certificate (setup.proposalRecoveryModel.actsOnceWhereItMatters_of_perfectRecall
          setup.proposalRecoveryModel_perfectRecall) ordinary who (ordinary who) site.1
          (ordinary who site.1) history.val history.property ended
            (InformationModel.InformationSite.active setup.proposalRecoveryModel site history)
      simp only [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self]
        at affine
      have integrated := congrArg (fun law => expect law payoff) affine
      rw [expect_bind_tower_bounded _ _ _ payoffBound] at integrated
      exact integrated.symm
  have baselineMean : expect ((ordinary who site.1).bind causal) (fun result => result.getD 0) =
      expect belief mean := by
    have integrable : PayoffIntegrable ((ordinary who site.1).bind causal)
        (fun result => result.getD 0) := by
      refine payoffIntegrable_of_bounded_on_support _ _ (C := bound) ?_
      intro result member
      obtain ⟨move, _supported, drawn⟩ := (PMF.mem_support_bind_iff ..).mp member
      exact causalBound move result drawn
    rw [expect_bind_tower _ _ _ integrable]
    simp_rw [causalMean]
    let _ := setup.proposalRecoveryModel.finite_choice_of_played
      (setup.proposalRecoveryModel.site_mem_playedInformation site)
    rw [expect_comm_of_support_finite_left (ordinary who site.1) belief (Set.toFinite _)
      (fun move history => selected history move)
      (fun move _ => payoffIntegrable_of_bounded _ _ (fun history => selectedBound history move))]
    exact expect_congr_on_support (fun history _ => baseline history)
  let ordinaryAssessment : setup.proposalRecoveryModel.BehavioralAssessment :=
    ⟨ordinary, source.belief⟩
  have unfiltered : expect (source.belief who site)
      (fun history => selected history choice - mean history) =
      setup.proposalRecoveryModel.localGain fuel id
        (fun history owner => setup.proposalRecoveryPayoff utility excludedPayoff owner history)
        ordinaryAssessment site (PMF.pure choice) := by
    rw [expect_sub (payoffIntegrable_of_bounded _ _ (fun h => selectedBound h choice))
      (payoffIntegrable_of_bounded _ _ meanBound), InformationModel.localGain_eq_sub,
      InformationModel.localValue_eq_expect_localRun,
      InformationModel.localValue_eq_expect_localRun,
      setup.proposalRecoveryModel.expect_localRun,
      setup.proposalRecoveryModel.expect_localRun]
    congr 1
    · apply expect_congr_on_support
      intro history _
      change expect (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who
            ((ordinary who).commit site.1 choice)) history.val) payoff =
        expect (setup.proposalRecoveryModel.runBehavioralFrom
          (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who
            ((ordinary who).commit site.1 choice)) fuel history.val) payoff
      exact congrArg (fun law => expect law payoff)
        (setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
          certificate setup.proposalRecoveryProtocol_bounded _ _)
    · apply expect_congr_on_support
      intro history _
      change mean history = expect (setup.proposalRecoveryModel.runBehavioralFrom
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who
          ((ordinary who).withLaw site.1 (ordinary who site.1))) fuel history.val) payoff
      rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self]
      exact congrArg (fun law => expect law payoff)
        (setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
          certificate setup.proposalRecoveryProtocol_bounded _ _)
  have conditioning := conditioned_gain_le setup who site source positive
    (fun history => selected history choice - mean history) bound (by
      intro history
      exact (abs_sub _ _).trans (by linarith [selectedBound history choice, meanBound history]))
  rw [expect_sub (payoffIntegrable_of_bounded _ _ (fun h => selectedBound h choice))
    (payoffIntegrable_of_bounded _ _ meanBound), unfiltered] at conditioning
  have flags := source_unflagged_gain_le setup scale bad values source prescribed who site
    (PMF.pure choice) (fun history owner =>
      setup.proposalRecoveryPayoff utility excludedPayoff owner history) bound payoffBound fuel
  rw [causalMean, baselineMean]
  dsimp only [ordinaryAssessment, fuel] at conditioning flags
  linarith

private theorem failed_current_binding_finish
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some before))
    (trace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ending))
    (witness : RecoverySourceWitness setup mode plan before.execution.application)
    (phase : RuntimePhase (graph)) (rest : List (RuntimePhase (graph)))
    (installed : before.execution.application.phases = phase :: rest)
    (kind : phase.kind = .commitment) (raw : RecoveryState (graph))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (clean : (phase.drain raw).excluded = before.execution.application.entry.excluded)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } : PhaseRuntimeState (graph)).normalize)
    (idle : ending.actor = none) (who : Player)
    (active : who ∉ before.execution.application.entry.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (failed : (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding who payload)).get?
      (phase.drain raw).native.config.store = some .failure)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (players : Player → (app).Policy)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    expect ((app).finish initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape) players
        (some ending)) (fun state =>
          phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who) =
      excludedPayoff who := by
  classical
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  obtain ⟨rawWitness, _checkpoint, _history⟩ := RecoverySourceWitness.raw_closing_checkpoint
    setup mode runtime leaks plan before ending witness raw effect changed
  obtain ⟨_native, _binding, _receipts, _stored, _remembered, coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending prior raw effect changed
  have debt := completed_binding_failed_field setup mode plan maximal
    ({ before.execution.application with current := raw } : PhaseRuntimeState (graph)) rawWitness
      phase rest installed kind finished clean coverage who active event inside payload
        binding failed
  obtain ⟨next, owed, _rest⟩ := rawWitness.completed_binding_checkpointDebt mode plan maximal
    phase rest installed kind finished (by rw [clean]; simp) who debt
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories sourceProfile (fun _ _ => false)
  have checkpointDebt : PhaseCheckpointDebt setup mode plan who ending.execution.application := by
    rw [normalized]
    exact ⟨next, owed⟩
  have rawTrace := (menu).toRawTrace initial horizon scheduler trace
  have idleTrace : ((app).protocol initial horizon scheduler).Trace
      (some ⟨ending.remaining, none, ending.execution⟩) := by
    simpa only [← idle] using rawTrace
  change expect ((app).finish initial horizon scheduler players (some ending)) _ = _
  simp only [ReactiveApplication.finish, idle, ReactiveApplication.resume, PMF.pure_bind,
    expect_map]
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)]
  · exact expect_constant _ _
  intro final reached
  obtain ⟨finalTrace⟩ := (app).raw_trace_runRounds initial horizon scheduler players 0
    ending.remaining ending.execution final (by simpa only [Nat.zero_add] using idleTrace)
      reached
  have completed := (ReservedEpoch.terminal_history_complete runtime leaks tape plan
    (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs
      ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩).1
  exact phaseCheckpointDebt_terminal_payoff setup mode runtime leaks plan maximal inputs horizon
    scheduler players ending.remaining ending.execution final idleTrace who checkpointDebt reached
      completed utility excludedPayoff

private theorem clean_send_complement
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (wellFormed : setup.WellFormed)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (fullValues : ∀ owner key, FullSupport (values owner key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (timely : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
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
    (foreign : ∀ owner, owner ≠ who → owner ∉ execution.application.current.excluded →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial
        (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape) owner
          ⟨some ⟨remaining, some who, execution⟩, trace⟩)
    (left right : (app).Action)
    (leftSupported : left ∈ (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
      values who (execution.recall who) (execution.observe app who)).support)
    (rightAvailable : right ∈ (menu).actions who (execution.recall who)
      (execution.observe app who))
    (nonsilent : right.transmission ≠ none)
    (removeQualified : Bool)
    (bad : removeQualified = false → right.transmission.bind PhaseProposal.bindingPreparation =
      none)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ bound)
    (excludedBound : |excludedPayoff who| ≤ bound)
    (defaultFloor : excludedPayoff who ≤ 0)
    (terminalFloor : ∀ terminal, excludedPayoff who ≤ utility terminal who) :
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let stop := fun next : (app).Execution =>
      next.application.attempt ≠ execution.application.attempt
    let value := fun ending : (app).Execution =>
      if removeQualified = true ∧ ending.application.attempt ≠ execution.application.attempt ∧
          ending.application.current.excluded = execution.application.entry.excluded then 0 else
        expect ((app).finish initial horizon scheduler players
          (some ⟨horizon - ending.environmentRecall.length, none, ending⟩))
            (fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
              state who)
    expect ((app).runUntil scheduler players stop remaining (execution.respond app who right))
        value ≤
      expect ((app).runUntil scheduler players stop remaining (execution.respond app who left))
        value := by
  classical
  intro horizon scheduler players stop value
  let model := (menu).information initial horizon scheduler
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  let payoff := fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
    state who
  let finishValue := fun state => expect ((app).finish initial horizon scheduler players state)
    payoff
  have bounded : ∀ state, |payoff state| ≤ bound := by
    intro state
    have interval := phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
      (fun _ => -bound) (fun _ => bound)
      (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).1)
      (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).2) state who
    have excluded := abs_le.mp excludedBound
    apply abs_le.mpr
    simpa only [min_eq_right excluded.1, min_eq_right (neg_nonpos.mpr nonnegative),
      max_eq_right excluded.2, max_eq_right nonnegative, Set.mem_Icc] using interval
  have floor : ∀ state, excludedPayoff who ≤ payoff state := by
    intro state
    cases state with
    | none => exact defaultFloor
    | some control =>
        change excludedPayoff who ≤ if who ∈ control.execution.application.current.excluded then
          excludedPayoff who else (phaseSourceReadout setup mode runtime leaks (some control)).elim
            0 (fun terminal => utility terminal who)
        split_ifs
        · exact le_rfl
        · cases phaseSourceReadout setup mode runtime leaks (some control) with
          | none => exact defaultFloor
          | some terminal => exact terminalFloor terminal
  have finishBound : ∀ state, |finishValue state| ≤ bound := fun _ =>
    expect_abs_le_of_bounded nonnegative bounded
  have finishFloor : ∀ state, excludedPayoff who ≤ finishValue state := by
    intro state
    simpa only [expect_constant] using expect_mono
      (μ := (app).finish initial horizon scheduler players state)
      (f := fun _ => excludedPayoff who) (g := payoff) (fun state _ => floor state)
        (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _ bounded)
  let anchor : (app).Control := ⟨remaining, some who, execution⟩
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler (initialEq ▸ trace)
  have proper := witness.bindingsHoldValues_of_no_saved_failure_and_foreign_good setup mode
    wellFormed runtime leaks bounds plan maximal horizon scheduler anchor trace who event payload
      binding request noSaved foreign
  obtain ⟨phase, rest, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks plan
    (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
      ((menu).toRawTrace initial horizon scheduler trace) who event payload binding request.2.2.1
  have phaseInstalled : phase ∈ execution.application.phases.head? :=
    Option.mem_def.mpr ((congrArg List.head? installed).trans rfl)
  obtain ⟨_material, _value, sent, _typed⟩ := phaseProposalUnflaggedBinding_supported_usable setup
    mode runtime leaks bounds plan complete covered maximal values fullValues horizon scheduler
      capacity remaining who execution (initialEq ▸ trace) event payload binding request unsent
        left leftSupported
  obtain ⟨leftTrace, rightTrace, leftOrigin, rightOrigin, paired⟩ :=
    phaseProposalUnflagged_available_send_reset_boundary setup mode runtime leaks bounds plan
      complete covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values fullValues
        tape activationGap processingGap gaps timely capacity remaining execution who left right
          trace (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
            who _ _ left leftSupported) rightAvailable
          (fun absent => by rw [absent] at sent; cases sent) phase
          phaseInstalled kind witness.checkpoint
  let responseAnchor := fun response : (app).Action => execution.respond app who response
  let anchored := fun response => ReactiveApplication.anchoredPolicy (responseAnchor response)
    players
  let profile := fun response owner => (menu).restrictPolicy initial horizon scheduler owner
    (anchored response owner)
  let stopped := fun final : ((menu).protocol initial horizon scheduler).History =>
    match final.state with | none => False | some control => stop control.execution
  let reward := fun state : (app).ProtocolState => match state with
    | none => 0
    | some control => if removeQualified = true ∧
        control.execution.application.attempt ≠ execution.application.attempt ∧
        control.execution.application.current.excluded = execution.application.entry.excluded
      then 0 else finishValue state
  have rewardBound : ∀ state, |reward state| ≤ bound := by
    intro state
    cases state <;> dsimp only [reward]
    · simpa only [abs_zero] using nonnegative
    · split_ifs
      · simpa only [abs_zero] using nonnegative
      · exact finishBound _
  have physical (response : (app).Action)
      (responseTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, responseAnchor response⟩)) :
      expect (model.runBehavioralUntil certificate (profile response) stopped
        ⟨some ⟨remaining, none, responseAnchor response⟩, responseTrace⟩)
          (fun final => reward final.state) =
        expect ((app).runUntil scheduler players stop remaining
          (responseAnchor response)) value := by
    have decoded : (menu).decodeProfile initial horizon scheduler (profile response) =
        anchored response := by
      funext owner
      apply (menu).decode_restrictPolicy_of_covered initial horizon scheduler owner
      exact (menu).anchoredPolicy_covered initial horizon scheduler
        ⟨remaining, none, responseAnchor response⟩ responseTrace players owner
          (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values owner)
    have law := PhaseProposalQualifiedBinding.attemptUntil_state setup mode runtime leaks bounds
      initial scheduler (profile response) execution.application.attempt remaining
        (responseAnchor response) responseTrace
    rw [decoded, ReactiveApplication.runUntil_anchoredPolicy_of_extends scheduler
      (responseAnchor response) players stop remaining (responseAnchor response)
        (fun _ => List.prefix_rfl)] at law
    have runner : (model.runBehavioralUntil certificate (profile response) stopped
        ⟨some ⟨remaining, none, responseAnchor response⟩, responseTrace⟩).map History.state =
        ((app).runUntil scheduler players stop remaining (responseAnchor response)).map
          (fun ending => (some ⟨horizon - ending.environmentRecall.length, none, ending⟩ :
            (app).ProtocolState)) := by
      convert law using 1
      dsimp only [model, stopped, stop, horizon, certificate]
      congr 2
      funext final
      cases final.state <;> rfl
    have integrated := congrArg (fun distribution => expect distribution reward) runner
    simpa only [expect_map, reward, finishValue, value, Function.comp_def] using integrated
  rw [← physical right rightTrace, ← physical left leftTrace]
  suffices order : ∀ leftFinal ∈ (model.runBehavioralUntil certificate (profile left) stopped
      ⟨some ⟨remaining, none, responseAnchor left⟩, leftTrace⟩).support,
      ∀ rightFinal ∈ (model.runBehavioralUntil certificate (profile right) stopped
        ⟨some ⟨remaining, none, responseAnchor right⟩, rightTrace⟩).support,
      reward rightFinal.state ≤ reward leftFinal.state by
    have averaged := expect_mono
      (μ := model.runBehavioralUntil certificate (profile left) stopped
        ⟨some ⟨remaining, none, responseAnchor left⟩, leftTrace⟩)
      (f := fun _ => expect (model.runBehavioralUntil certificate (profile right) stopped
        ⟨some ⟨remaining, none, responseAnchor right⟩, rightTrace⟩) (fun final => reward
          final.state))
      (g := fun final => reward final.state)
      (fun left member => expect_le_const _ _
        (payoffIntegrable_of_bounded _ _ (fun final :
          ((menu).protocol initial horizon scheduler).History => rewardBound final.state)) _
          (order left member)) (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_bounded _ _ (fun final :
        ((menu).protocol initial horizon scheduler).History => rewardBound final.state))
    simpa only [expect_constant] using averaged
  intro leftFinal leftReached rightFinal rightReached
  dsimp only at paired
  have responseAttempt (response : (app).Action) :
      (execution.respond app who response).application.attempt =
        execution.application.attempt := by
    rcases response with ⟨_ | material⟩ <;> rfl
  obtain ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior,
    leftJoint, rightJoint, leftLegal, rightLegal, leftRealized, rightRealized, leftRaw, rightRaw,
    leftState, rightState, leftPrefix, rightPrefix, leftEndPrefix, rightEndPrefix,
    leftSame, rightSame, leftEffect, rightEffect, _leftHead, _rightHead,
    leftFinished, rightFinished, leftIdle, rightIdle, leftChanged, rightChanged,
    leftNormalized, rightNormalized, _leftCoverage, _rightCoverage, leftExcluded, rightExcluded,
    archiveEq, _leftAcceptance, _rightAcceptance, _foreignAcceptance, survival⟩ :=
      paired leftFinal (by
        convert leftReached using 1
        dsimp only [model, certificate, horizon, players, scheduler]
        congr 2
        funext final
        dsimp only [stopped, stop]
        cases final.state <;> simp only [responseAttempt])
        rightFinal (by
          convert rightReached using 1
          dsimp only [model, certificate, horizon, players, scheduler]
          congr 2
          funext final
          dsimp only [stopped, stop]
          cases final.state <;> simp only [responseAttempt])
  by_cases excluded : who ∈ rightEnding.execution.application.current.excluded
  · have fixed : finishValue rightFinal.state = excludedPayoff who := by
      have terminalLaw := (menu).terminal_run_restrict_eq_finish initial horizon scheduler
        certificate players ((menu).admissible_of_covered initial horizon scheduler players
          (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values))
            rightFinal
      have forced := phase_excluded_expected_payoff setup mode runtime leaks utility excludedPayoff
        menu initial horizon scheduler certificate
        (fun owner => (menu).restrictPolicy initial horizon scheduler owner (players owner)) who
          rightFinal (by simpa only [PhaseExcluded, rightState] using excluded)
      have expectation := congrArg (fun law => expect law payoff) terminalLaw
      simp only [expect_map, Function.comp_def] at expectation
      exact expectation.symm.trans forced
    have leftFloor : excludedPayoff who ≤ reward leftFinal.state := by
      rw [leftState]
      dsimp only [reward]
      split_ifs
      · exact defaultFloor
      · exact finishFloor _
    have active : who ∉ execution.application.entry.excluded := by
      exact fun member => request.2.2.2.2
        (witness.exclusions.coverage.inherited member)
    have notClean : rightEnding.execution.application.current.excluded ≠
        execution.application.entry.excluded := fun same => active (same ▸ excluded)
    simpa only [reward, rightState, notClean, and_false, ite_false] using fixed.le.trans leftFloor
  obtain ⟨leftSurvives, _rightAccepted, _leftAccepted, _footprint, excludedEq, _retired,
    resetSources⟩ := survival excluded
  let before : Bool → (app).Control := fun side => if side then rightBefore else leftBefore
  let ending : Bool → (app).Control := fun side => if side then rightEnding else leftEnding
  let raw : Bool → RecoveryState (graph) := fun side => if side then rightRaw else leftRaw
  let priors : ∀ side, ((menu).protocol initial horizon scheduler).Trace (some (before side)) :=
    fun side => match side with | false => leftPrior | true => rightPrior
  let traces : ∀ side, ((menu).protocol initial horizon scheduler).Trace (some (ending side)) :=
    fun side => match side with | false => leftState ▸ leftFinal.trace | true => rightState ▸
      rightFinal.trace
  have kept : ∀ side, TracePrefix trace (priors side) := by
    intro side; cases side
    · exact leftOrigin.trans leftPrefix
    · exact rightOrigin.trans rightPrefix
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
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler trace)
  have entries : ∀ side, (before side).execution.application.entry = execution.application.entry
    := by
    intro side
    exact ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
      scheduler
      anchor (before side) trace (priors side) (kept side) ordered).2.2 (same side).symm).symm
  have rightEntry : rightBefore.execution.application.entry = execution.application.entry :=
    entries true
  have beforeInstalled : ∀ side, (before side).execution.application.phases = phase :: rest := by
    intro side
    exact (phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds plan horizon
      scheduler anchor (before side) trace (priors side) (kept side) (same side).symm).1.trans
        installed
  have beforeHead (side) : phase ∈ (before side).execution.application.phases.head? :=
    Option.mem_def.mpr ((congrArg List.head? (beforeInstalled side)).trans rfl)
  have idle : ∀ side, (ending side).actor = none := by
    intro side
    cases side <;> assumption
  have images : ∀ side, (phase.drain (raw side)).excluded =
      (ending side).execution.application.current.excluded := by intro side; cases side <;>
        assumption
  have cleanEq : leftEnding.execution.application.current.excluded =
      rightEnding.execution.application.current.excluded := leftExcluded.symm.trans
        (excludedEq.trans rightExcluded)
  by_cases clean : rightEnding.execution.application.current.excluded =
    execution.application.entry.excluded
  · by_cases remove : removeQualified = true
    · have leftNew : leftEnding.execution.application.attempt ≠
          execution.application.attempt := leftChanged
      have rightNew : rightEnding.execution.application.attempt ≠
          execution.application.attempt := rightChanged
      have zeroRight : reward rightFinal.state = 0 := by
        rw [rightState]
        exact ite_eq_left ⟨remove, rightNew, clean⟩
      have zeroLeft : reward leftFinal.state = 0 := by
        rw [leftState]
        exact ite_eq_left ⟨remove, leftNew, cleanEq.trans clean⟩
      exact le_of_eq (zeroRight.trans zeroLeft.symm)
    have retain : removeQualified = false := Bool.eq_false_of_not_eq_true remove
    have missingPreparation := bad retain
    obtain ⟨material, transmitted⟩ := Option.ne_none_iff_exists'.mp nonsilent
    have rightEq : right = ⟨some material⟩ := by
      cases right
      exact congrArg ReactiveApplication.Action.mk transmitted
    have available : (⟨some material⟩ : (app).Action) ∈ (menu).actions who
        (execution.recall who) (execution.observe app who) := rightEq ▸ rightAvailable
    obtain ⟨serial, opening, evidence, shape, _bounded, _fresh⟩ :=
      PhaseCount.onePacket_binding_shape runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
          execution trace event payload binding request material available
    have badValue : opening.bind (fun value => value.as? payload) = none := by
      rw [rightEq, shape] at missingPreparation
      simpa only [PhaseProposal.bindingPreparation, binding, Option.bind_some,
        Option.map_eq_none_iff] using missingPreparation
    obtain ⟨rightWitness, _archive, _history, _saved, _cp⟩ :=
      RecoverySourceWitness.prefix_at_same_attempt setup mode runtime leaks bounds plan maximal
        scheduler anchor rightBefore trace rightPrior (rightOrigin.trans rightPrefix) rightSame
          witness archived
    obtain ⟨emitted, recalled⟩ := (app).respond_recall_entry execution who right
    change ((responseAnchor right).recall who = execution.recall who ++
      [⟨execution.observe app who, right, emitted⟩]) at recalled
    let record : (app).PlayerEntry := ⟨execution.observe app who, right, emitted⟩
    have recordPresent : record ∈ rightBefore.execution.recall who := by
      have retainedRecall := (app).reaches_recall_prefix initial horizon scheduler
        ((menu).reaches_raw initial horizon scheduler rightPrefix.reachesWithin)
          ⟨remaining, none, responseAnchor right⟩ rightBefore rfl rfl who
      apply List.IsPrefix.subset retainedRecall
      rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self record)
    have lower : rightBefore.execution.application.attempt.phase ≤ event.val := by
      rw [rightSame]
      have ranks := (phase.mem_events event).mp inside
      change execution.application.phases = phase :: rest at installed
      simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
        Option.getD_some] using ranks.1
    have failed := closing_recorded_binding_material setup mode runtime leaks bounds plan horizon
      scheduler rightBefore rightEnding rightPrior phase rightRaw rightEffect
        (changed true) rightFinished who event inside payload binding lower
          (rightExcluded.symm ▸ excluded) serial opening evidence record recordPresent
          (by dsimp only [record]; rw [rightEq, shape])
          (by dsimp only [record]; exact rightSame.symm)
    rw [badValue] at failed
    have active : who ∉ rightBefore.execution.application.entry.excluded := by
      rw [rightEntry, ← clean]
      exact excluded
    have fixed := failed_current_binding_finish setup mode runtime leaks bounds plan maximal tape
      rightBefore rightEnding rightPrior (rightState ▸ rightFinal.trace) rightWitness phase
        rest (beforeInstalled true) kind rightRaw rightEffect (changed true) rightFinished
          ((rightExcluded.trans clean).trans (congrArg RecoveryState.excluded rightEntry).symm)
            rightNormalized rightIdle who
            active event inside payload binding failed
              (PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values) players utility
                excludedPayoff
    simpa only [reward, leftState, rightState, retain, Bool.false_eq_true, false_and, ite_false,
      finishValue] using fixed.le.trans (finishFloor leftFinal.state)
  · have reset : ((phase.drain rightRaw).excluded \
    execution.application.entry.excluded).Nonempty := by
      apply Finset.sdiff_nonempty.mpr
      intro contained
      apply clean
      apply Finset.Subset.antisymm
      · rwa [← rightExcluded]
      · have facts := phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan
          horizon scheduler rightBefore rightEnding rightPrior rightRaw rightEffect (changed true)
        have record := (facts.2.2.1.exclusion.installed phase (beforeHead true)).phase_drain phase
        intro owner member
        rw [← rightExcluded]
        exact (record.excluded owner).mpr
          (Or.inl ((congrArg RecoveryState.excluded rightEntry).symm ▸ member))
    have missed : ∀ side, (((phase.drain (raw side)).excluded \
        (before side).execution.application.entry.excluded) ∩ phase.owners).Nonempty := by
      intro side
      obtain ⟨_native, _binding, receipts, _stored, _remembered, _coverage⟩ :=
        phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
          (before side) (ending side) (priors side) (raw side) (effects side) (changed side)
      obtain ⟨owner, member⟩ := reset
      have present : owner ∈ (phase.drain (raw side)).excluded := by
        cases side
        · change owner ∈ (phase.drain leftRaw).excluded
          rw [excludedEq]
          exact (Finset.mem_sdiff.mp member).1
        · change owner ∈ (phase.drain rightRaw).excluded
          exact (Finset.mem_sdiff.mp member).1
      have active : owner ∉ (before side).execution.application.entry.excluded := by
        rw [entries side]; exact (Finset.mem_sdiff.mp member).2
      have record := (receipts.exclusion.installed phase (beforeHead side)).phase_drain phase
      rcases (record.excluded owner).mp present with old | ⟨failedEvent, lower, acting, failed⟩
      · exact (active old).elim
      · have positioned := receipts.exclusion.frontier.positioned
        change PhaseRuntimeState.Positioned _ _ _ at positioned
        rw [show ({ (before side).execution.application with current := raw side } :
          PhaseRuntimeState (graph)).phases = phase :: rest from beforeInstalled side] at positioned
        have upper := (phase.drain_within (raw side) positioned.2).2 failedEvent failed.completed
        exact ⟨owner, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨present, active⟩,
          Finset.mem_biUnion.mpr ⟨failedEvent, (phase.mem_events failedEvent).mpr ⟨lower, upper⟩,
            by simpa only [Option.mem_toFinset, Option.mem_def] using acting⟩⟩⟩
    have owned : who ∈ phase.owners := Finset.mem_biUnion.mpr ⟨event, inside,
      by simpa only [Option.mem_toFinset, Option.mem_def] using request.2.2.2.1⟩
    have survivors : ∀ side, (phase.owners \ (phase.drain (raw side)).excluded).Nonempty := by
      intro side
      refine ⟨who, Finset.mem_sdiff.mpr ⟨owned, ?_⟩⟩
      cases side
      · change who ∉ (phase.drain leftRaw).excluded
        rwa [leftExcluded]
      · change who ∉ (phase.drain rightRaw).excluded
        rwa [rightExcluded]
    have inherited : ∀ side, execution.application.current.excluded ⊆
        (ending side).execution.application.current.excluded := by
      intro side owner member
      let invariant : (app).Invariant (fun state => owner ∈ state.current.excluded) :=
        { submit := fun state player material present =>
            (phaseApplication_exclusion_monotone runtime leaks).submit state player material present
          handle := fun state message next present accepted =>
            (phaseApplication_exclusion_monotone runtime leaks).handle state message next
              accepted present
          environment := fun state command next present supported =>
            (phaseApplication_exclusion_monotone runtime leaks).environment state command next
              supported present }
      have atBefore := invariant.tracePrefix menu initial horizon scheduler anchor (before side)
        trace (priors side) (kept side) member
      cases side
      · exact (phaseApplication_exclusion_monotone runtime leaks).transition
          initial horizon scheduler leftBefore leftEnding leftJoint leftRealized atBefore
      · exact (phaseApplication_exclusion_monotone runtime leaks).transition
          initial horizon scheduler rightBefore rightEnding rightJoint rightRealized atBefore
    have equalLaw := phaseProposal_original_reset_payoff_law_eq setup mode runtime leaks bounds
      plan complete covered maximal values fullValues tape activationGap processingGap gaps timely
        capacity utility excludedPayoff anchor trace witness archived proper phase rest installed
          kind
          before ending priors traces kept same idle changed
            raw effects normalized finished missed survivors inherited archiveEq (resetSources
              reset) who
    have finishLaw (side) :
        (((menu).information initial horizon scheduler).runBehavioralTerminalFrom certificate
          (fun owner => (menu).restrictPolicy initial horizon scheduler owner
            (ReactiveApplication.anchoredPolicy (ending side).execution players owner))
          ⟨some (ending side), traces side⟩).map (fun final => payoff final.state) =
        ((app).finish initial horizon scheduler players (some (ending side))).map payoff := by
      have law := (menu).terminal_run_eq_finish initial horizon scheduler certificate
        (fun owner => (menu).restrictPolicy initial horizon scheduler owner
          (ReactiveApplication.anchoredPolicy (ending side).execution players owner))
        ⟨some (ending side), traces side⟩
      have decoded : (menu).decodeProfile initial horizon scheduler
          (fun owner => (menu).restrictPolicy initial horizon scheduler owner
            (ReactiveApplication.anchoredPolicy (ending side).execution players owner)) =
          ReactiveApplication.anchoredPolicy (ending side).execution players := by
        funext owner
        apply (menu).decode_restrictPolicy_of_covered initial horizon scheduler owner
        exact (menu).anchoredPolicy_covered initial horizon scheduler (ending side) (traces side)
          players owner (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds
            plan values owner)
      rw [decoded] at law
      have finish := congrArg (PMF.map payoff) law
      simpa only [ReactiveApplication.finish, idle side, ReactiveApplication.resume,
        PMF.pure_bind, PMF.bind_bind,
        ReactiveApplication.runRounds_anchoredPolicy, PMF.map_comp, Function.comp_def] using finish
    have exactLaw := (finishLaw false).symm.trans (equalLaw.trans (finishLaw true))
    have expectation := congrArg (fun law => expect law id) exactLaw
    have equality : finishValue leftFinal.state = finishValue rightFinal.state := by
      simpa only [finishValue, leftState, rightState, ending, Bool.false_eq_true, ite_false,
        ite_true,
        expect_map, Function.comp_def, id_eq] using expectation
    simpa only [reward, leftState, rightState, clean, cleanEq, and_false, ite_false] using
      equality.symm.le


section CleanBindingComparison

attribute [local implicit_reducible] ReservedConcurrentImplementation.initial
  ReservedConcurrentImplementation.scheduler PhaseCount.onePacketMenu
  EventGraph.withMode Setup.eventGraph toEventGraph InformationModel.InformationSite
  ReactiveApplication.ResponseMenu.protocol

variable (implementation : ReservedConcurrentImplementation setup)
  (payoffs : ConcurrentPayoffs setup)

local notation "cmenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "cN" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
    implementation.initial implementation.horizon implementation.scheduler
local notation "cE" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
    implementation.initial implementation.horizon implementation.scheduler
local notation "cS" => setup.proposalRecoveryModel
local notation "cHn" => 2 * implementation.horizon + 1
local notation "cHs" => (Fintype.card Player + 1) * (instructionCount setup.program + 1)

omit mode runtime leaks bounds plan in
open Classical in
theorem phaseProposal_clean_binding_gain_le
    [Fintype (cE).History] [Fintype setup.proposalRecoveryProtocol.History]
    (operational : implementation.Operational) (bounded : payoffs.Bounded)
    (qualified : PhaseProposalQualifiedBinding.QualifiedBindingLaw setup implementation)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (source : (cS).BehavioralAssessment)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      source.strategy owner ((cS).infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            ((cS).infoOf owner history.trace))
    (sourceMixed : source.IsFullyMixed)
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent cS source
      setup.proposalRecoveryModel_decisionAntichain)
    (native : (cN).BehavioralAssessment)
    (nativePrescribed : native.strategy = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      implementation.initial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (nativeMixed : native.IsFullyMixed)
    (nativeBayes : InformationModel.BehavioralAssessment.IsBayesConsistent cN native
      ((cmenu).decisionInformationAntichain implementation.initial implementation.horizon
        implementation.scheduler))
    (who : Player) (site : (cN).InformationSite who)
    (past : List implementation.application.PlayerEntry)
    (view : implementation.application.PlayerView)
    (information : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (unsent : ∀ message ∈ implementation.application.outputs past,
      PhaseCount.event? message.payload ≠ some ⟨view.application.2.attempt, event⟩)
    (noSaved : ¬ phaseProposalSavedBindingFailure setup .concurrent
      implementation.runtime implementation.leaks who event view)
    (noCurrent : ¬ phaseProposalCurrentBindingFailure setup .concurrent
      implementation.runtime implementation.leaks who event view)
    (noForcedReset : ¬ (view.application.2.excluded \
      ((view.application.2.retired.map fun record =>
          record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
        view.application.2.native.sourceFailureFootprint.1
          view.application.2.attempt.phase)).Nonempty)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |payoffs.utility terminal owner| ≤ bound)
    (excludedBound : ∀ owner, |payoffs.excludedPayoff owner| ≤ bound)
    (law : PMF ((cN).Choice who site.1)) :
    let nativePast := ∑ history : (cN).InformationHistory who site.1 with
      (∃ owner : Player, who ≠ owner ∧
        PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds implementation.initial
          implementation.horizon implementation.scheduler owner history.val),
      (native.belief who site history).toReal
    let nativeError := 2 * bound * (nativePast +
      (2 * (Fintype.card Player * cHn : Nat) + 1) *
        (⟨nativeBad, scale, scale, scale⟩ : PhaseProposalRates).flagBound)
    (cN).localGain cHn (fun history => history.state) (implementation.base payoffs)
        native site law ≤ nativeError ∨
      ∃ (sourceSite : (cS).InformationSite who)
        (sourceLaw : PMF ((cS).Choice who sourceSite.1)),
        0 < (cS).informationMass source.strategy who sourceSite ∧
        let sourcePast := ∑ history : (cS).InformationHistory who sourceSite.1 with
          (∃ owner : Player, who ≠ owner ∧
            setup.GeneratedPreparationHistory owner history.val),
          (source.belief who sourceSite history).toReal
        (cN).localGain cHn (fun history => history.state) (implementation.base payoffs)
            native site law ≤
          (cS).localGain cHs id
            (fun history owner => setup.proposalRecoveryPayoff payoffs.utility
              payoffs.excludedPayoff owner history) source sourceSite sourceLaw +
          nativeError + 4 * bound * (sourcePast +
            (Fintype.card Player * cHs : Nat) * (2 * scale.val + sourceBad.val))
 := by
  classical
  intro nativePast nativeError
  let _ : setup.FiniteInitialLaw := operational.finiteInitial
  let _ : implementation.leaks.FiniteSupport := by
    rw [operational.completePending]
    infer_instance
  let players := phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan values
  let ordinary := fun owner => (cmenu).restrictPolicy implementation.initial implementation.horizon
    implementation.scheduler owner (players owner)
  let baseline := ordinary who site.1
  let proper := fun (value : L.Val payload) (choice : (cN).Choice who site.1) =>
    ∃ (serial : Nat) (material : WitnessedSubmission (serviceGraph setup .concurrent)),
      choice.1 = some ⟨some material⟩ ∧
      material.call.packet = .commitment event (who, .prepared serial) ∧
      PhaseProposal.bindingPreparation material = some ⟨payload, value⟩
  let preparation := fun choice : (cN).Choice who site.1 =>
    choice.1.bind fun response => response.transmission.bind PhaseProposal.bindingPreparation
  let payoffAt := PhaseProposalQualifiedBinding.qualifiedPayoff setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      implementation.prior values
  let qualifiedValue := fun choice =>
    expect (payoffAt native who site choice payoffs.utility payoffs.excludedPayoff)
      (fun result => result.getD 0)
  let gain := fun choice : (cN).Choice who site.1 =>
    (cN).localGain cHn (fun history => history.state) (implementation.base payoffs)
      native site (PMF.pure choice)
  let _ := (cN).finite_choice_of_played ((cN).site_mem_playedInformation site)
  have nativeAffine : (cN).localGain cHn (fun history => history.state)
      (implementation.base payoffs) native site law = expect law gain := by
    simpa only [PMF.bind_pure] using (cN).localGain_bind cHn (fun history => history.state)
      (implementation.base payoffs) native site
      ((cmenu).bounded implementation.initial implementation.horizon implementation.scheduler)
      ((cmenu).decisionRecall implementation.initial implementation.horizon
        implementation.scheduler).actsOnceWhereItMatters law (fun choice => PMF.pure choice)
  suffices core :
      (∀ choice, (∃ value, proper value choice) → gain choice ≤ qualifiedValue choice -
        expect baseline qualifiedValue + nativeError) ∧
      (∀ choice, (¬ ∃ value, proper value choice) → gain choice ≤ nativeError) ∧
      (∀ choice ∈ baseline.support, ∃ value, proper value choice) ∧
      (∀ key, phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
        implementation.plan who event past view = some key →
        baseline.map preparation = (values who key).map (fun sampled => some
          (⟨payload, phaseRecoveryDomainValue setup .concurrent event who payload binding
            sampled.val.val⟩ : Raw L))) by
    have transport := qualified
    obtain zero | ⟨sourceSite, retained, encode, positive, queryEq, faithful, ordinaryEq, image⟩ :=
      transport operational scale sourceBad nativeBad scalePositive scaleBelow sourceBadPositive
        sourceBadBelow nativeBadPositive nativeBadBelow values fullValues source native sourceMixed
          sourceBayes sourcePrescribed nativeMixed nativeBayes nativePrescribed who site past view
            information event payload binding requested unsent noSaved noCurrent noForcedReset
    · left
      have qualifiedZero (choice) (typed : ∃ value, proper value choice) :
          qualifiedValue choice = 0 := by
        obtain ⟨value, typed⟩ := typed
        have exactLaw := (zero value choice typed).2 payoffs.utility payoffs.excludedPayoff
        change expect (payoffAt native who site choice payoffs.utility payoffs.excludedPayoff)
          (fun result => result.getD 0) = 0
        dsimp only [payoffAt]
        rw [exactLaw, expect_pure]
        rfl
      have baselineZero : expect baseline qualifiedValue = 0 := by
        rw [expect_congr_on_support (g := fun _ => 0)
          (fun choice member => qualifiedZero choice (core.2.2.1 choice member)), expect_constant]
      rw [nativeAffine]
      apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
      intro choice _
      by_cases typed : ∃ value, proper value choice
      · simpa only [qualifiedZero choice typed, baselineZero, sub_self, zero_add] using
          core.1 choice typed
      · exact core.2.1 choice typed
    · right
      obtain ⟨defaultChoice, supportedDefault⟩ := baseline.support_nonempty
      obtain ⟨defaultValue, _typedDefault⟩ := core.2.2.1 defaultChoice supportedDefault
      let selected := fun choice : (cN).Choice who site.1 =>
        if typed : ∃ value, proper value choice then typed.choose else defaultValue
      have selectedProper (choice) (typed : ∃ value, proper value choice) :
          proper (selected choice) choice := by
        dsimp only [selected]
        rw [dite_eq_left typed]
        exact typed.choose_spec
      have preparationOf (choice) (value) (typed : proper value choice) :
          preparation choice = some (⟨payload, value⟩ : Raw L) := by
        obtain ⟨serial, material, chosen, _packet, prepared⟩ := typed
        simp only [preparation, chosen, Option.bind_some, prepared]
      have sampled : baseline.map selected = (values who
          (setup.proposalRecoveryQuery who sourceSite.1)).map (fun sampled =>
            phaseRecoveryDomainValue setup .concurrent event who payload binding sampled.val.val)
              := by
        apply pmf_map_injective (f := fun value => some (⟨payload, value⟩ : Raw L))
        · intro first second same
          have decoded := congrArg (fun raw : Option (Raw L) => raw.bind fun value => value.as?
            payload) same
          exact Option.some.inj (by
            simpa only [Option.bind_some, Raw.as?_mk] using decoded)
        · rw [PMF.map_comp, PMF.map_comp]
          exact (map_congr_on_support baseline (fun choice member =>
            (preparationOf choice (selected choice)
              (selectedProper choice (core.2.2.1 choice member))).symm)).trans
                (core.2.2.2 _ queryEq)
      let causal := fun choice => PhaseProposalQualifiedBinding.sourceCausalPayoff setup values
        source who sourceSite choice positive payoffs.utility payoffs.excludedPayoff
      let mean := fun choice => expect (causal choice) (fun result => result.getD 0)
      have payoffBound (history) :
          |setup.proposalRecoveryPayoff payoffs.utility payoffs.excludedPayoff who history| ≤
            bound := by
        have limited := setup.proposalRecoveryPayoff_mem_Icc payoffs.utility payoffs.excludedPayoff
          (fun _ => -bound) (fun _ => bound) (fun terminal owner => abs_le.mp (utilityBound
            terminal owner))
          who history
        have excluded := abs_le.mp (excludedBound who)
        apply abs_le.mpr
        simpa only [min_eq_right excluded.1, min_eq_right (neg_nonpos.mpr nonnegative),
          max_eq_right excluded.2, max_eq_right nonnegative, Set.mem_Icc] using limited
      have causalIntegrable (choice) : PayoffIntegrable (causal choice) (fun result =>
        result.getD 0) := by
        apply payoffIntegrable_of_bounded_on_support (C := bound)
        intro result member
        change (result ∈ (((source.belief who sourceSite).filter _ positive).bind _).support)
          at member
        obtain ⟨history, _drawn, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
        obtain ⟨terminal, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        exact payoffBound terminal
      have qualifiedMean (choice) (typed : ∃ value, proper value choice) :
          qualifiedValue choice = retained.val * mean (encode (selected choice)) := by
        have exactLaw := (image (selected choice) choice (selectedProper choice typed)).2
          payoffs.utility payoffs.excludedPayoff
        change expect (payoffAt native who site choice payoffs.utility payoffs.excludedPayoff)
          (fun result => result.getD 0) = _
        dsimp only [payoffAt]
        rw [exactLaw, expect_mix _ _ _ _ _ _ (causalIntegrable _) (payoffIntegrable_pure _ _),
          expect_pure]
        simp only [Option.getD_none, mul_zero, add_zero]
        rfl
      have baselineMean : expect baseline qualifiedValue = retained.val *
          expect ((PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values) who
            sourceSite.1) mean := by
        have encoded : (baseline.map selected).map encode =
            PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values who
              sourceSite.1 := by
          rw [sampled, PMF.map_comp]
          exact ordinaryEq.symm
        have averaged := congrArg (fun lottery => expect lottery mean) encoded
        rw [expect_map, expect_map] at averaged
        change expect baseline (fun choice => mean (encode (selected choice))) =
          expect (PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values who
            sourceSite.1) mean at averaged
        rw [expect_congr_on_support (g := fun choice => retained.val * mean (encode (selected
          choice)))
          (fun choice member => qualifiedMean choice (core.2.2.1 choice member)), expect_const_mul,
          averaged]
      let sourcePast := ∑ history : (cS).InformationHistory who sourceSite.1 with
        (∃ owner : Player, who ≠ owner ∧ setup.GeneratedPreparationHistory owner history.val),
        (source.belief who sourceSite history).toReal
      let sourceError := 4 * bound * (sourcePast +
        (Fintype.card Player * cHs : Nat) * (2 * scale.val + sourceBad.val))
      have sourceErrorNonnegative : 0 ≤ sourceError := by
        dsimp only [sourceError, sourcePast]
        positivity
      let component := fun choice => if typed : ∃ value, proper value choice then
        mix retained.val retained.property.1.le retained.property.2
          (PMF.pure (encode (selected choice))) (source.strategy who sourceSite.1)
        else source.strategy who sourceSite.1
      have atomBound (choice) : gain choice ≤
          (cS).localGain cHs id (fun history owner =>
            setup.proposalRecoveryPayoff payoffs.utility payoffs.excludedPayoff owner history)
              source sourceSite (component choice) + nativeError + sourceError := by
        by_cases typed : ∃ value, proper value choice
        · have first := core.1 choice typed
          rw [qualifiedMean choice typed, baselineMean] at first
          have close := source_causal_gain_le setup scale sourceBad values source sourcePrescribed
            who sourceSite positive (encode (selected choice)) payoffs.utility
              payoffs.excludedPayoff
              bound nonnegative payoffBound
          have signed := (cS).localValue_mix cHs id
            (fun history owner => setup.proposalRecoveryPayoff payoffs.utility
              payoffs.excludedPayoff owner history)
            source sourceSite setup.proposalRecoveryProtocol_bounded
              ((cS).actsOnceWhereItMatters_of_perfectRecall
                setup.proposalRecoveryModel_perfectRecall)
              retained.val retained.property.1.le retained.property.2
                (PMF.pure (encode (selected choice))) (source.strategy who sourceSite.1)
          let _ := (cS).finite_choice_of_played ((cS).site_mem_playedInformation sourceSite)
          have integrable := payoffIntegrable_bind_of_finite_support
            (PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values who sourceSite.1)
            causal (fun result => result.getD 0) (Set.toFinite _)
            (fun choice _ => causalIntegrable choice)
          have baselineCausal := expect_bind_tower _ _ _ integrable
          change expect ((PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values who
            sourceSite.1).bind causal) (fun result => result.getD 0) =
              expect (PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values who
                sourceSite.1) mean at baselineCausal
          change mean (encode (selected choice)) -
              expect ((PhaseProposalQualifiedBinding.sourceUnflaggedStrategy setup values who
                sourceSite.1).bind causal) (fun result => result.getD 0) ≤
            (cS).localGain cHs id (fun history owner => setup.proposalRecoveryPayoff
              payoffs.utility payoffs.excludedPayoff owner history) source sourceSite
                (PMF.pure (encode (selected choice))) + sourceError at close
          rw [baselineCausal, InformationModel.localGain_eq_sub] at close
          simp only [component, dite_eq_left typed, InformationModel.localGain_eq_sub] at signed ⊢
          nlinarith [mul_le_mul_of_nonneg_left close retained.property.1.le,
            mul_le_of_le_one_left sourceErrorNonnegative retained.property.2]
        · simp only [component, dite_eq_right typed, InformationModel.localGain_self]
          exact (core.2.1 choice typed).trans (by linarith)
      refine ⟨sourceSite, law.bind component,
        (cS).informationMass_pos_of_fullSupport source.strategy sourceMixed who sourceSite, ?_⟩
      rw [nativeAffine, (cS).localGain_bind cHs id
        (fun history owner => setup.proposalRecoveryPayoff payoffs.utility payoffs.excludedPayoff
          owner history)
        source sourceSite setup.proposalRecoveryProtocol_bounded
          ((cS).actsOnceWhereItMatters_of_perfectRecall setup.proposalRecoveryModel_perfectRecall)]
      calc
        _ ≤ expect law (fun choice => (cS).localGain cHs id
            (fun history owner => setup.proposalRecoveryPayoff payoffs.utility
              payoffs.excludedPayoff owner history)
            source sourceSite (component choice) + nativeError + sourceError) :=
          expect_mono (fun choice _ => atomBound choice) (payoffIntegrable_of_finite _ _)
            (payoffIntegrable_of_finite _ _)
        _ = _ := by
          rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _),
            expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _),
            expect_constant, expect_constant]
  let outcome := fun state => implementation.base payoffs state who
  let certificate := ((cmenu).bounded implementation.initial implementation.horizon
    implementation.scheduler).wellFoundedHistories
  let responseOf : (cN).Choice who site.1 → implementation.application.Action :=
    fun choice => choice.1.getD ⟨none⟩
  let bad := fun history : (cN).InformationHistory who site.1 =>
    ∃ owner : Player, who ≠ owner ∧ PhaseProposal.GeneratedUnusableBindingHistory
      implementation.runtime implementation.leaks implementation.bounds implementation.initial
        implementation.horizon implementation.scheduler owner history.val
  have outcomeBound (state) : |outcome state| ≤ bound := by
    change |phaseExclusionBase setup .concurrent implementation.runtime implementation.leaks
      payoffs.utility payoffs.excludedPayoff state who| ≤ bound
    have interval := phaseExclusionBase_mem_Icc setup .concurrent implementation.runtime
      implementation.leaks payoffs.utility payoffs.excludedPayoff (fun _ => -bound)
        (fun _ => bound) (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).1)
          (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).2) state who
    have excluded := abs_le.mp (excludedBound who)
    apply abs_le.mpr
    simpa only [min_eq_right excluded.1, min_eq_right (neg_nonpos.mpr nonnegative),
      max_eq_right excluded.2, max_eq_right nonnegative, Set.mem_Icc] using interval
  have callback (history : (cN).InformationHistory who site.1) :
      ∃ control : implementation.application.Control, history.val.state = some control ∧
        control.actor = some who ∧ control.execution.recall who = past ∧
          control.execution.observe implementation.application who = view := by
    have observed := ((cmenu).info implementation.initial implementation.horizon
      implementation.scheduler who history.val.trace).symm.trans
        (history.property.trans information)
    cases current : history.val.state with
    | none => rw [current] at observed; cases observed
    | some control =>
        rw [current] at observed
        change (if control.actor = some who then some (control.execution.recall who,
          control.execution.observe implementation.application who) else none) =
            some (past, view) at observed
        split at observed
        · rename_i active
          exact ⟨control, rfl, active, (Prod.mk.inj (Option.some.inj observed)).1,
            (Prod.mk.inj (Option.some.inj observed)).2⟩
        · cases observed
  have offered (choice : (cN).Choice who site.1) :
      choice.1 = some (responseOf choice) ∧
        responseOf choice ∈ (cmenu).actions who past view := by
    have permitted := choice.property
    simp only [information] at permitted
    obtain ⟨response, member, selected⟩ := permitted
    constructor
    · simp only [responseOf, selected, Option.getD_some]
    · simpa only [responseOf, selected, Option.getD_some] using member
  have rawBaseline : baseline.map responseOf = players who past view := by
    have projection := congrArg (PMF.map fun response => response.getD ⟨none⟩)
      ((cmenu).restrictPolicy_map_val implementation.initial implementation.horizon
        implementation.scheduler who (players who) past view
          (phaseProposalUnflaggedPolicy_covered setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan values who past view))
    have atInformation := congrArg (fun input =>
      ((ordinary who input).map fun choice => choice.1.getD ⟨none⟩)) information
    change baseline.map responseOf = _ at atInformation
    refine atInformation.trans ?_
    simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at projection
    change _ = (players who past view).map id at projection
    rw [PMF.map_id] at projection
    exact projection
  obtain ⟨representative, _positiveRepresentative⟩ := (native.belief who site).support_nonempty
  obtain ⟨origin, originState, originActor, originPast, originView⟩ := callback representative
  have originTrace : (cE).Trace (some ⟨origin.remaining, some who, origin.execution⟩) := by
    simpa only [← originActor] using (originState ▸ representative.val.trace)
  have publicRequest (control : implementation.application.Control)
      (trace : (cE).Trace (some ⟨control.remaining, some who, control.execution⟩))
      (observed : control.execution.observe implementation.application who = view) :
      control.execution.application.SeedRequest who
        ⟨control.execution.application.attempt, event⟩ := by
    have invariant := phaseNativeInvariant_history implementation.runtime
      implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler
        (control := ⟨control.remaining, some who, control.execution⟩)
    rw [PMF.map_comp] at invariant
    obtain ⟨_draw, valid⟩ := invariant ((cmenu).toRawTrace implementation.initial
      implementation.horizon implementation.scheduler trace)
    apply (control.execution.application.requests_publicView valid who _).mp
    change PhaseRuntimeState.requests
      (control.execution.observe implementation.application who).application.2 who _
    have sameAttempt := congrArg
      (fun observation : implementation.application.PlayerView => observation.application.2.attempt)
      observed
    change control.execution.application.attempt = view.application.2.attempt at sameAttempt
    simpa only [observed, sameAttempt] using requested
  have originRequest := publicRequest origin originTrace originView
  have originAttempt : origin.execution.application.attempt = view.application.2.attempt := by
    exact congrArg (fun observed : implementation.application.PlayerView =>
      observed.application.2.attempt) originView
  have supportedProper (choice) (member : choice ∈ baseline.support) : ∃ value, proper value
    choice := by
    have emitted : responseOf choice ∈ (baseline.map responseOf).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨choice, member, rfl⟩
    rw [rawBaseline, ← originPast, ← originView] at emitted
    obtain ⟨material, value, transmitted, typed⟩ :=
      phaseProposalUnflaggedBinding_supported_usable setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan operational.completePending
          operational.outputValues operational.maximalPhases values fullValues
            implementation.horizon implementation.scheduler operational.candidateReserve
              origin.remaining who origin.execution originTrace event payload binding originRequest
                (by simpa only [originPast, originAttempt] using unsent) (responseOf choice) emitted
    have available := (offered choice).2
    rw [← originPast, ← originView] at available
    have shape := PhaseCount.onePacket_binding_shape implementation.runtime implementation.leaks
      implementation.bounds implementation.plan (serviceGraph_revealRelaxedOrdered setup
        .concurrent)
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
    rw [PMF.map_comp] at shape
    have responseEq : responseOf choice = ⟨some material⟩ :=
      congrArg (fun transmission =>
        ({ transmission := transmission } : implementation.application.Action)) transmitted
    have shaped := shape origin.remaining who origin.execution originTrace event payload binding
      originRequest material (by simpa only [responseEq, PhaseCount.onePacketMenu] using available)
    obtain ⟨serial, preparation, evidence, materialEq, _bounded, _fresh⟩ := shaped
    refine ⟨value, serial, material, ?_, ?_, typed⟩
    · rw [(offered choice).1]
      exact congrArg some responseEq
    · rw [materialEq]
  have preparationLaw (key) (queried : phaseProposalQuery? setup .concurrent
      implementation.runtime implementation.leaks implementation.plan who event past view = some
        key) :
      baseline.map preparation = (values who key).map (fun sampled => some
        (⟨payload, phaseRecoveryDomainValue setup .concurrent event who payload binding
          sampled.val.val⟩ : Raw L)) := by
    have projected := phaseProposalUnflaggedBinding_preparation_law_of_query setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        operational.outputValues values implementation.horizon implementation.scheduler
          operational.candidateReserve origin.remaining who origin.execution originTrace event
            payload binding originRequest (by simpa only [originPast, originAttempt] using unsent)
              key (by simpa only [originPast, originView] using queried)
    have mapped := congrArg
      (PMF.map fun response => response.transmission.bind PhaseProposal.bindingPreparation)
        rawBaseline
    have exactRead : baseline.map preparation = (baseline.map responseOf).map
        (fun response => response.transmission.bind PhaseProposal.bindingPreparation) := by
      rw [PMF.map_comp]
      apply congrArg (PMF.map · baseline)
      funext choice
      simp only [preparation, (offered choice).1, Option.bind_some, Function.comp_def]
    apply exactRead.trans
    apply mapped.trans
    rw [originPast, originView] at projected
    convert projected using 1
  let experiment := PhaseProposalQualifiedBinding.stoppedFinish setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      implementation.prior values
  let gateAt := PhaseProposalQualifiedBinding.originalAdmissionGate setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      implementation.prior
  let goodAt := PhaseProposalQualifiedBinding.foreignGood setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      implementation.prior
  let mean := fun (history : (cN).InformationHistory who site.1) choice =>
    expect (experiment who history.val (history.property.symm ▸ choice))
      (fun result => outcome result.2.state)
  let residual := fun (history : (cN).InformationHistory who site.1) choice (remove : Bool) =>
    expect (experiment who history.val (history.property.symm ▸ choice)) (fun result =>
      if remove = true ∧ gateAt history.val result.1 then 0 else outcome result.2.state)
  let retained := fun history choice => if bad history then 0 else
    mean history choice - residual history choice true
  have meanBound (history) (choice) : |mean history choice| ≤ bound :=
    expect_abs_le_of_bounded nonnegative (fun result => outcomeBound result.2.state)
  have residualBound (history) (choice) (remove) : |residual history choice remove| ≤ bound := by
    apply expect_abs_le_of_bounded nonnegative
    intro result
    split
    · simpa only [abs_zero] using nonnegative
    · exact outcomeBound _
  have qualifiedMean (choice) : qualifiedValue choice =
      expect (native.belief who site) (fun history => retained history choice) := by
    have integrable : PayoffIntegrable
        (payoffAt native who site choice payoffs.utility payoffs.excludedPayoff)
          (fun result : Option ℝ => result.getD 0) := by
      apply payoffIntegrable_of_bounded_on_support (C := bound)
      intro result member
      dsimp only [payoffAt, PhaseProposalQualifiedBinding.qualifiedPayoff] at member
      obtain ⟨history, _drawn, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      obtain ⟨pair, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      split <;> simp only [Option.getD_some, Option.getD_none, abs_zero]
      · exact outcomeBound _
      · exact nonnegative
    dsimp only [qualifiedValue, payoffAt, PhaseProposalQualifiedBinding.qualifiedPayoff]
    rw [expect_bind_tower _ _ _ integrable]
    apply expect_congr_on_support
    intro history _
    rw [expect_map]
    dsimp only [retained, mean, residual]
    change expect (experiment who history.val (history.property.symm ▸ choice))
      (fun result => (if goodAt who history.val ∧ gateAt history.val result.1
        then some (outcome result.2.state) else none).getD 0) = _
    have meanIntegrable := payoffIntegrable_of_bounded
      (experiment who history.val (history.property.symm ▸ choice))
      (fun result => outcome result.2.state) (fun result => outcomeBound result.2.state)
    have removedIntegrable := payoffIntegrable_of_bounded
      (experiment who history.val (history.property.symm ▸ choice))
      (fun result => if true = true ∧ gateAt history.val result.1 then 0
        else outcome result.2.state) (fun result => by
          split
          · simpa only [abs_zero] using nonnegative
          · exact outcomeBound result.2.state)
    rw [← expect_sub meanIntegrable removedIntegrable]
    by_cases foreignBad : bad history
    · have notGood : ¬ goodAt who history.val := by
        obtain ⟨owner, different, generated⟩ := foreignBad
        exact fun good => good owner different.symm generated
      simp only [foreignBad, ite_true, notGood, false_and, ite_false, Option.getD_none,
        expect_constant]
    · have good : goodAt who history.val := by
        intro owner different generated
        exact foreignBad ⟨owner, different.symm, generated⟩
      simp only [foreignBad, ite_false, good, true_and]
      apply expect_congr_on_support
      intro result _
      split_ifs <;> simp_all only [Option.getD_some, Option.getD_none] <;> ring
  have physicalResidual (history : (cN).InformationHistory who site.1)
      (control : implementation.application.Control) (current : history.val.state = some control)
      (active : control.actor = some who)
      (phase : RuntimePhase (serviceGraph setup .concurrent))
      (installed : phase ∈ control.execution.application.phases.head?)
      (kind : phase.kind = .commitment) (choice) (remove : Bool) :
      residual history choice remove =
        expect (((implementation.application).schedulerMixture implementation.prior
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime))).posterior
              control.execution.environmentRecall) (fun tape =>
          expect ((implementation.application).runUntil
            (ReservedEpoch.family implementation.runtime implementation.leaks
              (ReservedEpoch.packetCapacity implementation.runtime) tape) players
            (fun next => next.application.attempt ≠ control.execution.application.attempt)
              control.remaining (control.execution.respond implementation.application who
                (responseOf choice))) (fun ending =>
            if remove = true ∧ ending.application.attempt ≠ control.execution.application.attempt ∧
                ending.application.current.excluded = control.execution.application.entry.excluded
            then 0 else expect ((implementation.application).finish implementation.initial
              implementation.horizon (ReservedEpoch.family implementation.runtime
                implementation.leaks (ReservedEpoch.packetCapacity implementation.runtime) tape)
                  players (some ⟨implementation.horizon - ending.environmentRecall.length,
                    none, ending⟩)) outcome)) := by
    have joint := PhaseProposalQualifiedBinding.stoppedFinish_gate_seed_joint setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        implementation.prior values implementation.activationGap implementation.processingGap
          operational.boundedGaps operational.maximalPhases
    have exactJoint := joint who history.val (history.property.symm ▸ choice) control.remaining
      control.execution (by simpa only [← active] using current) (responseOf choice)
        (by
          have castVal : ∀ (first second : (cN).InfoState who) (same : first = second)
              (atom : (cN).Choice who first),
              ((same ▸ atom : (cN).Choice who second).val) = atom.val := by
            intro first second same atom
            cases same
            rfl
          exact (castVal _ _ history.property.symm choice).trans (offered choice).1)
        phase installed kind
    have read := congrArg (fun law => expect law (fun result =>
      if remove = true ∧ result.1.1 = true then 0 else outcome result.1.2)) exactJoint
    have rewardBound : ∀ result : (Bool × implementation.application.ProtocolState) ×
        ReservedEpoch.Tape Player implementation.tapeLength,
        |(if remove = true ∧ result.1.1 = true then 0 else outcome result.1.2 : ℝ)| ≤ bound := by
      intro result
      split
      · simpa only [abs_zero] using nonnegative
      · exact outcomeBound result.1.2
    simp only [expect_bind_tower_bounded _ _ _ rewardBound, expect_map,
      Function.comp_def, decide_eq_true_eq, expect_constant] at read
    dsimp only [residual, experiment, gateAt]
    rw [read]
    apply expect_congr_on_support
    intro tape _
    apply expect_congr_on_support
    intro ending _
    split_ifs <;> first | rfl | exact expect_constant _ _
  have physicalOrder (history : (cN).InformationHistory who site.1) (good : ¬ bad history)
      (choice) (remove : Bool)
      (typed : remove = true → ∃ value, proper value choice)
      (untyped : remove = false → ¬ ∃ value, proper value choice) :
      residual history choice remove ≤ expect baseline (fun left => residual history left remove)
        := by
    obtain ⟨control, current, active, recalled, observed⟩ := callback history
    have counted : (cE).Trace (some ⟨control.remaining, some who, control.execution⟩) := by
      simpa only [← active] using (current ▸ history.val.trace)
    have rawTrace := (cmenu).toRawTrace implementation.initial implementation.horizon
      implementation.scheduler counted
    have request := publicRequest control counted observed
    have phaseRead := phase_ready_binding_phase
      implementation.runtime implementation.leaks implementation.plan
        (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
          (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
          (control := ⟨control.remaining, some who, control.execution⟩)
    rw [PMF.map_comp] at phaseRead
    obtain ⟨phase, rest, installed, kind, _inside⟩ := phaseRead
      rawTrace who event payload binding request.2.2.1
    let family : ReservedEpoch.Tape Player implementation.tapeLength →
        implementation.application.Scheduler :=
      ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime)
    let valueAt := fun tape response => expect ((implementation.application).runUntil
      (family tape) players (fun next => next.application.attempt ≠
        control.execution.application.attempt)
        control.remaining (control.execution.respond implementation.application who response))
      (fun ending => if remove = true ∧
        ending.application.attempt ≠ control.execution.application.attempt ∧
          ending.application.current.excluded = control.execution.application.entry.excluded then 0
        else expect ((implementation.application).finish implementation.initial
          implementation.horizon
          (family tape) players (some ⟨implementation.horizon - ending.environmentRecall.length,
            none, ending⟩)) outcome)
    have valueBound (tape) (response) : |valueAt tape response| ≤ bound := by
      apply expect_abs_le_of_bounded nonnegative
      intro ending
      split
      · simpa only [abs_zero] using nonnegative
      · exact expect_abs_le_of_bounded nonnegative outcomeBound
    have phaseHead : phase ∈ control.execution.application.phases.head? := by
      change control.execution.application.phases = phase :: rest at installed
      rw [installed]
      exact Option.mem_some_iff.mpr rfl
    rw [physicalResidual history control current active phase phaseHead kind choice remove]
    have baselineResidual := expect_congr_on_support (μ := baseline) (fun left _ =>
      physicalResidual history control current active phase phaseHead kind left remove)
    refine le_of_le_of_eq ?_ baselineResidual.symm
    rw [expect_comm_of_support_finite_left baseline _ (Set.toFinite _)
      (fun left tape => valueAt tape (responseOf left))
      (fun left _ => payoffIntegrable_of_bounded _ _
        (fun tape => valueBound tape (responseOf left)))]
    change expect _ (fun tape => valueAt tape (responseOf choice)) ≤
      expect _ (fun tape => expect baseline (fun left => valueAt tape (responseOf left)))
    apply expect_mono _
      (payoffIntegrable_of_bounded _ _ (fun tape => valueBound tape (responseOf choice)))
      (payoffIntegrable_of_bounded _ _ (fun tape =>
        expect_abs_le_of_bounded nonnegative (fun left => valueBound tape (responseOf left))))
    intro tape tapeSupported
    have finiteInitial : implementation.initial.support.Finite := by
      simpa only [ReservedConcurrentImplementation.initial, PMF.support_map] using
        setup.initialLaw_support_finite.image
          (fun theta => PhaseRuntimeState.initial implementation.plan (encodeInputs theta))
    let fixedNature : implementation.application.FiniteNature implementation.initial
        (family tape) :=
      phaseApplication_finiteNature implementation.runtime implementation.leaks
        implementation.initial (family tape) finiteInitial (by
          intro earlier seen
          simp only [family, ReservedEpoch.family, PMF.support_pure]
          exact Set.finite_singleton _)
    let _ : implementation.application.FiniteNature
        ((setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan))
        (family tape) := by
      rw [PMF.map_comp]
      exact fixedNature
    let fixedValue := valueAt tape
    change fixedValue (responseOf choice) ≤ expect baseline (fun left => fixedValue (responseOf
      left))
    obtain ⟨tapeInPrior, ⟨fixedRawTrace⟩⟩ :=
      (implementation.application).schedulerMixture_trace_of_posterior_support implementation.prior
        family implementation.initial implementation.horizon
          ⟨control.remaining, some who, control.execution⟩ rawTrace tape tapeSupported
    obtain ⟨fixedTrace⟩ := (cmenu).trace_of_recorded_actions
      (PhaseCount.silence_onePacket implementation.runtime implementation.leaks
        implementation.bounds)
        implementation.initial implementation.horizon (family tape) _ fixedRawTrace (by
          intro owner earlier entry later recorded
          obtain ⟨before, _prior, _kept, _acting, _past, viewed, permitted⟩ :=
            (cmenu).recorded_response_at implementation.initial implementation.horizon
              implementation.scheduler _ counted owner earlier entry later recorded
          rwa [← viewed] at permitted)
    have fixedCounted : ((cmenu).protocol
        ((setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon (family tape)).Trace
          (some ⟨control.remaining, some who, control.execution⟩) := by
      rw [PMF.map_comp]
      exact fixedTrace
    have foreign (owner : Player) (different : owner ≠ who)
        (_surviving : owner ∉ control.execution.application.current.excluded)
        (generated : PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds
            ((setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan))
            implementation.horizon (family tape) owner
              ⟨some ⟨control.remaining, some who, control.execution⟩, fixedCounted⟩) : False := by
      apply good
      refine ⟨owner, different.symm, ?_⟩
      change ∃ record ∈ ((cmenu).signals implementation.initial implementation.horizon
        implementation.scheduler).ownPlay owner history.val.trace, _
      change ∃ record ∈ ((cmenu).signals
        ((setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon (family tape)).ownPlay owner fixedCounted, _ at generated
      rw [← (cmenu).ownPlay_toRawTrace _ implementation.horizon
        (family tape) owner fixedCounted, (implementation.application).trace_ownPlay] at generated
      rw [← (cmenu).ownPlay_toRawTrace implementation.initial implementation.horizon
        implementation.scheduler owner history.val.trace,
          (implementation.application).trace_ownPlay]
      simp only [ReactiveApplication.recallAt, current] at generated ⊢
      change ∃ record ∈ implementation.application.recallOwnPlay
        (control.execution.recall owner),
        PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
          owner record.2 at generated ⊢
      exact generated
    have currentAttempt : control.execution.application.attempt = view.application.2.attempt :=
      congrArg (fun observation : implementation.application.PlayerView =>
        observation.application.2.attempt) observed
    have unsentHere : ∀ message ∈ implementation.application.outputs
        (control.execution.recall who), PhaseCount.event? message.payload ≠
          some ⟨control.execution.application.attempt, event⟩ := by
      simpa only [recalled, currentAttempt] using unsent
    have available : responseOf choice ∈ (cmenu).actions who (control.execution.recall who)
        (control.execution.observe implementation.application who) := by
      simpa only [recalled, observed] using (offered choice).2
    have stopFinish (response : implementation.application.Action) :
        (implementation.application).finish implementation.initial implementation.horizon
          (family tape) players (some ⟨control.remaining, none,
            control.execution.respond implementation.application who response⟩) =
        ((implementation.application).runUntil (family tape) players
          (fun next => next.application.attempt ≠ control.execution.application.attempt)
            control.remaining (control.execution.respond implementation.application who
              response)).bind
          (fun ending => (implementation.application).finish implementation.initial
            implementation.horizon (family tape) players
              (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)) := by
      have accounted := implementation.application.raw_trace_horizon implementation.initial
        implementation.horizon (family tape) fixedRawTrace
      change control.execution.environmentRecall.length + control.remaining =
        implementation.horizon at accounted
      have responseRecall := implementation.application.respond_environmentRecall
        control.execution who response
      rw [implementation.application.finish_eq_runToHorizon _ _ _ _ _ _
        (by simpa only [responseRecall] using accounted)]
      rw [implementation.application.runToHorizon_eq_runUntilHorizon_bind _ _
        (fun next => next.application.attempt ≠ control.execution.application.attempt)]
      simp only [ReactiveApplication.runUntilHorizon, responseRecall,
        show implementation.horizon - control.execution.environmentRecall.length =
          control.remaining by omega, PMF.map_bind]
      apply bind_congr_on_support
      intro ending _
      simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind,
        ReactiveApplication.runToHorizon]
    cases transmitted : (responseOf choice).transmission with
    | none =>
        have notRemove : remove = false := by
          cases remove with
          | false => rfl
          | true =>
              obtain ⟨value, serial, material, selected, _packet, _prepared⟩ := typed rfl
              have impossible := congrArg (fun action => action.bind
                (fun response => response.transmission)) selected
              simp only [(offered choice).1, Option.bind_some, transmitted] at impossible
              cases impossible
        have waiting := phaseProposal_unflagged_wait_finish_le setup .concurrent
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
            operational.completePending operational.outputValues operational.maximalPhases
              operational.wellFormed values fullValues tape implementation.activationGap
                implementation.processingGap (operational.boundedGaps tape tapeInPrior)
                  operational.timely operational.candidateReserve control.remaining who
                    control.execution fixedCounted event payload binding request unsentHere
                      (by simpa only [observed] using noSaved)
                      (by simpa only [observed] using noCurrent)
        obtain ⟨witness, _archive⟩ := recoverySourceCheckpoint_proposalArchive_history setup
          .concurrent implementation.runtime implementation.leaks implementation.bounds
            implementation.plan operational.maximalPhases implementation.horizon (family tape)
              fixedTrace
        have savedE : control.execution.application.entry.excluded =
            PhaseRuntimeState.archivedFailureOwners control.execution.application.retired ∪
              control.execution.application.current.native.failureOwnersBefore
                control.execution.application.attempt.phase :=
          PhaseRuntimeState.saved_excluded_eq_public_failures witness.exclusions
            witness.failures witness.receipts.exclusion.frontier phase rest installed
        have equalE : control.execution.application.current.excluded =
            control.execution.application.entry.excluded := by
          apply Finset.Subset.antisymm
          · intro owner member
            by_contra absent
            apply noForcedReset
            rw [← observed]
            change (control.execution.application.publicView.excluded \
              ((control.execution.application.publicView.retired.map fun record =>
                record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
                control.execution.application.publicView.native.sourceFailureFootprint.1
                  control.execution.application.publicView.attempt.phase)).Nonempty
            simpa only [PhaseRuntimeState.publicView, State.sourceFailureFootprint_read,
              PhaseRuntimeState.sourceRecordFailures_sourceControlRecords,
              PhaseRuntimeState.archivedFailureOwners, List.map_map, Function.comp_def,
              State.sourceFailureFootprint, List.foldr_map, savedE] using
                (show (control.execution.application.current.excluded \
                  control.execution.application.entry.excluded).Nonempty from
                    ⟨owner, Finset.mem_sdiff.mpr ⟨member, absent⟩⟩)
          · exact witness.exclusions.coverage.inherited
        have comparison := waiting equalE foreign payoffs.utility payoffs.excludedPayoff bound
          nonnegative utilityBound (excludedBound who) (bounded.excluded_nonpositive who)
            (fun terminal => bounded.excluded_le terminal who)
        have waitingEq : responseOf choice = ⟨none⟩ :=
          congrArg (fun transmission =>
            ({ transmission := transmission } : implementation.application.Action)) transmitted
        have fullBaseline : (implementation.application).finish implementation.initial
            implementation.horizon (family tape) players
              (some ⟨control.remaining, some who, control.execution⟩) =
            (baseline.map responseOf).bind fun response =>
              (implementation.application).finish implementation.initial implementation.horizon
                (family tape) players (some ⟨control.remaining, none,
                  control.execution.respond implementation.application who response⟩) := by
          rw [rawBaseline, ← recalled, ← observed]
          simp only [ReactiveApplication.finish, ReactiveApplication.resume,
            ReactiveApplication.invoke, PMF.bind_map, PMF.pure_bind, PMF.map_bind,
            Function.comp_def]
        dsimp only at comparison
        rw [PMF.map_comp] at comparison
        change expect (implementation.application.finish implementation.initial
          implementation.horizon
          (family tape) players (some ⟨control.remaining, none,
            control.execution.respond implementation.application who ⟨none⟩⟩)) outcome ≤
          expect (implementation.application.finish implementation.initial implementation.horizon
            (family tape) players (some ⟨control.remaining, some who, control.execution⟩)) outcome
          at comparison
        rw [fullBaseline, expect_bind_tower_bounded _ _ _ outcomeBound, expect_map] at comparison
        have fixedFinish (response) : fixedValue response =
            expect (implementation.application.finish implementation.initial implementation.horizon
              (family tape) players (some ⟨control.remaining, none,
                control.execution.respond implementation.application who response⟩)) outcome := by
          dsimp only [fixedValue, valueAt]
          simp only [notRemove, Bool.false_eq_true, false_and, ite_false]
          rw [← expect_bind_tower_bounded _ _ _ outcomeBound, ← stopFinish]
        have baselineFinish := expect_congr_on_support (μ := baseline)
          (fun left _ => fixedFinish (responseOf left))
        rw [fixedFinish, baselineFinish]
        simpa only [waitingEq, Function.comp_def] using comparison
    | some material =>
        have responseEq : responseOf choice = ⟨some material⟩ :=
          congrArg (fun transmission =>
            ({ transmission := transmission } : implementation.application.Action)) transmitted
        have ordered : ∀ left ∈ baseline.support,
            fixedValue (responseOf choice) ≤ fixedValue (responseOf left) := by
          intro left leftSupported
          have supported : responseOf left ∈ (baseline.map responseOf).support :=
            (PMF.mem_support_map_iff _ _ _).mpr ⟨left, leftSupported, rfl⟩
          rw [rawBaseline, ← recalled, ← observed] at supported
          have badPreparation : remove = false →
              (responseOf choice).transmission.bind PhaseProposal.bindingPreparation = none := by
            intro isFalse
            cases prepared : PhaseProposal.bindingPreparation material with
            | none => simp only [transmitted, prepared, Option.bind_some]
            | some raw =>
                obtain ⟨serial, opening, evidence, materialEq, _bound, _fresh⟩ :=
                  PhaseCount.onePacket_binding_shape implementation.runtime implementation.leaks
                    implementation.bounds implementation.plan
                      (serviceGraph_revealRelaxedOrdered setup .concurrent)
                        (setup.initialLaw.map encodeInputs) implementation.horizon (family tape)
                          control.remaining who control.execution fixedCounted event payload binding
                            request material (by
                              simpa only [responseEq, PhaseCount.onePacketMenu] using available)
                have typedRaw : ∃ value, raw = (⟨payload, value⟩ : Raw L) := by
                  have mapped := prepared
                  simp only [PhaseProposal.bindingPreparation, materialEq, binding] at mapped
                  obtain ⟨value, _supported, same⟩ := Option.map_eq_some_iff.mp mapped
                  exact ⟨value, same.symm⟩
                obtain ⟨value, rfl⟩ := typedRaw
                have chosen : choice.1 = some ⟨some material⟩ := by
                  rw [(offered choice).1]
                  exact congrArg some responseEq
                have packet : material.call.packet = .commitment event (who, .prepared serial) := by
                  rw [materialEq]
                exact (untyped isFalse ⟨value, serial, material, chosen, packet, prepared⟩).elim
          have comparison := clean_send_complement setup .concurrent implementation.runtime
            implementation.leaks
            implementation.bounds implementation.plan operational.completePending
              operational.outputValues operational.maximalPhases operational.wellFormed values
                fullValues tape implementation.activationGap implementation.processingGap
                  (operational.boundedGaps tape tapeInPrior) operational.timely
                    operational.candidateReserve control.remaining who control.execution
                      fixedCounted
                      event payload binding request unsentHere
                        (by simpa only [observed] using noSaved) foreign
                          (responseOf left) (responseOf choice) supported available
                            (by rw [transmitted]; exact Option.some_ne_none _) remove badPreparation
                              payoffs.utility payoffs.excludedPayoff bound nonnegative utilityBound
                                (excludedBound who) (bounded.excluded_nonpositive who)
                                  (fun terminal => bounded.excluded_le terminal who)
          simpa only [fixedValue, valueAt, family, PMF.map_comp, Function.comp_def,
            players, outcome, ReservedConcurrentImplementation.initial,
            ReservedConcurrentImplementation.base] using comparison
        simpa only [expect_constant] using expect_mono ordered
          (payoffIntegrable_constant baseline _)
          (payoffIntegrable_of_bounded _ _ (fun left => valueBound tape (responseOf left)))
  let flagError := (2 * (Fintype.card Player * cHn : Nat) + 1) *
    (⟨nativeBad, scale, scale, scale⟩ : PhaseProposalRates).flagBound * (2 * bound)
  let deviation := fun choice : (cN).Choice who site.1 =>
    (⟨site, (native.strategy who).withLaw site.1 (PMF.pure choice)⟩ :
      (cN).AssessmentDeviation who)
  have historyFlag (history : (cN).InformationHistory who site.1) (choice) :
      (cN).historyGain ((cN).runBehavioralTerminalFrom certificate)
        (fun final => final.state) (implementation.base payoffs) native (deviation choice) history ≤
          mean history choice - expect baseline (mean history) + flagError := by
    obtain ⟨control, current, active, recalled, observed⟩ := callback history
    have callbackCurrent : history.val.state =
        some ⟨control.remaining, some who, control.execution⟩ := by
      simpa only [← active] using current
    let counted : (cE).Trace (some ⟨control.remaining, some who, control.execution⟩) :=
      callbackCurrent ▸ history.val.trace
    have estimate := phaseProposal_current_gain_flag_error setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        operational.completePending operational.outputValues operational.maximalPhases values
          fullValues (⟨nativeBad, scale, scale, scale⟩ : PhaseProposalRates)
            scalePositive scaleBelow scalePositive nativeBadPositive nativeBadBelow
              implementation.horizon implementation.scheduler
    rw [PMF.map_comp] at estimate
    obtain ⟨kernel, responseLaw, responseStates, estimate⟩ := estimate control.remaining who
      control.execution counted payoffs.utility payoffs.excludedPayoff bound nonnegative
        utilityBound (excludedBound who)
    let value := fun (profile : ∀ owner, (cN).BehavioralPolicy owner)
        (responses : PMF implementation.application.Action) => expect ((responses.bind kernel).bind
      ((cN).runBehavioralTerminalFrom certificate profile)) (fun final => outcome final.state)
    have localDecoded (profile : ∀ owner, (cN).BehavioralPolicy owner)
        (lottery : PMF ((cN).Choice who site.1)) :
        (cmenu).decodeProfile implementation.initial implementation.horizon implementation.scheduler
          (Profile.update (sig := (cN).behavioralSignature) profile who
            ((profile who).withLaw site.1 lottery)) who (control.execution.recall who)
              (control.execution.observe implementation.application who) = lottery.map responseOf
                := by
      simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
        ReactiveApplication.ResponseMenu.embedPolicy, Profile.update_same, PMF.map_comp,
        Function.comp_def, ReactiveApplication.ResponseMenu.rawChoice]
      rw [recalled, observed, ← information, InformationModel.BehavioralPolicy.withLaw_self]
    have presentation (profile : ∀ owner, (cN).BehavioralPolicy owner)
        (lottery : PMF ((cN).Choice who site.1)) :
        expect ((cN).runBehavioralTerminalFrom certificate
          (Profile.update (sig := (cN).behavioralSignature) profile who
            ((profile who).withLaw site.1 lottery)) history.val) (fun final => outcome
              final.state) =
          value profile (lottery.map responseOf) := by
      have enough : implementation.application.rank implementation.horizon history.val.state ≤
          2 * implementation.horizon + 1 := by
        have bounded := implementation.application.trace_bound implementation.initial
          implementation.horizon implementation.scheduler
            ((cmenu).toRawTrace implementation.initial implementation.horizon
              implementation.scheduler history.val.trace)
        omega
      have direct := (cmenu).run_local_law_finish_of_information implementation.initial
        implementation.horizon implementation.scheduler profile history.val who control.remaining
          control.execution callbackCurrent site.1 history.property lottery
            (2 * implementation.horizon) enough
      have physical : (((lottery.map responseOf).bind kernel).bind
          ((cN).runBehavioralTerminalFrom certificate profile)).map History.state =
          (lottery.map responseOf).bind (fun response => implementation.application.finish
            implementation.initial implementation.horizon implementation.scheduler
              ((cmenu).decodeProfile implementation.initial implementation.horizon
                implementation.scheduler profile) (some ⟨control.remaining, none,
                  control.execution.respond implementation.application who response⟩)) := by
        rw [PMF.map_bind, PMF.bind_bind]
        apply bind_congr_on_support
        intro response member
        have stateLaw := responseStates
          (Profile.update (sig := (cN).behavioralSignature) profile who
            ((profile who).withLaw site.1 lottery)) response (by
              change response ∈ ((cmenu).decodeProfile implementation.initial implementation.horizon
                implementation.scheduler (Profile.update (sig := (cN).behavioralSignature)
                  profile who ((profile who).withLaw site.1 lottery)) who
                    (control.execution.recall who)
                    (control.execution.observe implementation.application who)).support
              rwa [localDecoded])
        have physical := phaseProposal_response_kernel_finish setup .concurrent
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
            implementation.prior
        rw [PMF.map_comp] at physical
        simpa only [PMF.map_bind, ReservedConcurrentImplementation.initial,
          ReservedConcurrentImplementation.scheduler, Function.comp_def] using
          physical profile kernel control.remaining who control.execution response stateLaw
      have equation : ((cN).runBehavioralTerminalFrom certificate
          (Profile.update (sig := (cN).behavioralSignature) profile who
            ((profile who).withLaw site.1 lottery)) history.val).map History.state =
          (((lottery.map responseOf).bind kernel).bind
            ((cN).runBehavioralTerminalFrom certificate profile)).map History.state := by
        rw [(cN).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
          ((cmenu).bounded implementation.initial implementation.horizon implementation.scheduler),
          direct, physical]
      simpa only [expect_map, Function.comp_def, value] using
        congrArg (fun law => expect law outcome) equation
    have meanKernel (selected) : mean history selected =
        value ordinary (PMF.pure (responseOf selected)) := by
      have terminalLaw := PhaseProposalQualifiedBinding.stoppedFinish_terminal setup .concurrent
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
          implementation.prior values
      have first := responseLaw (Profile.update (sig := (cN).behavioralSignature) ordinary who
        ((ordinary who).withLaw site.1 (PMF.pure selected)))
      have actualHistory : (⟨some ⟨control.remaining, some who, control.execution⟩, counted⟩ :
          (cE).History) = history.val := by
        dsimp only [counted]
        rcases history with ⟨⟨state, trace⟩, _atSite⟩
        cases callbackCurrent
        rfl
      change (cN).runBehavioralFrom _ 1 _ =
        (((cmenu).decodeProfile implementation.initial implementation.horizon
          implementation.scheduler _ who (control.execution.recall who)
            (control.execution.observe implementation.application who)).bind kernel) at first
      rw [actualHistory] at first
      rw [localDecoded ordinary (PMF.pure selected), PMF.pure_map, PMF.pure_bind] at first
      change expect (experiment who history.val (history.property.symm ▸ selected))
        (fun result => outcome result.2.state) = _
      have projected := expect_map (Prod.snd : (cE).History × (cE).History → (cE).History)
        (experiment who history.val (history.property.symm ▸ selected))
        (fun final => outcome final.state)
      dsimp only [Function.comp_def] at projected
      refine projected.symm.trans ?_
      dsimp only [experiment]
      have finished := terminalLaw who history.val (history.property.symm ▸ selected)
      refine (congrArg (fun law : PMF (cE).History =>
        expect law (fun final => outcome final.state)) finished).trans ?_
      have commitTransport : ∀ (first second : (cN).InfoState who) (same : first = second)
          (atom : (cN).Choice who second),
          (ordinary who).commit first (same.symm ▸ atom) =
            (ordinary who).withLaw second (PMF.pure atom) := by
        intro first second same atom
        cases same
        rfl
      change expect (((cN).runBehavioralFrom
        (Profile.update (sig := (cN).behavioralSignature) ordinary who
          ((ordinary who).commit ((cN).infoOf who history.val.trace)
            (history.property.symm ▸ selected))) 1 history.val).bind
              ((cN).runBehavioralTerminalFrom certificate ordinary))
                (fun final => outcome final.state) = _
      rw [commitTransport _ _ history.property selected, first]
      simp only [value, PMF.pure_bind]
    have cleanBaseline : expect baseline (mean history) =
        value ordinary (players who (control.execution.recall who)
          (control.execution.observe implementation.application who)) := by
      rw [expect_congr_on_support (fun selected _ => meanKernel selected)]
      calc
        _ = expect (baseline.map responseOf) (fun response => value ordinary (PMF.pure response)) :=
          (expect_map responseOf baseline (fun response => value ordinary (PMF.pure response))).symm
        _ = _ := by
          rw [rawBaseline, ← recalled, ← observed]
          simp only [value, PMF.pure_bind]
          rw [PMF.bind_bind]
          exact (expect_bind_tower_bounded _ _ _
            (fun final : (cE).History => outcomeBound final.state)).symm
    have decodedNative : (cmenu).decodeProfile implementation.initial implementation.horizon
        implementation.scheduler native.strategy = phaseProposalReferencePolicy setup .concurrent
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
            values ⟨nativeBad, scale, scale, scale⟩ := by
      rw [nativePrescribed]
      funext owner
      exact (cmenu).decode_restrictPolicy_of_covered _ _ _ _ _
        (phaseProposalReferencePolicy_covered setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values _ owner)
    have reference := localDecoded native.strategy (native.strategy who site.1)
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self,
      decodedNative] at reference
    have referenceValue := presentation native.strategy (native.strategy who site.1)
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self, ← reference]
      at referenceValue
    have historyEq : (cN).historyGain ((cN).runBehavioralTerminalFrom certificate)
        (fun final => final.state) (implementation.base payoffs) native (deviation choice) history =
        value native.strategy (PMF.pure (responseOf choice)) - value native.strategy
          (phaseProposalReferencePolicy setup .concurrent implementation.runtime
            implementation.leaks
            implementation.bounds implementation.plan values ⟨nativeBad, scale, scale, scale⟩ who
              (control.execution.recall who) (control.execution.observe
                implementation.application who)) := by
      simp only [InformationModel.historyGain, deviation, expect_map, Function.comp_def,
        Profile.update_eq_self]
      rw [presentation native.strategy (PMF.pure choice), PMF.pure_map, referenceValue]
    have error := estimate (PMF.pure (responseOf choice))
    change (value (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan implementation.initial
        implementation.horizon implementation.scheduler values ⟨nativeBad, scale, scale, scale⟩) _ -
      value (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan implementation.initial
        implementation.horizon implementation.scheduler values
          ⟨nativeBad, scale, scale, scale⟩) _) -
      (value ordinary _ - value ordinary _) ≤ flagError at error
    rw [← nativePrescribed] at error
    change (value native.strategy _ - value native.strategy _) -
      (value ordinary _ - value ordinary _) ≤ flagError at error
    rw [historyEq, meanKernel, cleanBaseline]
    linarith only [error]
  have pureComparison (choice) (typed : Bool)
      (properChoice : typed = true → ∃ value, proper value choice)
      (notProper : typed = false → ¬ ∃ value, proper value choice) :
      gain choice ≤ (if typed = true then qualifiedValue choice - expect baseline qualifiedValue
        else 0) + nativeError := by
    have pointwise (history : (cN).InformationHistory who site.1) :
        (cN).historyGain ((cN).runBehavioralTerminalFrom certificate)
          (fun final => final.state) (implementation.base payoffs) native (deviation choice)
            history ≤
        (if typed = true then retained history choice - expect baseline (retained history) else 0) +
          (if bad history then 2 * bound else 0) + flagError := by
      exact retained_gain_le baseline (mean history) (retained history)
        (residual history) (bad history) bound flagError _ choice typed nonnegative
        (meanBound history) (payoffIntegrable_of_finite _ _) (fun _ => rfl)
        (fun selected => by
          simp only [residual, mean, Bool.false_eq_true, false_and, ite_false])
        (historyFlag history choice)
        (fun good => physicalOrder history good choice typed properChoice notProper)
    have presentation : gain choice = expect (native.belief who site)
        ((cN).historyGain ((cN).runBehavioralTerminalFrom certificate)
          (fun final => final.state) (implementation.base payoffs) native (deviation choice)) := by
      change (cN).localGain cHn (fun final => final.state) _ native site (PMF.pure choice) = _
      change expect ((cN).assessmentComparisonWith ((cN).truncatedRunner cHn)
        (fun final => final.state) native who (deviation choice)).alternative _ -
          expect ((cN).assessmentComparisonWith ((cN).truncatedRunner cHn)
            (fun final => final.state) native who (deviation choice)).prescribed _ = _
      have runner : (cN).truncatedRunner cHn = (cN).runBehavioralTerminalFrom certificate := by
        funext profile history
        exact ((cN).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
          ((cmenu).bounded implementation.initial implementation.horizon implementation.scheduler)
            profile history).symm
      rw [runner, (cN).gain_eq_expect_historyGain]
    rw [presentation]
    have badMean : expect (native.belief who site) (fun history =>
        if bad history then 2 * bound else 0) = 2 * bound * nativePast := by
      rw [expect_eq_sum]
      dsimp only [nativePast]
      rw [Finset.mul_sum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro history _
      by_cases generated : bad history
      · simp only [bad] at generated ⊢
        simp only [generated, ite_true]
        ring
      · simp only [bad] at generated ⊢
        simp only [generated, ite_false, mul_zero]
    have errorEq : 2 * bound * nativePast + flagError = nativeError := by
      dsimp only [nativeError, flagError]
      ring
    have estimate := expect_retained_gain_le (native.belief who site) baseline
      ((cN).historyGain ((cN).runBehavioralTerminalFrom certificate)
        (fun final => final.state) (implementation.base payoffs) native (deviation choice))
      retained qualifiedValue (fun history => if bad history then 2 * bound else 0)
      flagError choice typed (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _) qualifiedMean pointwise
    rw [badMean] at estimate
    calc
      _ ≤ (if typed = true then qualifiedValue choice - expect baseline qualifiedValue else 0) +
          2 * bound * nativePast + flagError := estimate
      _ = _ := by rw [add_assoc, errorEq]
  refine ⟨?_, ?_, supportedProper, preparationLaw⟩
  · intro choice typed
    simpa only [ite_true] using pureComparison choice true (fun _ => typed)
      (fun impossible => by cases impossible)
  · intro choice untyped
    simpa only [Bool.false_eq_true, ite_false, zero_add] using
      pureComparison choice false (fun impossible => by cases impossible) (fun _ => untyped)

end CleanBindingComparison

end Vegas

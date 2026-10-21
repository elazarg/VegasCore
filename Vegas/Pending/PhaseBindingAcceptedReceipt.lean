/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingStampHistory
import Vegas.Pending.PhaseBindingReceiptResolution
import Vegas.Pending.PhaseArchivedBindings

/-! # Live and retired accepted bindings have actual accepting receipts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

open scoped Classical in
/-- Actual own outputs with their permanent true receipt, rather than all
submitted packets or all ledger packets. -/
def acceptingBindingOutputs (execution : (app).Execution) (owner : Player) :
    List (Message Player (CommitAttemptPacket graph)) :=
  ((app).outputs (execution.recall owner)).filter fun message =>
    (message.id, true) ∈ execution.receipts

private theorem acceptingBindingOutputs_mono (before after : (app).Execution)
    (recallKept : ∀ owner, before.recall owner ⊆ after.recall owner)
    (receiptsKept : before.receipts ⊆ after.receipts) (owner : Player) :
    acceptingBindingOutputs runtime leaks before owner ⊆
      acceptingBindingOutputs runtime leaks after owner := by
  classical
  intro message member
  obtain ⟨authored, accepted⟩ := List.mem_filter.mp member
  obtain ⟨entry, recalled, emitted⟩ := List.mem_filterMap.mp authored
  exact List.mem_filter.mpr ⟨List.mem_filterMap.mpr
    ⟨entry, recallKept owner recalled, emitted⟩,
      by simpa only [decide_eq_true_eq] using
        receiptsKept (of_decide_eq_true accepted)⟩

private theorem includePending_acceptingBindingOutputs (execution : (app).Execution)
    (id : MessageId Player) (owner : Player) :
    acceptingBindingOutputs runtime leaks execution owner ⊆
      acceptingBindingOutputs runtime leaks (execution.includePending app id) owner := by
  apply acceptingBindingOutputs_mono
  · intro who
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases execution.network.lookup id <;> exact List.Subset.refl _
  · exact ((app).includePending_receipts_prefix execution id).subset

private theorem includePending_accepting_message (execution : (app).Execution)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (next : PhaseRuntimeState graph) (found : execution.network.lookup id = some message)
    (handled : execution.application.handle runtime message = some next)
    (origins : execution.Provenance app) :
    message ∈ acceptingBindingOutputs runtime leaks (execution.includePending app id)
      message.sender := by
  classical
  have addressed : message.id = id := by
    simpa only [decide_eq_true_eq] using (List.find?_eq_some_iff_append.mp found).1
  obtain ⟨entry, recalled, _material, _transmitted, emitted, _packet⟩ :=
    origins.lookup id message found
  have recallEq : (execution.includePending app id).recall = execution.recall := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  change message ∈ (((app).outputs
    ((execution.includePending app id).recall message.sender)).filter
      (fun issued => decide ((issued.id, true) ∈ (execution.includePending app id).receipts)))
  rw [recallEq]
  apply List.mem_filter.mpr
  refine ⟨List.mem_filterMap.mpr ⟨entry, recalled, emitted⟩, ?_⟩
  change decide ((message.id, true) ∈ (execution.includePending app id).receipts) = true
  apply decide_eq_true
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, show (app).handle execution.application message = some next from handled,
    Option.isSome_some, addressed]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- True receipts retain both each attempt's exact namespace and every inherited
accepted handle in saved, live and retired snapshots. -/
structure BindingAcceptedReceipts (execution : (app).Execution) : Prop where
  liveStamp : BindingStamp (acceptingBindingOutputs runtime leaks execution)
    execution.application.attempt execution.application.current.native
  retiredStamp : ∀ record ∈ execution.application.retired,
    BindingStamp (acceptingBindingOutputs runtime leaks execution) record.attempt record.state
  saved : SignedBindingTable (acceptingBindingOutputs runtime leaks execution)
    execution.application.entry.native
  live : SignedBindingTable (acceptingBindingOutputs runtime leaks execution)
    execution.application.current.native
  retired : ∀ record ∈ execution.application.retired,
    SignedBindingTable (acceptingBindingOutputs runtime leaks execution) record.state

private theorem bindingAcceptedReceipts_respond (execution : (app).Execution)
    (owner : Player) (response : (app).Action)
    (valid : BindingAcceptedReceipts runtime leaks execution) :
    BindingAcceptedReceipts runtime leaks (execution.respond app owner response) := by
  have more := acceptingBindingOutputs_mono runtime leaks execution
    (execution.respond app owner response)
    ((app).respond_recall_mono execution owner · response)
    (by rw [(app).respond_receipts])
  have liveStamp := valid.liveStamp.mono more
  have retiredStamp := fun record member => (valid.retiredStamp record member).mono more
  have saved := valid.saved.mono more
  have live := valid.live.mono more
  have retired := fun record member => (valid.retired record member).mono more
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨liveStamp, retiredStamp, saved, live, retired⟩
  | some material =>
    have table : (submitStep (material.call.register execution.application.current.native owner)
        owner material.call.packet).accepted = execution.application.current.native.accepted := by
      rw [submitStep_accepted, Submission.register_accepted]
    exact ⟨liveStamp.copy table, retiredStamp, saved, live.copy table, retired⟩

private theorem bindingAccepted_handle
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (state : PhaseRuntimeState graph) (native : State graph)
    (message : Message Player (CommitAttemptPacket graph))
    (old : BindingStamp outputs state.attempt state.current.native)
    (signed : SignedBindingTable outputs state.current.native)
    (present : message ∈ outputs message.sender)
    (current : message.payload.attempt = state.attempt)
    (accepted : EventGraphRuntime.handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    BindingStamp outputs state.attempt native ∧ SignedBindingTable outputs native := by
  rcases handle_tables_cases runtime state.current.native native _ accepted with
    ⟨event, candidate, called, _, table, owner⟩ | ⟨table, _⟩
  · constructor
    · intro field handle installed
      change native.accepted (.inr field) = some handle at installed
      rw [table] at installed
      by_cases same : field = event
      · subst field
        rw [Function.update_self] at installed
        cases Option.some.inj installed
        exact Or.inr ⟨message, by simpa only [Message.sender, owner] using present,
          owner.symm, called, current⟩
      · rw [Function.update_of_ne (by simpa using same)] at installed
        exact old field handle installed
    · constructor
      · intro input handle installed
        change native.accepted (.inl input) = some handle at installed
        rw [table, Function.update_of_ne (by simp)] at installed
        exact signed.1 input handle installed
      · intro field handle installed
        change native.accepted (.inr field) = some handle at installed
        rw [table] at installed
        by_cases same : field = event
        · subst field
          rw [Function.update_self] at installed
          cases Option.some.inj installed
          exact ⟨message, by simpa only [Message.sender, owner] using present, owner.symm, called⟩
        · rw [Function.update_of_ne (by simpa using same)] at installed
          exact signed.2 field handle installed
  · exact ⟨old.copy table, signed.copy table⟩

private theorem bindingAcceptedReceipts_includePending (execution : (app).Execution)
    (id : MessageId Player) (valid : BindingAcceptedReceipts runtime leaks execution)
    (record : execution.application.ExclusionRecord) (origins : execution.Provenance app) :
    BindingAcceptedReceipts runtime leaks (execution.includePending app id) := by
  classical
  let outputs := acceptingBindingOutputs runtime leaks (execution.includePending app id)
  have live : BindingStamp outputs execution.application.attempt
      execution.application.current.native :=
    valid.liveStamp.mono (includePending_acceptingBindingOutputs runtime leaks execution id)
  have archives : ∀ retired ∈ execution.application.retired,
      BindingStamp outputs retired.attempt retired.state :=
    fun retired member => (valid.retiredStamp retired member).mono
      (includePending_acceptingBindingOutputs runtime leaks execution id)
  have saved := valid.saved.mono
    (includePending_acceptingBindingOutputs runtime leaks execution id)
  have signed := valid.live.mono
    (includePending_acceptingBindingOutputs runtime leaks execution id)
  have signedArchives := fun retired member => (valid.retired retired member).mono
    (includePending_acceptingBindingOutputs runtime leaks execution id)
  cases found : execution.network.lookup id with
  | none =>
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found] using (show BindingAcceptedReceipts runtime leaks
        {execution.includePending app id with application := execution.application} from
          ⟨live, archives, saved, signed, signedArchives⟩)
  | some message =>
    cases handled : execution.application.handle runtime message with
    | none =>
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, show (app).handle execution.application message = none from handled,
        Option.getD_none] using (show BindingAcceptedReceipts runtime leaks
          {execution.includePending app id with application := execution.application} from
            ⟨live, archives, saved, signed, signedArchives⟩)
    | some next =>
      have present : message ∈ outputs message.sender := by
        exact includePending_accepting_message runtime leaks execution id message next found
          handled origins
      have current := PhaseRuntimeState.handle_attempt_eq runtime execution.application next
        message handled
      have actualHandled := handled
      unfold PhaseRuntimeState.handle at handled
      split at handled
      · rename_i allowed
        obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
        have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
        have raw := bindingAccepted_handle runtime outputs execution.application native
          message live signed present current accepted
        have rawStamp := raw.1
        have frontier := PhaseRuntimeState.raw_handle_frontier runtime _ record.frontier
          _ native authorized accepted
        have complete := record.active.step (completionStep_handle runtime _ native _ accepted)
        have result := PhaseRuntimeState.normalize_bindingStamp outputs _ frontier record.saved
          complete rawStamp
        have retired := PhaseRuntimeState.normalize_archivedBindingStamp outputs _ frontier
          record.saved complete rawStamp archives
        have signedResult := PhaseRuntimeState.settle_signedBindings outputs
          execution.application.phases execution.application.generation execution.application.entry
          (execution.application.current.inclusionResult message.payload.packet.call native)
          execution.application.retired saved raw.2 signedArchives
        simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, show (app).handle execution.application message = some _ from actualHandled,
          Option.getD_some] using (show BindingAcceptedReceipts runtime leaks
            {execution.includePending app id with application :=
              ({execution.application with current :=
                (execution.application.current.inclusionResult message.payload.packet.call native)}
                : PhaseRuntimeState graph).normalize} from
            ⟨result, retired, signedResult.1, signedResult.2.1, signedResult.2.2⟩)
      · cases handled

private theorem bindingAcceptedReceipts_environment (execution next : (app).Execution)
    (command : (app).Command) (valid : BindingAcceptedReceipts runtime leaks execution)
    (record : execution.application.ExclusionRecord) (origins : execution.Provenance app)
    (reached : next ∈ (execution.environmentStep app command).support) :
    BindingAcceptedReceipts runtime leaks next := by
  cases command with
  | wait =>
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff ..).mp reached
    exact ⟨valid.liveStamp, valid.retiredStamp, valid.saved, valid.live, valid.retired⟩
  | activate owner =>
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
    obtain ⟨sample, _selected, rfl⟩ := PMF.support_map .. ▸ supported
    exact ⟨valid.liveStamp, valid.retiredStamp, valid.saved, valid.live, valid.retired⟩
  | «include» id =>
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff ..).mp reached
    have kept := bindingAcceptedReceipts_includePending runtime leaks execution id
      valid record origins
    exact ⟨kept.liveStamp, kept.retiredStamp, kept.saved, kept.live, kept.retired⟩
  | application operation =>
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
    obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ supported
    change state ∈ (execution.application.environment runtime operation).support at moved
    unfold PhaseRuntimeState.environment at moved
    split at moved
    · rename_i allowed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ moved
      have frontier := PhaseRuntimeState.raw_environment_frontier runtime _ record.frontier
        _ native allowed nativeMoved
      have complete := record.active.step
        (completionStep_environmentStep runtime _ native operation nativeMoved)
      have rawStamp := valid.liveStamp.copy
        (environmentStep_tables runtime _ _ operation nativeMoved).1
      have signed := PhaseRuntimeState.settle_signedBindings _
        execution.application.phases execution.application.generation execution.application.entry
        (execution.application.current.environmentResult operation native)
        execution.application.retired valid.saved
        (valid.live.copy (environmentStep_tables runtime _ _ operation nativeMoved).1) valid.retired
      exact ⟨PhaseRuntimeState.normalize_bindingStamp _ _ frontier record.saved complete rawStamp,
        PhaseRuntimeState.normalize_archivedBindingStamp _ _ frontier record.saved complete
          rawStamp valid.retiredStamp, signed.1, signed.2.1, signed.2.2⟩
    · cases (PMF.mem_support_pure_iff ..).mp moved
      exact ⟨valid.liveStamp, valid.retiredStamp, valid.saved, valid.live, valid.retired⟩

/-- Every actual live or archived accepted binding has a real true-receipted
owner output, retaining its original full attempt through normalization. -/
theorem phaseBindingAcceptedReceipts_history (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) : BindingAcceptedReceipts runtime leaks control.execution := by
  have invariant : (app).ServiceInvariant scheduler (fun execution =>
      BindingAcceptedReceipts runtime leaks execution ∧ execution.application.ExclusionRecord ∧
        execution.Provenance app) := {
    respond := fun execution owner response valid =>
      ⟨bindingAcceptedReceipts_respond runtime leaks execution owner response valid.1,
        (phaseApplication_exclusionRecord runtime leaks).respond execution owner response valid.2.1,
        (app).respond_provenance execution owner response valid.2.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨bindingAcceptedReceipts_environment runtime leaks execution next command valid.1 valid.2.1
          valid.2.2 reached,
        (phaseApplication_exclusionRecord runtime leaks).environmentStep execution next command
          valid.2.1 reached,
        (app).environment_provenance execution next command valid.2.2 reached⟩ }
  exact (invariant.history _ horizon (by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    have empty : ∀ event candidate, (State.initial draw).accepted (.inr event) = some candidate →
        False := by
      intro event candidate accepted
      obtain ⟨_input, _owner, _payload, impossible, _rest⟩ :=
        State.initial_accepted_eq_some draw (.inr event) candidate accepted
      cases impossible
    have saved : ∀ phase ∈ plan.phases.head?, ∀ event candidate,
        (State.initial draw).accepted (.inr event) = some candidate → event.val < phase.low :=
      fun _ _ event candidate accepted => (empty event candidate accepted).elim
    have bounded : ∀ phase ∈ plan.phases.head?, ∀ event candidate,
        (State.initial draw).accepted (.inr event) = some candidate → event.val < phase.high :=
      fun _ _ event candidate accepted => (empty event candidate accepted).elim
    have active : BindingStamp (fun _ => []) ⟨PhaseRuntimeState.phaseLow plan.phases, 0⟩
        (State.initial draw) := fun event candidate accepted =>
          (empty event candidate accepted).elim
    have signed := PhaseRuntimeState.settle_signedBindings (fun _ => []) plan.phases 0
      ⟨State.initial draw, ∅⟩ ⟨State.initial draw, ∅⟩ []
      (SignedBindingTable.initial draw) (SignedBindingTable.initial draw)
      (fun _ impossible => (List.not_mem_nil impossible).elim)
    exact ⟨⟨PhaseRuntimeState.settle_bindingStamp _ plan.phases 0 _ _ [] plan.adjacent
        saved bounded active,
      PhaseRuntimeState.settle_archivedBindingStamp _ plan.phases 0 _ _ [] plan.adjacent
        saved bounded active (fun _ impossible => (List.not_mem_nil impossible).elim),
      signed.1, signed.2.1, signed.2.2⟩,
      PhaseRuntimeState.initial_exclusionRecord plan draw, MessageNetwork.Satisfies.empty⟩) trace).1

/-- A successful physical inclusion exposes its original native snapshot and
certifies every binding accepted there by a true receipt in the same actual
execution. The snapshot precedes normalization, so a clean phase advance
does not replace its original attempt by the successor's namespace. -/
theorem phase_inclusion_snapshot_bindingAccepted (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (id : MessageId Player)
    (message : Message Player (CommitAttemptPacket graph))
    (found : control.execution.network.lookup id = some message) (next : PhaseRuntimeState graph)
    (handled : control.execution.application.handle runtime message = some next) :
    ∃ native : State graph,
      EventGraphRuntime.handle runtime control.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      next = ({ control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize ∧
      (∀ event candidate, control.execution.application.attempt.phase ≤ event.val →
        native.accepted (.inr event) = some candidate →
        PhaseService.BindingAccepted runtime leaks
          ⟨control.execution.application.attempt, event⟩ candidate.1
            (control.execution.includePending app id)) ∧
      BindingStamp (fun who => (app).outputs (control.execution.recall who))
        control.execution.application.attempt native := by
  classical
  let outputs := acceptingBindingOutputs runtime leaks (control.execution.includePending app id)
  have stamp := (phaseBindingAcceptedReceipts_history runtime leaks plan inputs horizon scheduler
    trace).liveStamp.mono
      (includePending_acceptingBindingOutputs runtime leaks control.execution id)
  have present := includePending_accepting_message runtime leaks control.execution id message next
    found handled ((app).history_provenance _ horizon scheduler trace)
  have current := PhaseRuntimeState.handle_attempt_eq runtime control.execution.application next
    message handled
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · obtain ⟨native, accepted, normalized⟩ := Option.map_eq_some_iff.mp handled
    have signed := (phaseBindingAcceptedReceipts_history runtime leaks plan inputs horizon
      scheduler trace).live.mono
        (includePending_acceptingBindingOutputs runtime leaks control.execution id)
    have rawStamp := (bindingAccepted_handle runtime outputs control.execution.application
      native message stamp signed present current accepted).1
    refine ⟨native, accepted, normalized.symm, ?_, ?_⟩
    · intro event candidate lower installed
      rcases rawStamp event candidate installed with earlier |
        ⟨packet, member, sender, called, attemptEq⟩
      · omega
      · obtain ⟨authored, received⟩ := List.mem_filter.mp member
        have recallEq : (control.execution.includePending app id).recall =
            control.execution.recall := by
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
        have inputsEq : (control.execution.includePending app id).network.inputs =
            control.execution.network.inputs := by
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
        have recalled := (app).history_inputRecall (inputs.map (PhaseRuntimeState.initial plan))
          horizon scheduler trace candidate.1
        rw [recallEq, ← recalled] at authored
        exact ⟨packet, by rw [inputsEq]; exact (List.mem_filter.mp authored).1,
          sender, attemptEq, by simp only [called, Payload.event?], of_decide_eq_true received⟩
    · apply rawStamp.mono
      intro who packet member
      have unfiltered := (List.mem_filter.mp member).1
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] using unfiltered
  · cases handled

/-- Current-attempt accepted bindings certify actual true receipts without
requiring every owner to remain clear. -/
theorem phase_live_bindingAccepted (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (event : graph.EventId)
    (inside : control.execution.application.attempt.phase ≤ event.val) (candidate : Handle graph)
    (accepted :
      control.execution.application.current.native.accepted (.inr event) = some candidate) :
    PhaseService.BindingAccepted runtime leaks ⟨control.execution.application.attempt, event⟩
      candidate.1 control.execution := by
  classical
  have stamped := (phaseBindingAcceptedReceipts_history runtime leaks plan inputs horizon scheduler
    trace).liveStamp event candidate accepted
  rcases stamped with earlier | ⟨message, member, sender, called, attemptEq⟩
  · omega
  · obtain ⟨authored, received⟩ := List.mem_filter.mp member
    have recalled := (app).history_inputRecall (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler trace candidate.1
    rw [← recalled] at authored
    exact ⟨message, (List.mem_filter.mp authored).1, sender, attemptEq,
      by simp only [called, Payload.event?], of_decide_eq_true received⟩

/-- An actual accepted binding in the original archived phase has a true
physical receipt in that exact namespace, even when the owner later failed. -/
theorem phase_archived_bindingAccepted (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (record : RetiredCommitAttempt graph)
    (retired : record ∈ control.execution.application.retired) (event : graph.EventId)
    (inside : record.attempt.phase ≤ event.val) (candidate : Handle graph)
    (accepted : record.state.accepted (.inr event) = some candidate) :
    PhaseService.BindingAccepted runtime leaks ⟨record.attempt, event⟩ candidate.1
      control.execution := by
  classical
  have stamped := (phaseBindingAcceptedReceipts_history runtime leaks plan inputs horizon scheduler
    trace).retiredStamp record retired event candidate accepted
  rcases stamped with earlier | ⟨message, member, sender, called, attemptEq⟩
  · omega
  · obtain ⟨authored, received⟩ := List.mem_filter.mp member
    have recalled := (app).history_inputRecall (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler trace candidate.1
    rw [← recalled] at authored
    exact ⟨message, (List.mem_filter.mp authored).1, sender, attemptEq,
      by simp only [called, Payload.event?], of_decide_eq_true received⟩

/-- Every completed archived binding of an owner surviving the original
phase has an actual accepting receipt. Failure coverage excludes omission;
the receipt stamp retains the pre-reset physical attempt. -/
theorem phase_archived_survivor_bindingAccepted (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (record : RetiredCommitAttempt graph)
    (retired : record ∈ control.execution.application.retired)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (lower : record.attempt.phase ≤ event.val)
    (completed : event ∈ record.state.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded) :
    PhaseService.BindingAccepted runtime leaks ⟨record.attempt, event⟩ owner control.execution := by
  have archive := phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler trace
  obtain ⟨_phase, _installed, _address, _kind, _finished, _receipts, covered⟩ :=
    archive.archives record retired
  have present : record.state.accepted (.inr event) ≠ none := by
    intro missing
    have missed := (record.state.publicView_missedBinding event owner payload binding).mpr
      ⟨completed, missing⟩
    exact surviving (covered event owner (actor?_of_outputLayout_binding graph binding)
      (Or.inl missed))
  obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
  obtain ⟨valid, _native, _fixed⟩ :=
    phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler trace record retired
  have owned : candidate.1 = owner := by
    obtain ⟨_otherPayload, typed⟩ := valid.accepted_typed (.inr event) candidate accepted
    exact (EventField.binding.inj (typed.symm.trans binding)).1
  simpa only [owned] using
    phase_archived_bindingAccepted runtime leaks plan inputs horizon scheduler
      trace record retired event lower candidate accepted

end Vegas.EventGraphRuntime

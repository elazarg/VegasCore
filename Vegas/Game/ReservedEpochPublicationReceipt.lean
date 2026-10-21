/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOpeningReceiptOrigins
import Vegas.Game.PhaseProposalPublicationImage
import Vegas.Game.CompiledRevealPhase
import Vegas.Game.ReservedEpochStoppedCoupling
import Vegas.Pending.PhaseSemanticProgress

/-! # Physical TRUE receipts in the original completed publication image -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem phaseClosingEffect_history_prefix (before after : (app).Execution)
    (raw : RecoveryState graph) (effect : PhaseClosingEffect runtime leaks before after raw) :
    before.application.current.native.config.history.IsPrefix raw.native.config.history := by
  rcases effect with included | applied
  · obtain ⟨id, message, native, found, stepped, handled, rfl⟩ := included
    obtain ⟨event, named, ready, action, supported⟩ :=
      handle_config_mem_step runtime before.application.current.native native
        ⟨message.id, message.payload.packet.call⟩ handled
    change before.application.current.native.config.history.IsPrefix native.config.history
    rw [before.application.current.native.config.step_history event ready action native.config
      supported]
    exact ⟨_, rfl⟩
  · obtain ⟨command, native, stepped, moved, rfl⟩ := applied
    exact environmentStep_history_prefix runtime before.application.current.native native command
      moved

omit [Fintype Player] in
/-- The original raw closing reply and its actual drain retain TRUE physical
receipt origins. No normalized successor or semantic guard verdict replaces it. -/
theorem closing_opening_receipt_origins (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (before : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before))
    (after : (app).Execution) (raw : RecoveryState graph)
    (changed : after.application.attempt ≠ before.execution.application.attempt)
    (effect : PhaseClosingEffect runtime leaks before.execution after raw)
    (phase : RuntimePhase graph) :
    PhaseProposal.OpeningOrigins (PhaseProposal.trueReceiptInputs runtime leaks after)
      (phase.drain raw).native := by
  have valid := PhaseProposal.openingReceiptOrigins_history runtime leaks plan inputs horizon
    scheduler before trace
  rcases effect with included | applied
  · obtain ⟨id, message, native, found, stepped, handled, rfl⟩ := included
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at stepped
    cases (PMF.mem_support_pure_iff _ _).mp stepped
    obtain ⟨next, phaseHandled⟩ : ∃ next,
        before.execution.application.handle runtime message = some next := by
      cases result : before.execution.application.handle runtime message with
      | none =>
          have unchanged : (before.execution.includePending app id).application =
              before.execution.application := by
            simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
              found, show (app).handle before.execution.application message = none from result,
              Option.getD_none]
          exact (changed (congrArg PhaseRuntimeState.attempt unchanged)).elim
      | some next => exact ⟨next, rfl⟩
    exact (valid.inclusion runtime leaks before.execution
      ((app).history_provenance _ horizon scheduler trace)
      ((app).history_inputRecall _ horizon scheduler trace) id message found next phaseHandled
        native handled).drain _ phase
  · obtain ⟨command, native, stepped, moved, rfl⟩ := applied
    have sameInputs := (app).environmentStep_inputs before.execution after
      (.application command) stepped
    have sameReceipts : after.receipts = before.execution.receipts := by
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ stepped
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
    have same : PhaseProposal.trueReceiptInputs runtime leaks after =
        PhaseProposal.trueReceiptInputs runtime leaks before.execution := by
      unfold PhaseProposal.trueReceiptInputs
      rw [sameInputs, sameReceipts]
    rw [same]
    exact (valid.1.environment runtime command native moved).drain _ phase

/-- Any recorded TRUE completion in the original phase is witnessed by its
literal full-attempt submitted opening and TRUE physical receipt. This includes
the owner's first rejecting guard and does not claim source success. -/
theorem closing_disclosure_has_receipt (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (before : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (after : (app).Execution) (raw : RecoveryState graph)
    (changed : after.application.attempt ≠ before.execution.application.attempt)
    (effect : PhaseClosingEffect runtime leaks before.execution after raw)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (event : graph.EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (action : (graph.outputLayout event).Action)
    (recorded : ⟨event, action⟩ ∈ (phase.drain raw).native.config.history)
    (disclosed : cast (congrArg EventField.Action publication) action = true) :
    ∃ (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
      (value : Raw L), message ∈ after.network.inputs ∧
      message.payload.attempt = before.execution.application.attempt ∧
      message.payload.packet.call = .opening event candidate value ∧
      (message.id, true) ∈ after.receipts := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have origins := closing_opening_receipt_origins runtime leaks plan inputs horizon scheduler before
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace)
      after raw changed effect phase
  have actual : PhaseProposal.publicationDiscloses (graph.outputLayout event) action = true :=
    (PhaseProposal.publicationDiscloses_cast publication action).symm.trans disclosed
  obtain ⟨message, present, candidate, value, call⟩ := origins ⟨event, action⟩ recorded actual
  obtain ⟨input, received⟩ := List.mem_filter.mp present
  have inputsEq : after.network.inputs = before.execution.network.inputs := by
    rcases effect with included | applied
    · obtain ⟨id, packet, native, found, stepped, handled, rawEq⟩ := included
      exact (app).environmentStep_inputs before.execution after (.include id) stepped
    · obtain ⟨command, native, stepped, moved, rawEq⟩ := applied
      exact (app).environmentStep_inputs before.execution after (.application command) stepped
  have proposed : PhaseProposal.packetProposal? message.payload =
      some (⟨message.payload.attempt, event⟩, value) := by
    simp only [PhaseProposal.packetProposal?, call]
  have address := PhaseProposal.submitted_opening_installed_attempt runtime leaks bounds plan
    ordered inputs horizon scheduler before trace phase (Option.mem_def.mp installed) _ inside
      message (by rwa [inputsEq] at input) value proposed
  exact ⟨message, candidate, value, input, address, call, of_decide_eq_true received⟩

/-- A TRUE receipt of the original counted opening records the literal TRUE
native action in the pre-normalization original snapshot. The receipt may
itself reject the semantic guard and end the owner's surviving prefix. -/
theorem original_opening_receipt_recorded (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (start before ending : (app).Control)
    (startTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some start))
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (joint : Player → Option (app).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal (some before) joint)
    (realized : some ending ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) joint).support)
    (fromStart : TracePrefix startTrace prior)
    (same : start.execution.application.attempt = before.execution.application.attempt)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ ending.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (value : Raw L)
    (call : message.payload.packet.call = .opening event candidate value)
    (address : message.payload.attempt = start.execution.application.attempt)
    (absent : (message.id, true) ∉ start.execution.receipts)
    (received : (message.id, true) ∈ ending.execution.receipts) :
    ∃ action : (graph.outputLayout event).Action,
      ⟨event, action⟩ ∈ raw.native.config.history ∧
        PhaseProposal.publicationDiscloses (graph.outputLayout event) action = true := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let closed := prior.extend joint legal realized
  have closedPrefix : TracePrefix startTrace closed := .extend fromStart joint legal realized
  obtain ⟨acceptingBefore, acceptingAfter, acceptingTrace, acceptingJoint, acceptingLegal,
      acceptingRealized, toAccepting, afterAccepting, noReceipt, selected, moved, accepted⟩ :=
    prefix_accepting_receipt_boundary runtime leaks menu initial horizon scheduler start ending
      startTrace closed closedPrefix message.id absent received
  let acceptedTrace := acceptingTrace.extend acceptingJoint acceptingLegal acceptingRealized
  have acceptingPrefix : TracePrefix acceptingTrace closed :=
    (TracePrefix.extend .refl acceptingJoint acceptingLegal acceptingRealized).trans afterAccepting
  have rawClosed := menu.toRawTrace initial horizon scheduler closed
  have rawAccepting := menu.toRawTrace initial horizon scheduler acceptingTrace
  have found : acceptingBefore.execution.network.lookup message.id = some message := by
    cases lookup : acceptingBefore.execution.network.lookup message.id with
    | none =>
        have unchanged := moved
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at unchanged
        have literal := (PMF.mem_support_pure_iff _ _).mp unchanged
        have equal := congrArg (fun execution : (app).Execution => execution.receipts) literal
        have receiptsEqual : acceptingAfter.execution.receipts =
            acceptingBefore.execution.receipts := by
          simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            lookup] using equal
        exact (noReceipt (receiptsEqual ▸ accepted)).elim
    | some actual =>
        have pending := List.mem_of_find?_eq_some lookup
        have actualInput := ((app).retained_envelopes_mem_inputs acceptingBefore.execution
          ((app).history_provenance initial horizon scheduler rawAccepting)
          ((app).history_inputRecall initial horizon scheduler rawAccepting)).pending actual pending
        have atEnd := input_mem_prefix runtime leaks menu initial horizon scheduler acceptingBefore
          ending acceptingTrace closed acceptingPrefix actual actualInput
        have sameId : actual.id = message.id := by
          simpa only [decide_eq_true_eq] using List.find?_some lookup
        have actualEq := (app).input_identifier_injective_history initial horizon scheduler ending
          rawClosed actual message atEnd input sameId
        exact congrArg some actualEq
  have pending := List.mem_of_find?_eq_some found
  have acceptingInput := ((app).retained_envelopes_mem_inputs acceptingBefore.execution
    ((app).history_provenance initial horizon scheduler rawAccepting)
    ((app).history_inputRecall initial horizon scheduler rawAccepting)).pending message pending
  obtain ⟨native, following, phaseHandled, nativeHandled⟩ :=
    accepting_include_native runtime leaks plan inputs horizon scheduler acceptingBefore
      rawAccepting acceptingAfter.execution message acceptingInput noReceipt moved accepted
  have typedHandled : handle runtime acceptingBefore.execution.application.current.native
      ⟨message.id, .opening event candidate value⟩ = some native := by
    simpa only [call] using nativeHandled
  obtain ⟨ready, action, completed, _clock, _stamp, owner, payload, binding, checks,
    publication, code, node, actionEq⟩ := handle_opening_config_step runtime
      acceptingBefore.execution.application.current.native native message.id event candidate value
        typedHandled
  have installed : (⟨event, action⟩ : graph.Completion) ∈ native.config.history := by
    rw [acceptingBefore.execution.application.current.native.config.step_history event ready action
      native.config completed]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have disclosed : PhaseProposal.publicationDiscloses (graph.outputLayout event) action = true := by
    rw [actionEq]
    exact PhaseProposal.publicationDiscloses_cast publication.symm true
  refine ⟨action, ?_, disclosed⟩
  have closingBeforePrefix : TracePrefix prior closed := by
    change TracePrefix prior (prior.extend joint legal realized)
    exact TracePrefix.extend (E := menu.protocol initial horizon scheduler)
      .refl joint legal realized
  by_cases earlier : acceptedTrace.length ≤ prior.length
  · have toClosing : TracePrefix acceptedTrace prior :=
      (ReachesWithin.ancestor_comparable (E := menu.protocol initial horizon scheduler)
        (first := ⟨some acceptingAfter, acceptedTrace⟩) (second := ⟨some before, prior⟩)
        (target := ⟨some ending, closed⟩) afterAccepting.reachesWithin
        closingBeforePrefix.reachesWithin earlier).tracePrefix
    have initialized : ∀ state ∈ initial.support, state.Ordered := by
      intro state member
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_ordered plan draw
    have orderedBefore := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized rawAccepting
    have orderedAfter := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized (menu.toRawTrace initial horizon scheduler acceptedTrace)
    have startProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon scheduler start acceptingAfter startTrace acceptedTrace
        (.extend toAccepting acceptingJoint acceptingLegal acceptingRealized)
        ((phaseApplication_seedOrder runtime leaks).history initial horizon scheduler initialized
          (menu.toRawTrace initial horizon scheduler startTrace))
    have endProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon scheduler acceptingAfter before acceptedTrace prior toClosing orderedAfter
    have afterSame : acceptingAfter.execution.application.attempt =
        before.execution.application.attempt := by
      have generation := congrArg CommitAttemptId.generation same
      have phase := congrArg CommitAttemptId.phase same
      cases first : start.execution.application.attempt
      cases middle : acceptingAfter.execution.application.attempt
      cases last : before.execution.application.attempt
      simp only [first, middle, last] at startProgress endProgress generation phase
      congr <;> omega
    obtain ⟨sameNative, handled, normalized, _receipts, _rawStamp⟩ :=
      phase_inclusion_snapshot_bindingAccepted runtime leaks plan inputs horizon scheduler
        rawAccepting message.id message found following phaseHandled
    have nativeEq : sameNative = native := Option.some.inj (handled.symm.trans nativeHandled)
    subst sameNative
    have afterApplication : acceptingAfter.execution.application = following := by
      have literal := moved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at literal
      have equal := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp literal)
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, show (app).handle acceptingBefore.execution.application message = some following
          from phaseHandled, Option.getD_some] using equal
    have rawAttempt : message.payload.attempt = acceptingBefore.execution.application.attempt :=
      PhaseRuntimeState.handle_attempt_eq runtime _ following message phaseHandled
    have rawSame : acceptingBefore.execution.application.attempt = following.attempt := by
      rw [← afterApplication, afterSame, ← same, ← address, rawAttempt]
    have present : (⟨event, action⟩ : graph.Completion) ∈
        acceptingAfter.execution.application.current.native.config.history := by
      rw [afterApplication, normalized]
      exact (PhaseRuntimeState.normalize_semantic_extension
        ({ acceptingBefore.execution.application with
          current := acceptingBefore.execution.application.current.inclusionResult
            message.payload.packet.call native } : PhaseRuntimeState graph)
        orderedBefore (by
          simpa only [normalized, PhaseRuntimeState.attempt] using rawSame)).2.subset
          installed
    have atClosing := (phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
      acceptingAfter before acceptedTrace prior toClosing orderedAfter afterSame).2.subset present
    exact (phaseClosingEffect_history_prefix runtime leaks before.execution ending.execution raw
      effect).subset atClosing
  · have beforeLength : acceptingTrace.length = prior.length := by
      have upper := afterAccepting.length_le
      simp only [closed, acceptedTrace, Trace.length] at upper earlier
      omega
    have afterLength : acceptedTrace.length = closed.length := by
      simp only [closed, acceptedTrace, Trace.length, beforeLength]
    have beforeHistory := TracePrefix.eq_of_same_length acceptingPrefix
      closingBeforePrefix beforeLength
    have beforeEq : acceptingBefore = before :=
      Option.some.inj (congrArg History.state beforeHistory)
    have afterHistory := afterAccepting.eq_of_length afterLength
    have afterEq : acceptingAfter = ending :=
      Option.some.inj (congrArg History.state afterHistory)
    subst acceptingBefore
    subst acceptingAfter
    rcases effect with included | applied
    · obtain ⟨id, actual, sameNative, lookup, stepped, handled, rfl⟩ := included
      have idEq : id = message.id := ReactiveApplication.Command.include.inj
        ((app).environmentStep_command_unique before.execution ending.execution
          (.include id) (.include message.id) stepped moved)
      subst id
      have messageEq : actual = message := Option.some.inj (lookup.symm.trans found)
      subst actual
      have nativeEq : sameNative = native := Option.some.inj
        (handled.symm.trans nativeHandled)
      subst sameNative
      exact installed
    · obtain ⟨command, _native, stepped, _nativeMoved, _rawEq⟩ := applied
      have impossible := (app).environmentStep_command_unique before.execution ending.execution
        (.application command) (.include message.id) stepped moved
      cases impossible

/-- At the actual first original phase exit, a counted opening's TRUE
physical receipt is exactly its recorded TRUE action in the original drained
image. Failed guard results and every primitive closing witness are retained. -/
theorem original_opening_receipt_iff_recorded (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (start before ending : (app).Control)
    (startTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some start))
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (joint : Player → Option (app).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal (some before) joint)
    (realized : some ending ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) joint).support)
    (fromStart : TracePrefix startTrace prior)
    (same : start.execution.application.attempt = before.execution.application.attempt)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ ending.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (value : Raw L)
    (call : message.payload.packet.call = .opening event candidate value)
    (address : message.payload.attempt = start.execution.application.attempt)
    (absent : (message.id, true) ∉ start.execution.receipts)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (inside : event ∈ phase.events) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (ordered : graph.RevealRelaxedOrdered)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt) :
    ((message.id, true) ∈ ending.execution.receipts ↔
      ∃ action : (graph.outputLayout event).Action,
        ⟨event, action⟩ ∈ (phase.drain raw).native.config.history ∧
          PhaseProposal.publicationDiscloses (graph.outputLayout event) action = true) := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let closed := prior.extend joint legal realized
  constructor
  · intro received
    obtain ⟨action, recorded, disclosed⟩ := original_opening_receipt_recorded runtime leaks bounds
      plan inputs horizon scheduler start before ending startTrace prior joint legal realized
        fromStart same raw effect message input event candidate value call address absent received
    exact ⟨action, (phase.drain_history_prefix raw).subset recorded, disclosed⟩
  · rintro ⟨action, recorded, disclosed⟩
    have selected : cast (congrArg EventField.Action publication) action = true :=
      (PhaseProposal.publicationDiscloses_cast publication action).trans disclosed
    obtain ⟨original, otherCandidate, otherValue, originalInput, originalAddress, originalCall,
      originalReceipt⟩ := closing_disclosure_has_receipt runtime leaks bounds plan ordered inputs
        horizon scheduler before prior ending.execution raw changed effect phase installed event
          inside payload publication action recorded selected
    have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
      initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) closed
    have firstAllowed := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 original originalInput)
    have secondAllowed := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
    have firstOwner := countCallCorrect_owned_event _ (PhaseCount.nativeMessage original)
      firstAllowed.2.1 (by
        change original.payload.packet.call.event? graph = some event
        rw [originalCall]; rfl)
    have secondOwner := countCallCorrect_owned_event _ (PhaseCount.nativeMessage message)
      secondAllowed.2.1 (by
        change message.payload.packet.call.event? graph = some event
        rw [call]; rfl)
    have rawClosed := menu.toRawTrace initial horizon scheduler closed
    have identified : original = message := PhaseCount.Permits.eq_of_same_event firstAllowed
      secondAllowed originalInput input
      (fun first firstInput second secondInput ids =>
        (app).input_identifier_injective_history initial horizon scheduler ending rawClosed
          first second firstInput secondInput ids)
      (Option.some.inj (firstOwner.symm.trans secondOwner)) (by
        change (original.payload.packet.call.event? graph).map
            (fun event => (⟨original.payload.attempt, event⟩ : CommitAttemptEvent graph)) =
          (message.payload.packet.call.event? graph).map
            (fun event => (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph))
        rw [originalCall, call]
        simp only [Payload.event?, Option.map_some, originalAddress, address, same])
    simpa only [identified] using originalReceipt

/-- The SAME selected canonical replay step reads the original physical TRUE
receipt bit exactly. This consumes exact native Bool retention; semantic guard
success is not used to infer disclosure. -/
theorem original_opening_receipt_iff_canonical_disclosure (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (start before ending : (app).Control)
    (startTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some start))
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (physicalJoint : Player → Option (app).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal
        (some before) physicalJoint)
    (realized : some ending ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) physicalJoint).support)
    (fromStart : TracePrefix startTrace prior)
    (same : start.execution.application.attempt = before.execution.application.attempt)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ ending.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (value : Raw L)
    (call : message.payload.packet.call = .opening event candidate value)
    (address : message.payload.attempt = start.execution.application.attempt)
    (absent : (message.id, true) ∉ start.execution.receipts)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (inside : event ∈ phase.events) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (ordered : graph.RevealRelaxedOrdered)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (offset : Nat)
    (first last : SourceProgram.ProtocolState program × Finset Player)
    (step : NativePublicSourceStep (phase.drain raw).native offset program first last)
    (owner : Player) (acting : SourceProgram.ProtocolState.actor program first.1 = some owner)
    (active : owner ∉ first.2)
    (rank : event.val = offset + (SourceProgram.instructionCount program -
      SourceProgram.ProtocolState.remaining program first.1)) :
    ∃ joint,
      last ∈ (SourceProgram.ProtocolState.recoveryStep program first.1 first.2 joint).support ∧
      NativeDisclosureReadback (phase.drain raw).native offset program first.1 first.2 joint ∧
      ((message.id, true) ∈ ending.execution.receipts ↔
        SourceProgram.OwnAction.disclosure ((joint owner).map (·.action)) = true) := by
  obtain ⟨joint, reached, readback⟩ := step.2.2.2
  obtain ⟨actual, actualPayload, actualPublication, action, actualRank, recorded, selected⟩ :=
    readback owner acting active
  have eventEq : actual = event := Fin.ext (actualRank.trans rank.symm)
  subst actual
  have disclosed : PhaseProposal.publicationDiscloses (graph.outputLayout event) action =
      SourceProgram.OwnAction.disclosure ((joint owner).map (·.action)) :=
    (PhaseProposal.publicationDiscloses_cast actualPublication action).symm.trans selected
  have receipt := original_opening_receipt_iff_recorded runtime leaks bounds plan inputs horizon
    scheduler start before ending startTrace prior physicalJoint legal realized fromStart same raw
      effect
      message input event candidate value call address absent phase installed inside payload
        publication ordered changed
  refine ⟨joint, reached, readback, ?_⟩
  constructor
  · intro accepted
    obtain ⟨otherAction, otherRecorded, otherDisclosed⟩ := receipt.mp accepted
    have unique : (⟨event, otherAction⟩ : graph.Completion) = ⟨event, action⟩ :=
      List.inj_on_of_nodup_map (phase.drain raw).native.config.history_nodup
        otherRecorded recorded rfl
    cases unique
    exact disclosed.symm.trans otherDisclosed
  · intro chosen
    exact receipt.mpr ⟨action, recorded, disclosed.trans chosen⟩

end Vegas.EventGraphRuntime.ReservedEpoch

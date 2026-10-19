/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochStoppedImage
import Vegas.Game.ReservedEpochCountedSuccessor
import Vegas.Pending.PhaseAcceptedProgress
import Interaction.ReactiveReceiptIdentity
import Vegas.Pending.ReservedEpochReceiptTiming

/-! # Retained binding receipts in paired original attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem prefix_accepting_receipt_boundary (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (start ending : (app).Control)
    (startTrace : (menu.protocol initial horizon scheduler).Trace (some start))
    (endingTrace : (menu.protocol initial horizon scheduler).Trace (some ending))
    (kept : TracePrefix startTrace endingTrace) (id : MessageId Player)
    (absent : (id, true) ∉ start.execution.receipts)
    (received : (id, true) ∈ ending.execution.receipts) :
    ∃ (before after : (app).Control)
      (prior : (menu.protocol initial horizon scheduler).Trace (some before))
      (joint : Player → Option (app).Action)
      (legal : (menu.protocol initial horizon scheduler).Legal (some before) joint)
      (realized : some after ∈ ((app).transition initial horizon scheduler
        (some before) joint).support),
      TracePrefix startTrace prior ∧
      TracePrefix (prior.extend joint legal realized) endingTrace ∧
      (id, true) ∉ before.execution.receipts ∧
      (.include id : (app).Command) ∈ (scheduler before.execution.environmentRecall
        (before.execution.observeEnvironment app)).support ∧
      after.execution ∈ (before.execution.environmentStep app (.include id)).support ∧
      (id, true) ∈ after.execution.receipts := by
  have along : ∀ {state} {target : (menu.protocol initial horizon scheduler).Trace state},
      TracePrefix startTrace target → ∃ current : (app).Control, state = some current ∧
        ((id, true) ∈ current.execution.receipts →
          ∃ (before after : (app).Control)
            (prior : (menu.protocol initial horizon scheduler).Trace (some before))
            (joint : Player → Option (app).Action)
            (legal : (menu.protocol initial horizon scheduler).Legal (some before) joint)
            (realized : some after ∈ ((app).transition initial horizon scheduler
              (some before) joint).support),
            TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) target ∧
            (id, true) ∉ before.execution.receipts ∧
            (.include id : (app).Command) ∈ (scheduler before.execution.environmentRecall
              (before.execution.observeEnvironment app)).support ∧
            after.execution ∈ (before.execution.environmentStep app (.include id)).support ∧
            (id, true) ∈ after.execution.receipts) := by
    intro state target retainedPrefix
    induction retainedPrefix with
    | refl => exact ⟨start, rfl, fun accepted => (absent accepted).elim⟩
    | @extend source target previous retainedPrefix joint legal actual ih =>
        obtain ⟨current, rfl, earlier⟩ := ih
        have moved : target ∈ ((app).transition initial horizon scheduler
            (some current) joint).support := actual
        obtain ⟨next, rfl, _retained⟩ := (app).transition_receipts_prefix initial horizon scheduler
          current target joint moved
        refine ⟨next, rfl, ?_⟩
        intro accepted
        by_cases old : (id, true) ∈ current.execution.receipts
        · obtain ⟨before, after, prior, earlierJoint, earlierLegal, earlierRealized, fromStart,
            toPrevious, absentBefore, chosen, stepped, firstReceipt⟩ := earlier old
          exact ⟨before, after, prior, earlierJoint, earlierLegal, earlierRealized, fromStart,
            .extend toPrevious joint legal actual, absentBefore, chosen, stepped, firstReceipt⟩
        · rcases current with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp moved
              exact (old accepted).elim
          | none =>
              cases remaining with
              | zero =>
                  cases (PMF.mem_support_pure_iff _ _).mp moved
                  exact (old accepted).elim
              | succ remaining =>
                  obtain ⟨command, chosen, dispatched⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
                  obtain ⟨observed, stepped, equal⟩ := PMF.support_map .. ▸ dispatched
                  have same : next = ⟨remaining, command.actor? app, observed⟩ :=
                    (Option.some.inj equal).symm
                  subst next
                  have identity := (app).new_accepting_receipt_command execution observed id
                    old command stepped accepted
                  subst command
                  exact ⟨_, _, previous, joint, legal, actual, retainedPrefix, .refl, old, chosen,
                    stepped, accepted⟩
  obtain ⟨current, stateEq, origin⟩ := along kept
  cases Option.some.inj stateEq
  exact origin received

theorem rejected_binding_not_accepted (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ control.execution.network.inputs)
    (event : (graph).EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (rejected : (message.id, false) ∈ control.execution.receipts) :
    ¬ PhaseService.BindingAccepted runtime leaks ⟨message.payload.attempt, event⟩
      message.sender control.execution := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  intro accepted
  obtain ⟨original, originalInput, originalSender, originalAttempt, originalNamed, received⟩ :=
    accepted
  have same : original = message := PhaseCount.Permits.eq_of_same_event
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 original originalInput))
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)) originalInput input
    (fun first firstInput second secondInput ids =>
      (app).input_identifier_injective_history initial horizon scheduler control raw
        first second firstInput secondInput ids) originalSender (by
          change (original.payload.packet.call.event? graph).map
              (fun event => (⟨original.payload.attempt, event⟩ : CommitAttemptEvent graph)) =
            (message.payload.packet.call.event? graph).map
              (fun event => (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph))
          rw [originalNamed, call]
          simp only [Payload.event?, Option.map_some, originalAttempt])
  rw [same] at received
  exact (app).rejected_identifier_not_accepted initial horizon scheduler control raw
    message.id rejected received

omit [Fintype Player] in
private theorem closing_effect_preserves_accepted
    (before after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before after current)
    (field : graph.Field) (candidate : Handle graph)
    (present : before.application.current.native.accepted field = some candidate) :
    current.native.accepted field = some candidate := by
  rcases effect with included | applied
  · obtain ⟨id, message, native, _found, _stepped, handled, rfl⟩ := included
    exact handle_preserves_accepted runtime before.application.current.native native
      ⟨message.id, message.payload.packet.call⟩ handled field candidate present
  · obtain ⟨command, native, _stepped, moved, rfl⟩ := applied
    change native.accepted field = some candidate
    rwa [(environmentStep_tables runtime _ native command moved).1]

omit [Fintype Player] in
theorem original_snapshot_preserves_accepted (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (acceptedAt before : (app).Control) (after : (app).Execution)
    (acceptedTrace : (menu.protocol initial horizon scheduler).Trace (some acceptedAt))
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (kept : TracePrefix acceptedTrace prior) (ordered : acceptedAt.execution.application.Ordered)
    (same : acceptedAt.execution.application.attempt = before.execution.application.attempt)
    (current : RecoveryState graph) (effect : PhaseClosingEffect runtime leaks
      before.execution after current) (phase : RuntimePhase graph)
    (field : graph.Field) (candidate : Handle graph)
    (present : acceptedAt.execution.application.current.native.accepted field = some candidate) :
    (phase.drain current).native.accepted field = some candidate := by
  rw [(phase.drain_tables current).1]
  exact closing_effect_preserves_accepted runtime leaks before.execution after current effect
    field candidate (phase_prefix_accepted runtime leaks menu initial horizon scheduler
      acceptedAt before acceptedTrace prior kept ordered same field candidate present)

omit [Fintype Player] in
theorem input_mem_prefix (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (final : (menu.protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior final) (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ before.execution.network.inputs) :
    message ∈ after.execution.network.inputs := by
  have rawBefore := menu.toRawTrace initial horizon scheduler prior
  have rawAfter := menu.toRawTrace initial horizon scheduler final
  have recalled := (app).reaches_recall_prefix initial horizon scheduler
    (menu.reaches_raw initial horizon scheduler kept.reachesWithin) before after rfl rfl
      message.sender
  have output : message ∈ (app).outputs (before.execution.recall message.sender) := by
    rw [← (app).history_inputRecall initial horizon scheduler rawBefore message.sender]
    exact List.mem_filter.mpr ⟨input, by simp⟩
  obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
  have atEnd : message ∈ (app).outputs (after.execution.recall message.sender) :=
    List.mem_filterMap.mpr ⟨entry, recalled.subset member, emitted⟩
  rw [← (app).history_inputRecall initial horizon scheduler rawAfter message.sender] at atEnd
  exact (List.mem_filter.mp atEnd).1

omit [Fintype Player] in
/-- Readiness rules out an earlier true receipt of a literal binding
identifier, even when that packet is supplied from a later actual prefix.
Ledger provenance and global identifier uniqueness identify any earlier copy. -/
theorem request_binding_identifier_not_receipted (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (prior : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before))
    (final : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some after)) (kept : TracePrefix prior final)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ after.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (call : message.payload.packet.call = .commitment event candidate)
    (request : before.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩) :
    (message.id, true) ∉ before.execution.receipts := by
  intro received
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawBefore := menu.toRawTrace initial horizon scheduler prior
  have rawAfter := menu.toRawTrace initial horizon scheduler final
  have identifiers := (app).receipt_identifiers_history initial horizon scheduler before rawBefore
  have ledgerId : message.id ∈ before.execution.network.ledger.map Message.id := by
    rw [← identifiers]
    exact List.mem_map.mpr ⟨(message.id, true), received, rfl⟩
  obtain ⟨original, ledger, equalId⟩ := List.mem_map.mp ledgerId
  have originalInput := ((app).retained_envelopes_mem_inputs before.execution
    ((app).history_provenance initial horizon scheduler rawBefore)
    ((app).history_inputRecall initial horizon scheduler rawBefore)).ledger original ledger
  have endInput := input_mem_prefix runtime leaks menu initial horizon scheduler before after
    prior final kept original originalInput
  have equal : original = message := (app).input_identifier_injective_history initial horizon
    scheduler after rawAfter original message endInput input equalId
  have inputBefore : message ∈ before.execution.network.inputs := equal ▸ originalInput
  exact PhaseService.not_bindingAccepted_of_request runtime leaks plan inputs horizon scheduler
    rawBefore ⟨message.payload.attempt, event⟩ message.sender request
      ⟨message, inputBefore, rfl, rfl, by rw [call]; rfl, received⟩

/-- A true binding receipt in the actual closing control identifies its handle
in the ORIGINAL raw image. The literal accepting transition either precedes
that closing primitive or is that same primitive. Normalization is never
inverted, and mere coordinate resolution is not used as acceptance. -/
theorem original_binding_receipt_accepted (bounds : MessageBounds graph)
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
    (candidate : Handle graph) (call : message.payload.packet.call = .commitment event candidate)
    (address : message.payload.attempt = start.execution.application.attempt)
    (absent : (message.id, true) ∉ start.execution.receipts)
    (received : (message.id, true) ∈ ending.execution.receipts) :
    raw.native.accepted (.inr event) = some candidate := by
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
    accepting_include_binding runtime leaks plan inputs horizon scheduler acceptingBefore
      rawAccepting acceptingAfter.execution message acceptingInput event candidate call noReceipt
        moved accepted
  have installed : native.accepted (.inr event) = some candidate := by
    rw [(handle_commitment_tables runtime _ native message.id event candidate nativeHandled).2.1]
    exact Function.update_self _ _ _
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
    obtain ⟨sameNative, handled, normalized, _receipts⟩ :=
      phase_inclusion_snapshot_bindingAccepted runtime leaks plan inputs horizon scheduler
        rawAccepting message.id message found following phaseHandled
    have typedHandle : handle runtime acceptingBefore.execution.application.current.native
        ⟨message.id, .commitment event candidate⟩ = some sameNative := by
      simpa only [call] using handled
    have nativeEq : sameNative = native := Option.some.inj (typedHandle.symm.trans nativeHandled)
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
    have present : acceptingAfter.execution.application.current.native.accepted (.inr event) =
        some candidate := by
      rw [afterApplication, normalized]
      exact PhaseRuntimeState.normalize_preserves_accepted
        ({ acceptingBefore.execution.application with
          current := acceptingBefore.execution.application.current.inclusionResult
            message.payload.packet.call native } : PhaseRuntimeState graph)
        orderedBefore (by simpa only [normalized, PhaseRuntimeState.attempt] using rawSame)
        (.inr event) candidate installed
    have atClosing := phase_prefix_accepted runtime leaks menu initial horizon scheduler
      acceptingAfter before acceptedTrace prior toClosing orderedAfter afterSame
        (.inr event) candidate present
    exact closing_effect_preserves_accepted runtime leaks before.execution ending.execution raw
      effect (.inr event) candidate atClosing
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
      have otherHandled : handle runtime before.execution.application.current.native
          ⟨message.id, .commitment event candidate⟩ = some sameNative := by
        simpa only [call] using handled
      have nativeEq : sameNative = native := Option.some.inj
        (otherHandled.symm.trans nativeHandled)
      subst sameNative
      exact installed
    · obtain ⟨command, _native, stepped, _nativeMoved, _rawEq⟩ := applied
      have impossible := (app).environmentStep_command_unique before.execution ending.execution
        (.application command) (.include message.id) stepped moved
      cases impossible

end Vegas.EventGraphRuntime.ReservedEpoch

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
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

/-- A rejected original packet cannot become an accepting binding in the actual
completed image, even if normalization has already installed a retry. -/
theorem phaseProposalUnflagged_stopped_rejected_binding
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, none, anchor⟩))
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (message : Message Player (CommitAttemptPacket graph))
    (inputMessage : message ∈ anchor.network.inputs) (event : (graph).EventId)
    (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (address : message.payload.attempt = anchor.application.attempt)
    (inside : event ∈ phase.events)
    (rejected : (message.id, false) ∈ anchor.receipts) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      ∃ (ending before : (app).Control)
        (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
        (joint : Player → Option (app).Action)
        (legal : ((menu).protocol initial horizon scheduler).Legal (some before) joint)
        (realized : some ending ∈ ((app).transition initial horizon scheduler
          (some before) joint).support) (raw : RecoveryState graph),
        final.state = some ending ∧ TracePrefix trace prior ∧
          TracePrefix (prior.extend joint legal realized) final.trace ∧
          before.execution.application.attempt = anchor.application.attempt ∧
          PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
          phase.Finished (phase.drain raw) ∧
          raw.native.accepted (.inr event) = none ∧
          message.sender ∈ ending.execution.application.current.excluded ∧
          PhaseProposal.sourceArchive ending.execution.network.inputs =
            PhaseProposal.sourceArchive anchor.network.inputs := by
  classical
  intro initial horizon scheduler players profile stopped final supported
  obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, _idle, _changed,
    fromStart, toFinal, same, _installed, _normalized, effect, finished, valid, coverage,
    excluded, tables, _candidates, archive, receipts, failures, _origins, _record⟩ :=
    phaseProposalUnflagged_stopped_binding_image setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps margin
        capacity remaining anchor trace phase installed commitment final supported
  have kept : TracePrefix trace final.trace :=
    (TracePrefix.extend fromStart joint legal realized).trans toFinal
  have endingTrace : ((menu).protocol initial horizon scheduler).Trace (some ending) :=
    stateEq ▸ final.trace
  have rawStart := (menu).toRawTrace initial horizon scheduler trace
  have rawEnd := (menu).toRawTrace initial horizon scheduler endingTrace
  have recalled := (app).reaches_recall_prefix initial horizon scheduler
    ((menu).reaches_raw initial horizon scheduler kept.reachesWithin)
      ⟨remaining, none, anchor⟩ ending rfl stateEq message.sender
  have beforeOutput : message ∈ (app).outputs (anchor.recall message.sender) := by
    rw [← (app).history_inputRecall initial horizon scheduler rawStart message.sender]
    exact List.mem_filter.mpr ⟨inputMessage, by simp⟩
  obtain ⟨entry, entryBefore, emitted⟩ := List.mem_filterMap.mp beforeOutput
  have finalOutput : message ∈ (app).outputs (ending.execution.recall message.sender) :=
    List.mem_filterMap.mpr ⟨entry, recalled.subset entryBefore, emitted⟩
  rw [← (app).history_inputRecall initial horizon scheduler rawEnd message.sender] at finalOutput
  have finalInput := (List.mem_filter.mp finalOutput).1
  have receiptsKept := (app).reaches_receipts_prefix initial horizon scheduler
    ((menu).reaches_raw initial horizon scheduler kept.reachesWithin)
      ⟨remaining, none, anchor⟩ ending rfl stateEq
  have noReceipt := EventGraphRuntime.ReservedEpoch.rejected_binding_not_accepted runtime leaks
    bounds plan inputs horizon scheduler ending endingTrace message finalInput event candidate call
      (receiptsKept.subset rejected)
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) endingTrace
  have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message finalInput)
  have actor : (graph).actor? event = some message.sender := countCallCorrect_owned_event _
    (PhaseCount.nativeMessage message) permitted.2.1 (by
      change (message.payload.packet.call.event? graph) = some event
      rw [call]; rfl)
  have lower : anchor.application.attempt.phase ≤ event.val := by
    have head := Option.mem_def.mp installed
    simpa only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some] using
      ((phase.mem_events event).mp inside).1
  have missing : raw.native.accepted (.inr event) = none := by
    by_contra present
    obtain ⟨selected, accepted⟩ := Option.ne_none_iff_exists'.mp present
    have acceptedImage : (phase.drain raw).native.accepted (.inr event) = some selected := by
      rwa [tables]
    obtain ⟨payload, binding⟩ := valid.accepted_typed (.inr event) selected acceptedImage
    have owner : selected.1 = message.sender := Option.some.inj
      (((graph).actor?_of_outputLayout_binding binding).symm.trans actor)
    have received := receipts event selected lower acceptedImage
    exact noReceipt (by simpa only [address, owner] using received)
  have ownerExcluded := coverage.covered event message.sender actor
    ((failures event inside).mpr missing)
  rw [excluded] at ownerExcluded
  exact ⟨ending, before, prior, joint, legal, realized, raw, stateEq, fromStart, toFinal, same,
    effect, finished, missing, ownerExcluded, archive⟩

end Vegas

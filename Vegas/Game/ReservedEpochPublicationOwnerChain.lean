/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochOpeningExpiry
import Vegas.Pending.PhaseProposalRetention
import Vegas.Pending.PhaseExclusionOrigin
import Vegas.Game.ReservedEpochStoppedFootprint
import Vegas.Pending.PhaseProposalFailure
import Vegas.Game.ReservedEpochPublicationReceipt

/-! # Actual publication successor chains cannot acquire a fresh service failure -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- A ready actual callback reads the same locked successful binding as any
same-attempt anchor on its actual chronological branch. Both orderings of the
callback and anchor are handled by existing immutable store retention. -/
theorem publication_callback_locked_value (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (anchor callback ending : (app).Control)
    (anchorTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some anchor))
    (callbackTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some callback))
    (endingTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ending))
    (anchorKept : TracePrefix anchorTrace endingTrace)
    (callbackKept : TracePrefix callbackTrace endingTrace)
    (same : anchor.execution.application.attempt = callback.execution.application.attempt)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (ready : callback.execution.application.current.native.config.cut.Ready event)
    (value : L.Val payload)
    (locked : binding.get? anchor.execution.application.current.native.config.store =
      some (.success value)) :
    binding.get? callback.execution.application.current.native.config.store =
      some (.success value) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state member
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  by_cases earlier : anchorTrace.length ≤ callbackTrace.length
  · have kept : TracePrefix anchorTrace callbackTrace :=
      (ReachesWithin.ancestor_comparable (E := menu.protocol initial horizon scheduler)
        (first := ⟨some anchor, anchorTrace⟩) (second := ⟨some callback, callbackTrace⟩)
        (target := ⟨some ending, endingTrace⟩) anchorKept.reachesWithin
        callbackKept.reachesWithin earlier).tracePrefix
    exact PhaseProposal.kept_reference
      (PhaseProposal.same_attempt_prefix_keeps_store runtime leaks menu initial initialized horizon
        scheduler anchor callback anchorTrace callbackTrace kept same) binding (.success value)
          locked
  · have kept : TracePrefix callbackTrace anchorTrace :=
      (ReachesWithin.ancestor_comparable (E := menu.protocol initial horizon scheduler)
        (first := ⟨some callback, callbackTrace⟩) (second := ⟨some anchor, anchorTrace⟩)
        (target := ⟨some ending, endingTrace⟩) callbackKept.reachesWithin
        anchorKept.reachesWithin (by
          change callbackTrace.length ≤ anchorTrace.length
          omega)).tracePrefix
    have read : binding.field ∈ (graph.nodes event).readFields := by
      rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
      exact Finset.mem_insert_self _ _
    obtain ⟨actual, present⟩ := Option.isSome_iff_exists.mp
      (binding.get?_isSome callback.execution.application.current.native.config.store
        (callback.execution.application.current.native.config.read_available ready read))
    have retained := PhaseProposal.kept_reference
      (PhaseProposal.same_attempt_prefix_keeps_store runtime leaks menu initial initialized horizon
        scheduler callback anchor callbackTrace anchorTrace kept same.symm) binding actual present
    have equal : actual = .success value := Option.some.inj (retained.symm.trans locked)
    simpa only [equal] using present


omit [Fintype Player] in
/-- The original first-exclusion transition has exactly its physical cause:
an accepted opening whose semantic publication failed, or a ready expiry.
The literal lookup, handler, primitive command and TRUE receipt are retained. -/
theorem publication_exclusion_cause (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (joint : Player → Option (app).Action)
    (realized : some after ∈ ((app).transition initial horizon scheduler
      (some before) joint).support)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (owner : Player) (active : owner ∉ before.execution.application.current.excluded)
    (excluded : owner ∈ after.execution.application.current.excluded) :
    ∃ event ∈ phase.events,
      before.execution.application.SeedRequest owner
        ⟨before.execution.application.attempt, event⟩ ∧
      ((∃ (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
          (candidate : Handle graph) (value : Raw L) (native : State graph),
        before.execution.network.lookup id = some message ∧
        after.execution ∈ (before.execution.environmentStep app (.include id)).support ∧
        message.payload.packet.call = .opening event candidate value ∧
        handle runtime before.execution.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = some native ∧
        RecoveryState.publicationFailed native event = true ∧
        (message.id, true) ∈ after.execution.receipts) ∨
      ∃ native : State graph,
        after.execution ∈
          (before.execution.environmentStep app (.application (.expire event))).support ∧
        native ∈ (environmentStep runtime before.execution.application.current.native
          (.expire event)).support ∧ event ∈ native.config.cut.completed) := by
  classical
  have environmental : ∃ command : (app).Command,
      after.execution ∈ (before.execution.environmentStep app command).support := by
    rcases before with ⟨remaining, actor, execution⟩
    cases actor with
    | some acting =>
        cases (PMF.mem_support_pure_iff ..).mp realized
        generalize actionEq : (joint acting).getD
          ({ transmission := none } : (app).Action) = action at excluded
        rcases action with ⟨transmission⟩
        cases transmission <;> exact (active excluded).elim
    | none =>
        cases remaining with
        | zero =>
            cases (PMF.mem_support_pure_iff ..).mp realized
            exact (active excluded).elim
        | succ remaining =>
            obtain ⟨command, _selected, supported⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
            obtain ⟨next, moved, same⟩ := PMF.support_map .. ▸ supported
            cases Option.some.inj same
            exact ⟨command, moved⟩
  obtain ⟨command, moved⟩ := environmental
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      have equal := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff ..).mp moved)
      change after.execution.application = before.execution.application at equal
      rw [equal] at excluded
      exact (active excluded).elim
  | activate acting =>
      obtain ⟨updated, supported, same⟩ := PMF.support_map .. ▸ moved
      obtain ⟨sample, _selected, rfl⟩ := PMF.support_map .. ▸ supported
      have equal := congrArg (fun execution : (app).Execution => execution.application) same
      change before.execution.application = after.execution.application at equal
      rw [← equal] at excluded
      exact (active excluded).elim
  | «include» id =>
      have actual := moved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      have equal := (PMF.mem_support_pure_iff ..).mp moved
      have applicationEq := congrArg (fun execution : (app).Execution => execution.application)
        equal
      have receiptsEq := congrArg (fun execution : (app).Execution => execution.receipts) equal
      change after.execution.application =
        (before.execution.includePending app id).application at applicationEq
      change after.execution.receipts =
        (before.execution.includePending app id).receipts at receiptsEq
      rw [applicationEq] at excluded
      cases found : before.execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
            found] at excluded
          exact (active excluded).elim
      | some message =>
          cases handled : before.execution.application.handle runtime message with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
                found, show (app).handle before.execution.application message = none from handled,
                Option.getD_none] at excluded
              exact (active excluded).elim
          | some next =>
              have now : owner ∈ next.current.excluded := by
                simpa only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending,
                  found,
                  show (app).handle before.execution.application message = some next
                    from handled,
                  Option.getD_some] using excluded
              obtain ⟨event, candidate, value, native, inside, request, call, accepted, failed⟩ :=
                before.execution.application.handle_new_exclusion_request runtime next phase
                  installed message handled owner active now
              have addressed : message.id = id := by
                simpa only [decide_eq_true_eq] using List.find?_some found
              have receipt : (message.id, true) ∈
                  (before.execution.includePending app id).receipts := by
                simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
                  found,
                  show (app).handle before.execution.application message = some next
                    from handled,
                  Option.isSome_some, addressed]
                exact List.mem_append_right _ (List.mem_singleton_self _)
              exact ⟨event, inside, request,
                Or.inl ⟨id, message, candidate, value, native, found, actual, call, accepted,
                  failed, receiptsEq ▸ receipt⟩⟩
  | application command =>
      have actual := moved
      obtain ⟨updated, supported, same⟩ := PMF.support_map .. ▸ moved
      obtain ⟨next, reached, rfl⟩ := PMF.support_map .. ▸ supported
      have equal := congrArg (fun execution : (app).Execution => execution.application) same
      change next = after.execution.application at equal
      rw [← equal] at excluded
      obtain ⟨event, native, commandEq, inside, request, nativeMoved, completed, _normalized⟩ :=
        PhaseRuntimeState.environment_new_exclusion_request runtime before.execution.application
          next phase installed command reached owner active excluded
      subst command
      exact ⟨event, inside, request, Or.inr ⟨native, actual, nativeMoved, completed⟩⟩


omit [Fintype Player] in
/-- The actual original drained image contains no failure before an owner's
ready request. Immutable publication values, the literal closing primitive and
its real drain transport the existing counted readiness theorem. -/
theorem publication_request_prior_failures (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (callback closing : (app).Control)
    (callbackTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some callback))
    (closingTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some closing))
    (kept : TracePrefix callbackTrace closingTrace)
    (same : callback.execution.application.attempt = closing.execution.application.attempt)
    (after : (app).Execution) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after raw)
    (phase : RuntimePhase graph) (kind : phase.kind = .reveal)
    (owner : Player) (event : graph.EventId)
    (request : callback.execution.application.SeedRequest owner
      ⟨callback.execution.application.attempt, event⟩)
    (earlier : graph.EventId) (inside : earlier ∈ phase.events)
    (acting : graph.actor? earlier = some owner) (lower : earlier.val < event.val) :
    ¬ (phase.drain raw).native.PublicFailure earlier := by
  obtain ⟨completed, safe⟩ := PhaseProposal.requested_earlier_own_completed_not_failed runtime leaks
    plan
    ordered inputs horizon scheduler callback
      (menu.toRawTrace _ horizon scheduler callbackTrace) owner _ request earlier acting lower
  have initialized : ∀ state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support,
      state.Ordered := by
    intro state member
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have callbackOrdered := (phaseApplication_seedOrder runtime leaks).history _ horizon scheduler
    initialized (menu.toRawTrace _ horizon scheduler callbackTrace)
  have progress := phase_prefix_semantic_extension runtime leaks menu _ horizon scheduler callback
    closing callbackTrace closingTrace kept callbackOrdered same
  have beforeCompleted := completed_subset_of_history_prefix _ _ progress.2 completed
  have bounds := (phase.mem_events earlier).mp inside
  obtain ⟨payload, publication⟩ := kind ▸ phase.fields earlier bounds.1 bounds.2
  have primitive := phaseClosingEffect_publicFailureExtension runtime leaks closing.execution after
    raw effect
  have extension := primitive.trans (phase.drain_publicFailureExtension raw)
  intro failed
  exact safe ((PhaseProposal.publication_failure_kept progress.1 earlier payload publication
    completed).mp ((extension.failures earlier beforeCompleted).mp failed))


omit [Fintype Player] in
private theorem closing_effect_raw_eq (before after : (app).Execution)
    (first second : RecoveryState graph)
    (left : PhaseClosingEffect runtime leaks before after first)
    (right : PhaseClosingEffect runtime leaks before after second)
    (command : (app).Command)
    (moved : after ∈ (before.environmentStep app command).support)
    (strategic : (∃ id, command = .include id) ∨
      ∃ event, command = .application (.expire event)) : first = second := by
  rcases left with included | applied
  · obtain ⟨id, message, native, found, actual, handled, rfl⟩ := included
    rcases right with included | applied
    · obtain ⟨otherId, otherMessage, otherNative, otherFound, otherActual, otherHandled, rfl⟩ :=
        included
      have sameId : id = otherId := ReactiveApplication.Command.include.inj
        ((app).environmentStep_command_unique before after (.include id) (.include otherId)
          actual otherActual)
      subst otherId
      have sameMessage : message = otherMessage := Option.some.inj (found.symm.trans otherFound)
      subst otherMessage
      have sameNative : native = otherNative := Option.some.inj (handled.symm.trans otherHandled)
      subst otherNative
      rfl
    · obtain ⟨otherCommand, _otherNative, otherActual, _nativeMoved, _raw⟩ := applied
      have impossible := (app).environmentStep_command_unique before after (.include id)
        (.application otherCommand) actual otherActual
      cases impossible
  · obtain ⟨firstCommand, firstNative, firstActual, firstMoved, rfl⟩ := applied
    rcases right with included | applied
    · obtain ⟨id, _message, _native, _found, actual, _handled, _raw⟩ := included
      have impossible := (app).environmentStep_command_unique before after
        (.application firstCommand) (.include id) firstActual actual
      cases impossible
    · obtain ⟨secondCommand, secondNative, secondActual, secondMoved, rfl⟩ := applied
      have sameCommand : firstCommand = secondCommand := ReactiveApplication.Command.application.inj
        ((app).environmentStep_command_unique before after (.application firstCommand)
          (.application secondCommand) firstActual secondActual)
      subst secondCommand
      have selected := (app).environmentStep_command_unique before after
        (.application firstCommand) command firstActual moved
      rcases strategic with ⟨id, rfl⟩ | ⟨event, rfl⟩
      · cases selected
      · have isExpiry : firstCommand = .expire event :=
          ReactiveApplication.Command.application.inj selected
        subst firstCommand
        have firstEq := (PMF.mem_support_pure_iff _ _).mp firstMoved
        have secondEq := (PMF.mem_support_pure_iff _ _).mp secondMoved
        have nativeEq : firstNative = secondNative := firstEq.trans secondEq.symm
        rw [nativeEq]


omit [Fintype Player] in
private theorem original_publication_result_kept (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (firstBefore firstAfter closing ending : (app).Control)
    (firstTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some firstBefore))
    (closingTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some closing))
    (firstJoint : Player → Option (app).Action)
    (firstLegal : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Legal (some firstBefore) firstJoint)
    (firstRealized : some firstAfter ∈ ((app).transition
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
        (some firstBefore) firstJoint).support)
    (closingJoint : Player → Option (app).Action)
    (closingLegal : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Legal (some closing) closingJoint)
    (closingRealized : some ending ∈ ((app).transition
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
        (some closing) closingJoint).support)
    (fromFirst : TracePrefix firstTrace closingTrace)
    (toClosing : TracePrefix (firstTrace.extend firstJoint firstLegal firstRealized)
      (closingTrace.extend closingJoint closingLegal closingRealized))
    (same : firstBefore.execution.application.attempt = closing.execution.application.attempt)
    (firstRaw raw : RecoveryState graph)
    (firstEffect : PhaseClosingEffect runtime leaks firstBefore.execution firstAfter.execution
      firstRaw)
    (firstNormalized : firstAfter.execution.application =
      ({ firstBefore.execution.application with current := firstRaw } :
        PhaseRuntimeState graph).normalize)
    (effect : PhaseClosingEffect runtime leaks closing.execution ending.execution raw)
    (command : (app).Command)
    (moved : firstAfter.execution ∈
      (firstBefore.execution.environmentStep app command).support)
    (strategic : (∃ id, command = .include id) ∨
      ∃ event, command = .application (.expire event))
    (phase : RuntimePhase graph) (event : graph.EventId) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (failed : firstRaw.native.PublicFailure event) :
    firstRaw.native.config.history.IsPrefix (phase.drain raw).native.config.history ∧
      (phase.drain raw).native.PublicFailure event := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let acceptedTrace := firstTrace.extend firstJoint firstLegal firstRealized
  let closed := closingTrace.extend closingJoint closingLegal closingRealized
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state member
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have orderedBefore := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized (menu.toRawTrace initial horizon scheduler firstTrace)
  have orderedAfter := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized (menu.toRawTrace initial horizon scheduler acceptedTrace)
  by_cases earlier : acceptedTrace.length ≤ closingTrace.length
  · have afterKept : TracePrefix acceptedTrace closingTrace :=
      (ReachesWithin.ancestor_comparable (E := menu.protocol initial horizon scheduler)
        (first := ⟨some firstAfter, acceptedTrace⟩) (second := ⟨some closing, closingTrace⟩)
        (target := ⟨some ending, closed⟩) toClosing.reachesWithin
        (TracePrefix.extend (E := menu.protocol initial horizon scheduler)
          .refl closingJoint closingLegal closingRealized).reachesWithin earlier).tracePrefix
    have startProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon scheduler firstBefore firstAfter firstTrace acceptedTrace
        (TracePrefix.extend (E := menu.protocol initial horizon scheduler)
          .refl firstJoint firstLegal firstRealized) orderedBefore
    have endProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon scheduler firstAfter closing acceptedTrace closingTrace afterKept orderedAfter
    have afterSame : firstAfter.execution.application.attempt =
        closing.execution.application.attempt := by
      have generation := congrArg CommitAttemptId.generation same
      have rank := congrArg CommitAttemptId.phase same
      cases first : firstBefore.execution.application.attempt
      cases middle : firstAfter.execution.application.attempt
      cases last : closing.execution.application.attempt
      simp only [first, middle, last] at startProgress endProgress generation rank
      congr <;> omega
    have normalized := PhaseRuntimeState.normalize_semantic_extension
      ({ firstBefore.execution.application with current := firstRaw } : PhaseRuntimeState graph)
      orderedBefore (by
        change firstBefore.execution.application.attempt =
          ({ firstBefore.execution.application with current := firstRaw } :
            PhaseRuntimeState graph).normalize.attempt
        rw [← firstNormalized]
        exact same.trans afterSame.symm)
    have progress := phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
      firstAfter closing acceptedTrace closingTrace afterKept orderedAfter afterSame
    have stored : KeepsStore firstRaw.native closing.execution.application.current.native := by
      intro field value present
      apply progress.1 field value
      rw [firstNormalized]
      exact normalized.1 field value present
    have atClosing := (PhaseProposal.publication_failure_kept stored event payload publication
      failed.completed).mpr failed
    have primitive := phaseClosingEffect_publicFailureExtension runtime leaks closing.execution
      ending.execution raw effect
    have normalizedHistory : firstRaw.native.config.history.IsPrefix
        firstAfter.execution.application.current.native.config.history := by
      rw [firstNormalized]
      exact normalized.2
    have originalHistory := (normalizedHistory.trans progress.2).trans
      (phaseClosingEffect_history_prefix runtime leaks closing.execution ending.execution raw
        effect)
    exact ⟨originalHistory.trans (phase.drain_history_prefix raw),
      ((primitive.trans (phase.drain_publicFailureExtension raw)).failures event
        atClosing.completed).mpr atClosing⟩
  · have beforeLength : firstTrace.length = closingTrace.length := by
      have upper := toClosing.length_le
      simp only [acceptedTrace, Trace.length] at upper earlier
      omega
    have afterLength : acceptedTrace.length = closed.length := by
      simp only [acceptedTrace, closed, Trace.length, beforeLength]
    have firstBeforeEq : firstBefore = closing := Option.some.inj (congrArg History.state
      (TracePrefix.eq_of_same_length fromFirst .refl beforeLength))
    have firstAfterEq : firstAfter = ending := Option.some.inj
      (congrArg History.state (toClosing.eq_of_length afterLength))
    subst firstBefore
    subst firstAfter
    have rawEq := closing_effect_raw_eq runtime leaks closing.execution ending.execution firstRaw
      raw firstEffect effect command moved strategic
    subst firstRaw
    exact ⟨phase.drain_history_prefix raw,
      ((phase.drain_publicFailureExtension raw).failures event failed.completed).mpr failed⟩


omit [Fintype Player] in
/-- The actual exclusion cause supplies its raw pre-normalization native
failure and exact command. Accepted openings additionally retain their TRUE
completion and physical receipt, including rejecting guards. -/
theorem publication_exclusion_original_result (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before))
    (joint : Player → Option (app).Action)
    (realized : some after ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) joint).support)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (owner : Player) (active : owner ∉ before.execution.application.current.excluded)
    (excluded : owner ∈ after.execution.application.current.excluded) :
    ∃ (event : graph.EventId) (raw : RecoveryState graph) (command : (app).Command),
      event ∈ phase.events ∧ before.execution.application.SeedRequest owner
        ⟨before.execution.application.attempt, event⟩ ∧
      PhaseClosingEffect runtime leaks before.execution after.execution raw ∧
      after.execution.application =
        ({before.execution.application with current := raw} : PhaseRuntimeState graph).normalize ∧
      raw.native.PublicFailure event ∧
      after.execution ∈ (before.execution.environmentStep app command).support ∧
      ((∃ id, command = .include id ∧ (id, true) ∈ after.execution.receipts ∧
        ∃ action : (graph.outputLayout event).Action,
          ⟨event, action⟩ ∈ raw.native.config.history ∧
          PhaseProposal.publicationDiscloses (graph.outputLayout event) action = true) ∨
      command = .application (.expire event)) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨event, inside, request, cause⟩ := publication_exclusion_cause runtime leaks initial
      horizon
    scheduler before after joint realized phase installed owner active excluded
  rcases cause with ⟨id, message, candidate, value, native, found, moved, call, handled, failed,
      receipt⟩ | ⟨native, moved, nativeMoved, completed⟩
  · have pending := List.mem_of_find?_eq_some found
    have addressed : message.id = id := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    have acceptingMove : after.execution ∈
        (before.execution.environmentStep app (.include message.id)).support := by
      simpa only [addressed] using moved
    have input := ((app).retained_envelopes_mem_inputs before.execution
      ((app).history_provenance initial horizon scheduler rawTrace)
      ((app).history_inputRecall initial horizon scheduler rawTrace)).pending message pending
    have absent := (app).pending_identifier_not_receipted initial horizon scheduler before rawTrace
      message pending true
    obtain ⟨actualNative, following, phaseHandled, nativeHandled⟩ :=
      accepting_include_native runtime leaks plan inputs horizon scheduler before rawTrace
        after.execution message input absent acceptingMove receipt
    have sameNative : actualNative = native := Option.some.inj (nativeHandled.symm.trans handled)
    subst actualNative
    obtain ⟨actualNative, actualHandled, normalized, _receipts, _rawStamp⟩ :=
      phase_inclusion_snapshot_bindingAccepted runtime leaks plan inputs horizon scheduler rawTrace
        id message found following phaseHandled
    have nativeEq : actualNative = native := Option.some.inj (actualHandled.symm.trans handled)
    subst actualNative
    have afterApplication : after.execution.application = following := by
      have actual := moved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at actual
      have equal := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp actual)
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, show (app).handle before.execution.application message = some following
          from phaseHandled, Option.getD_some] using equal
    have typedHandled : handle runtime before.execution.application.current.native
        ⟨message.id, .opening event candidate value⟩ = some native := by
      simpa only [call] using handled
    obtain ⟨ready, action, supported, _clock, _stamp, _owner, _payload, _binding, _checks,
        publication, _code, _node, actionEq⟩ := handle_opening_config_step runtime
      before.execution.application.current.native native message.id event candidate value
        typedHandled
    have recorded : (⟨event, action⟩ : graph.Completion) ∈ native.config.history := by
      rw [before.execution.application.current.native.config.step_history event ready action
        native.config supported]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have disclosed : PhaseProposal.publicationDiscloses (graph.outputLayout event) action =
        true := by
      rw [actionEq]
      exact PhaseProposal.publicationDiscloses_cast publication.symm true
    refine ⟨event, before.execution.application.current.inclusionResult
      message.payload.packet.call native, .include id, inside, request,
        Or.inl ⟨id, message, native, found, moved, handled, rfl⟩, ?_, Or.inr failed, moved,
          Or.inl ⟨id, rfl, ?_, action, recorded, disclosed⟩⟩
    · exact afterApplication.trans normalized
    · simpa only [addressed] using receipt
  · have nativeFailed : native.PublicFailure event :=
      SuffixExclusionRecord.expire_publicFailure runtime before.execution.application.current.native
        native (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
          rawTrace).active event nativeMoved (by
            intro sameConfig
            exact request.2.2.1.1 (sameConfig ▸ completed)) request.2.2.2.1
    have normalized : after.execution.application =
        ({before.execution.application with current :=
          before.execution.application.current.environmentResult (.expire event) native} :
            PhaseRuntimeState graph).normalize := by
      obtain ⟨updated, supported, equal⟩ := PMF.support_map .. ▸ moved
      obtain ⟨next, reached, rfl⟩ := PMF.support_map .. ▸ supported
      have applicationEq := congrArg (fun execution : (app).Execution => execution.application)
        equal
      change next = after.execution.application at applicationEq
      rw [← applicationEq] at excluded ⊢
      obtain ⟨actualEvent, actualNative, commandEq, _inside, _request, actualMoved, _completed,
          normalized⟩ := PhaseRuntimeState.environment_new_exclusion_request runtime
        before.execution.application next phase installed (.expire event) reached owner active
          excluded
      have eventEq : event = actualEvent := EnvironmentCommand.expire.inj commandEq
      subst actualEvent
      have nativeEq : actualNative = native :=
        ((PMF.mem_support_pure_iff _ _).mp actualMoved).trans
          ((PMF.mem_support_pure_iff _ _).mp nativeMoved).symm
      subst actualNative
      exact normalized
    exact ⟨event, before.execution.application.current.environmentResult (.expire event) native,
      .application (.expire event), inside, request,
        Or.inr ⟨.expire event, native, moved, nativeMoved, rfl⟩, normalized, nativeFailed, moved,
          Or.inr rfl⟩


/-- An active owner's first ranked FALSE publication in the original image is
its literal actual expiry at that SAME event. A guard-rejected TRUE opening
cannot be mistaken for this case. All original stopped/primitive witnesses
remain in the result. -/
theorem stopped_false_publication_expiry_origin (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (profile : ∀ who, (menu.information (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).BehavioralPolicy who)
    (start closing ending : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some start))
    (closingTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some closing))
    (closingJoint : Player → Option (app).Action)
    (closingLegal : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Legal (some closing) closingJoint)
    (closingRealized : some ending ∈ ((app).transition
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
        (some closing) closingJoint).support)
    (fromStart : TracePrefix trace closingTrace)
    (same : closing.execution.application.attempt = start.execution.application.attempt)
    (changed : ending.execution.application.attempt ≠ start.execution.application.attempt)
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (kind : phase.kind = .reveal) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution ending.execution raw)
    (coverage : (phase.drain raw).FailureCoverage)
    (excludedEq : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (event : graph.EventId) (inside : event ∈ phase.events) (owner : Player)
    (acting : graph.actor? event = some owner)
    (active : owner ∉ start.execution.application.current.excluded)
    (failed : (phase.drain raw).native.PublicFailure event)
    (scan : owner ∉ (phase.drain raw).native.failureOwnersBefore event.val)
    (action : (graph.outputLayout event).Action)
    (recorded : (⟨event, action⟩ : graph.Completion) ∈ (phase.drain raw).native.config.history)
    (withheld : PhaseProposal.publicationDiscloses (graph.outputLayout event) action = false) :
    let E := menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
    let N := menu.information (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
    let stopped := fun history : E.History => match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ start.execution.application.attempt
    ∀ final ∈ (N.runBehavioralUntil (menu.bounded _ horizon scheduler).wellFoundedHistories
      profile stopped ⟨some start, trace⟩).support,
      final.state = some ending →
      TracePrefix (closingTrace.extend closingJoint closingLegal closingRealized) final.trace →
        ∃ (before after : (app).Control) (prior : E.Trace (some before))
          (joint : Player → Option (app).Action) (legal : E.Legal (some before) joint)
          (realized : some after ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
            horizon scheduler (some before) joint).support) (firstRaw : RecoveryState graph),
          TracePrefix trace prior ∧ TracePrefix (prior.extend joint legal realized) final.trace ∧
          before.execution.application.attempt = start.execution.application.attempt ∧
          phase ∈ before.execution.application.phases.head? ∧
          owner ∈ after.execution.application.current.excluded ∧
          before.execution.application.SeedRequest owner
            ⟨before.execution.application.attempt, event⟩ ∧
          PhaseClosingEffect runtime leaks before.execution after.execution firstRaw ∧
          after.execution.application =
            ({before.execution.application with current := firstRaw} :
              PhaseRuntimeState graph).normalize ∧ firstRaw.native.PublicFailure event ∧
          after.execution ∈ (before.execution.environmentStep app
            (.application (.expire event))).support := by
  classical
  intro E N stopped final supported finalState closedKept
  let closed := closingTrace.extend closingJoint closingLegal closingRealized
  have first := N.runBehavioralUntil_support_first
    (menu.bounded _ horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, trace⟩ final supported
  have closedLength : closed.length = final.trace.length := by
    have upper := closedKept.length_le
    apply Nat.le_antisymm upper
    by_contra later
    exact first ⟨some ending, closed⟩
      (.extend fromStart closingJoint closingLegal closingRealized)
      closedKept (by
        change closed.length < final.trace.length
        exact Nat.lt_of_not_ge later) changed
  have closedEq : (⟨some ending, closed⟩ : E.History) = final :=
    closedKept.eq_of_length closedLength
  have nowExcluded : owner ∈ ending.execution.application.current.excluded :=
    excludedEq ▸ coverage.covered event owner acting failed
  obtain ⟨before, after, prior, joint, legal, realized, _origin, startKept, finalKept,
      beforeSame, phaseInstalled, wasActive, nowExcluded, _inside, _requested⟩ :=
    phase_attempt_stopped_exclusion_origin runtime leaks menu plan inputs horizon scheduler profile
      start trace phase installed owner active final supported ending finalState nowExcluded
  obtain ⟨physical, firstRaw, command, physicalInside, request, firstEffect, normalized,
      firstFailed, moved, cause⟩ :=
    publication_exclusion_original_result runtime leaks menu plan inputs horizon
    scheduler before after prior joint realized phase phaseInstalled owner wasActive nowExcluded
  let afterTrace := prior.extend joint legal realized
  have afterKept : TracePrefix afterTrace closed := by
    change TracePrefix afterTrace (⟨some ending, closed⟩ : E.History).trace
    rw [closedEq]
    exact finalKept
  have priorKept : TracePrefix prior closed :=
    (TracePrefix.extend .refl joint legal realized).trans afterKept
  have priorLength : prior.length ≤ closingTrace.length := by
    have upper := afterKept.length_le
    simp only [afterTrace, closed, Trace.length] at upper
    omega
  have toClosing : TracePrefix prior closingTrace :=
    (ReachesWithin.ancestor_comparable (E := E)
      (first := ⟨some before, prior⟩) (second := ⟨some closing, closingTrace⟩)
      (target := ⟨some ending, closed⟩) priorKept.reachesWithin
      (TracePrefix.extend (E := E) .refl closingJoint closingLegal closingRealized).reachesWithin
        priorLength).tracePrefix
  have strategic : (∃ id, command = .include id) ∨
      ∃ target, command = .application (.expire target) := by
    rcases cause with ⟨id, chosen, _receipt, _action⟩ | expiry
    · exact Or.inl ⟨id, chosen⟩
    · exact Or.inr ⟨physical, expiry⟩
  have bounds := (phase.mem_events physical).mp physicalInside
  obtain ⟨payload, publication⟩ := kind ▸ phase.fields physical bounds.1 bounds.2
  obtain ⟨historyKept, physicalFailed⟩ := original_publication_result_kept runtime leaks menu plan
    inputs horizon scheduler before after closing ending prior closingTrace joint legal realized
      closingJoint closingLegal closingRealized toClosing afterKept (beforeSame.trans same.symm)
        firstRaw raw firstEffect normalized effect command moved strategic phase physical payload
          publication firstFailed
  have notBefore : ¬ physical.val < event.val := by
    intro lower
    apply scan
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ owner,
      ⟨physical, lower, request.2.2.2.1, physicalFailed⟩⟩
  have notAfter : ¬ event.val < physical.val := by
    intro lower
    exact publication_request_prior_failures runtime leaks menu plan ordered inputs horizon
      scheduler
      before closing prior closingTrace toClosing (beforeSame.trans same.symm) ending.execution raw
        effect phase kind owner physical request event inside acting lower failed
  have equal : physical = event := Fin.ext (by omega)
  subst physical
  rcases cause with ⟨id, _chosen, _receipt, trueAction, trueRecorded, disclosed⟩ | expiry
  · have unique : (⟨event, action⟩ : graph.Completion) = ⟨event, trueAction⟩ :=
      List.inj_on_of_nodup_map (phase.drain raw).native.config.history_nodup recorded
        (historyKept.subset trueRecorded) rfl
    cases unique
    cases withheld.symm.trans disclosed
  · refine ⟨before, after, prior, joint, legal, realized, firstRaw, startKept, finalKept,
      beforeSame, phaseInstalled, nowExcluded, request, firstEffect, normalized, firstFailed, ?_⟩
    simpa only [expiry] using moved

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

/-- A physical publication expiry of a proper locked binding belongs to an
actual old ready request at the anchor, including its remembered WAIT/SEND word.
Every newly enabled successor is excluded from this service failure case;
semantic guard rejection remains possible through a TRUE opening receipt. -/
theorem phaseProposalUnflagged_opening_expiry_old_request
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (anchor dueControl : (app).Control)
    (anchorTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some anchor))
    (dueTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some dueControl))
    (anchorKept : TracePrefix anchorTrace dueTrace)
    (same : anchor.execution.application.attempt = dueControl.execution.application.attempt)
    (owner : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload)
    (locked : binding.get? anchor.execution.application.current.native.config.store =
      some (.success value))
    (request : dueControl.execution.application.SeedRequest owner
      ⟨dueControl.execution.application.attempt, event⟩)
    (entered : Nat)
    (stamp : dueControl.execution.application.current.native.activatedAt event = some entered)
    (due : runtime.deadline event ≤
      dueControl.execution.application.current.native.clock - entered)
    (expired : (app).Execution) (expiryRemaining : Nat)
    (expiry : expired ∈ (dueControl.execution.environmentStep (app)
      (.application (.expire event))).support)
    (expiryTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨expiryRemaining, none, expired⟩))
    (kept : TracePrefix dueTrace expiryTrace)
    (count : Nat)
    (supported : expired ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
        count anchor.execution).support) :
    anchor.execution.application.SeedRequest owner ⟨anchor.execution.application.attempt, event⟩ ∧
      PhaseCount.ResponseRecorded runtime leaks owner
        ⟨anchor.execution.application.attempt, event⟩ (anchor.execution.recall owner) := by
  obtain old | ⟨remaining, execution, prior, entry, priorKept, _member, _viewed,
      requested, _first, unusable, _silent⟩ :=
    phaseProposalUnflagged_opening_expiry_origin setup mode runtime leaks bounds plan coveredValues
      maximal ordered values tape activationGap processingGap gaps margin anchor anchorTrace
        dueControl dueTrace owner event payload binding checks outputEq codeEq node request entered
          stamp due expired expiryRemaining expiry expiryTrace kept count supported
  · have recorded : PhaseCount.ResponseRecorded runtime leaks owner
        ⟨anchor.execution.application.attempt, event⟩ (anchor.execution.recall owner) := by
      simpa only [same] using old
    have orderedAnchor := (phaseApplication_seedOrder runtime leaks).history
      ((inputs).map (PhaseRuntimeState.initial plan)) (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (by
        intro state member
        obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ member
        exact PhaseRuntimeState.initial_ordered plan draw)
      ((menu).toRawTrace _ _ _ anchorTrace)
    have progress := phase_prefix_semantic_extension runtime leaks menu
      ((inputs).map (PhaseRuntimeState.initial plan)) (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      anchor dueControl anchorTrace dueTrace anchorKept orderedAnchor same
    have unfinished : event ∉ anchor.execution.application.current.native.config.cut.completed := by
      intro completed
      exact request.2.2.1.1
        (completed_subset_of_history_prefix _ _ progress.2 completed)
    exact ⟨phase_recorded_unfinished_request runtime leaks menu plan ordered maximal inputs
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        anchor anchorTrace owner event recorded unfinished, recorded⟩
  · have stored := ReservedEpoch.publication_callback_locked_value runtime leaks menu plan inputs
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
          anchor ⟨remaining, some owner, execution⟩ dueControl anchorTrace prior dueTrace anchorKept
            priorKept (same.trans requested.1) event owner payload binding checks outputEq codeEq
              requested.2.2.1 value locked
    exact (unusable ⟨value, stored⟩).elim


/-- In the actual stopped unflagged continuation, the first ranked FALSE row
of an active owner with a proper locked binding is an old ready episode.
Fresh active proper rows therefore have TRUE native disclosure. This includes
the original closing transition and does not assert semantic guard acceptance. -/
theorem phaseProposalUnflagged_stopped_false_opening_old_request
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, anchor⟩))
    (closing ending : (app).Control)
    (closingTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some closing))
    (joint : Player → Option (app).Action)
    (legal : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Legal
        (some closing) joint)
    (realized : some ending ∈ ((app).transition ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        (some closing) joint).support)
    (fromStart : TracePrefix trace closingTrace)
    (same : closing.execution.application.attempt = anchor.application.attempt)
    (changed : ending.execution.application.attempt ≠ anchor.application.attempt)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (kind : phase.kind = .reveal) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution ending.execution raw)
    (coverage : (phase.drain raw).FailureCoverage)
    (excludedEq : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events) (owner : Player)
    (acting : (graph).actor? event = some owner)
    (active : owner ∉ anchor.application.current.excluded)
    (payload : L.Ty) (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload)
    (locked : binding.get? anchor.application.current.native.config.store = some (.success value))
    (failed : (phase.drain raw).native.PublicFailure event)
    (scan : owner ∉ (phase.drain raw).native.failureOwnersBefore event.val)
    (action : ((graph).outputLayout event).Action)
    (recorded : (⟨event, action⟩ : (graph).Completion) ∈ (phase.drain raw).native.config.history)
    (withheld : PhaseProposal.publicationDiscloses ((graph).outputLayout event) action = false) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let ordinary := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let players := ReactiveApplication.anchoredPolicy anchor ordinary
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let E := (menu).protocol initial horizon scheduler
    let N := (menu).information initial horizon scheduler
    let stopped := fun history : E.History => match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (N.runBehavioralUntil ((menu).bounded _ horizon scheduler).wellFoundedHistories
      profile stopped ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      final.state = some ending →
      TracePrefix (closingTrace.extend joint legal realized) final.trace →
        anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩ ∧
          PhaseCount.ResponseRecorded runtime leaks owner ⟨anchor.application.attempt, event⟩
            (anchor.recall owner) := by
  classical
  intro initial horizon scheduler ordinary players profile E N stopped final supported finalState
    closedKept
  obtain ⟨before, after, prior, selected, selectedLegal, selectedRealized, firstRaw, startKept,
      finalKept, beforeSame, phaseInstalled, nowExcluded, request, firstEffect, _normalized,
      firstFailed, applicationStep⟩ :=
    ReservedEpoch.stopped_false_publication_expiry_origin runtime leaks menu plan inputs horizon
      scheduler ordered profile ⟨remaining, none, anchor⟩ closing ending trace closingTrace joint
        legal realized fromStart same changed phase installed kind raw effect coverage excludedEq
          event inside owner acting active failed scan action recorded withheld final
            (by
              convert supported using 1
              congr 2
              funext history
              dsimp only [stopped]
              cases history.state <;> rfl)
            finalState closedKept
  have idle := phase_exclusion_transition_idle runtime leaks initial horizon scheduler before after
    selected selectedRealized owner request.2.2.2.2 nowExcluded (.expire event) applicationStep
  have native : ∃ native : EventGraphRuntime.State graph,
      native ∈ (environmentStep runtime before.execution.application.current.native
        (.expire event)).support ∧ event ∈ native.config.cut.completed := by
    rcases firstEffect with included | applied
    · obtain ⟨id, _message, _native, _found, actual, _handled, _raw⟩ := included
      have impossible := (app).environmentStep_command_unique before.execution after.execution
        (.include id) (.application (.expire event)) actual applicationStep
      cases impossible
    · obtain ⟨command, native, actual, nativeStep, rawEq⟩ := applied
      have commandEq : command = .expire event := ReactiveApplication.Command.application.inj
        ((app).environmentStep_command_unique before.execution after.execution
          (.application command)
          (.application (.expire event)) actual applicationStep)
      subst command
      have completed : event ∈ native.config.cut.completed := by
        simpa only [rawEq, RecoveryState.environmentResult] using firstFailed.completed
      exact ⟨native, nativeStep, completed⟩
  obtain ⟨native, nativeStep, completed⟩ := native
  have rounds := stopped_prefix_roundsSupported menu initial horizon scheduler profile remaining
    anchor trace stopped final supported ⟨some after, prior.extend selected selectedLegal
      selectedRealized⟩ (.extend startKept selected selectedLegal selectedRealized) finalKept
  have decoded : (menu).decodeProfile initial horizon scheduler profile = players := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who (players who)
      ((menu).anchoredPolicy_covered initial horizon scheduler ⟨remaining, none, anchor⟩ trace
        ordinary who (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan
          values who))
  rw [decoded] at rounds
  rcases after with ⟨afterRemaining, afterActor, afterExecution⟩
  change afterActor = none at idle
  subst afterActor
  obtain ⟨count, reached⟩ := rounds
  rw [ReactiveApplication.runRounds_anchoredPolicy] at reached
  obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler ((menu).toRawTrace initial horizon scheduler prior)
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((invariant.active.activated_iff event).mpr
      ⟨request.2.2.1, by simp only [request.2.2.2.1, Option.isSome_some]⟩)
  have due : runtime.deadline event ≤
      before.execution.application.current.native.clock - entered := by
    by_contra early
    rw [environmentStep_expire_of_not_due runtime _ event request.2.2.1 entered stamp early]
      at nativeStep
    cases (PMF.mem_support_pure_iff _ _).mp nativeStep
    exact request.2.2.1.1 completed
  exact phaseProposalUnflagged_opening_expiry_old_request setup mode runtime leaks bounds plan
    coveredValues maximal ordered values tape activationGap processingGap gaps margin
      ⟨remaining, none, anchor⟩ before trace prior startKept beforeSame.symm owner event payload
        binding checks outputEq codeEq node value locked request entered stamp due afterExecution
          afterRemaining applicationStep (prior.extend selected selectedLegal selectedRealized)
            (TracePrefix.extend (E := E) .refl selected selectedLegal selectedRealized)
              count reached

end Vegas

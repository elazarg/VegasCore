module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketForcedInputs
public import Vegas.Game.SourcePrefixPublications

@[expose] public section

/-! # Existence of the intended replay along forced regular histories

A decoded point with a ready event is not terminal
(`Vegas.decodedPoint_not_terminal`), and at a decoded point the source actor is
the actor of the ready event, so the acting joint of a completion is legal in
the intended game as soon as the decoded action is an intended action of that
actor (`Vegas.intendedLegal_of_completion`).

Along a native history ending in a forced state of `who`, the unsettled content
is positive when the history is regular (`Vegas.unsettledContent_pos`), a
completion of another player's event is not failing, since that player would
owe a failure, and its decoded action receives positive mass from the intended
assessment at that player's view of the decoded point
(`Vegas.completion_choice_pos`). So the intended replay of a regular history
ending in a forced state of `who` exists whenever `who`'s own completions along
it decode to intended actions (`Vegas.intendedHistory?_isSome`). Together with
the period invariant this assembles the source weights of forced beliefs from
forcedness of the regular histories of a site and intended own completions
(`Vegas.ForcedBeliefInputs.ofForcedHistories`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source state decoded at a rank inside the program is not terminal. -/
theorem decodeSourcePrefix?_not_terminal {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
      some state →
    count < eventCount program → ¬ ProtocolState.terminal program state
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, state,
      decoded,
      inside => by
      cases program with
      | ret _ => simp [eventCount] at inside
      | sample _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact id
      | commit _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact id
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact id
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, state,
      decoded, inside => by
      cases program with
      | ret _ => cases decoded
      | sample _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_not_terminal count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | commit _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_not_terminal count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_not_terminal count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)

variable {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

/-- At a native configuration with a ready event, the decoded point is the
whole-program decoding at the rank of the ready event. -/
theorem decodedPoint_decode {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) :
    decodeSourcePrefix? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) []
      (Revelations.initial setup.context) (outputRef setup.program) event.val config.store
      (decodeHistory setup.program config.history) config.defaults = some point := by
  unfold decodedPoint at decoded
  split at decoded
  · rename_i ordered
    have atEvent : config.cut.IsPrefix event.val :=
      ⟨event.isLt.le, fun query =>
        setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
    have rank := atEvent.unique ordered.choose_spec
    rw [rank]
    exact decoded
  · cases decoded

/-- **A decoded point with a ready event is not terminal.** -/
theorem decodedPoint_not_terminal {config : (graph setup).Config}
    {event : (graph setup).EventId} (ready : config.cut.Ready event)
    {point : ProtocolState setup.program} (decoded : decodedPoint setup config = some point) :
    ¬ ProtocolState.terminal setup.program point :=
  decodeSourcePrefix?_not_terminal event.val setup.program _ _ _ _ _ _ _ point
    (decodedPoint_decode ready decoded) event.isLt

/-- An intended choice of positive mass at a view whose actor is `actor` is an
intended action of `actor`. -/
theorem intendedAvailable_of_pos (assessment : setup.intendedModel.BehavioralAssessment)
    {actor : Player} {point : ProtocolState setup.program}
    (acting : ProtocolView.actor actor setup.program
      (ProtocolState.observe actor setup.program point) = some actor)
    {choice : Option (OwnAction Player L)}
    (positive : ((assessment.strategy actor (setup.protocolObserve actor (some point))).map
      Subtype.val) choice ≠ 0) :
    ∃ action, choice = some action ∧
      action ∈ ProtocolView.intendedAvailable actor setup.program
        (ProtocolState.observe actor setup.program point) := by
  obtain ⟨picked, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp
    ((PMF.mem_support_iff _ _).mpr positive)
  have offered := picked.2
  rw [same] at offered
  cases choice with
  | none =>
      exact absurd acting offered
  | some action =>
      exact ⟨action, rfl, offered.2⟩

/-- **A completion is a legal intended step** when the decoded action is an
intended action of the event's actor. At a chance event the acting joint gives
nothing to anybody. -/
theorem intendedLegal_of_completion {history : setup.intendedProtocol.History}
    {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (current : history.state = some point)
    {choice : Option (OwnAction Player L)}
    (intended : ∀ actor, (graph setup).actor? event = some actor → ∃ action,
      choice = some action ∧ action ∈ ProtocolView.intendedAvailable actor setup.program
        (ProtocolState.observe actor setup.program point)) :
    setup.intendedProtocol.Legal history.state (actingJoint setup history.state choice) := by
  rw [current]
  refine setup.intendedProtocol.legal_of_legalOption
    (decodedPoint_not_terminal ready decoded) fun player => ?_
  change LegalOption setup.intendedProtocol (some point) player
    (if ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some player then choice else none)
  by_cases acts : ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some player
  · rw [ite_eq_left acts]
    have filtered := (decodedPoint_actor player ready decoded).symm.trans acts
    have owner := (Option.filter_eq_some_iff.mp filtered).1
    obtain ⟨action, rfl, offered⟩ := intended player owner
    exact ⟨acts, offered⟩
  · rw [ite_eq_right acts]
    exact acts

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **Unsettled content is positive along regular histories.** -/
theorem unsettledContent_pos (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state),
    RegularTrace setup timeouts leaks bounds horizon scheduler assessment who trace →
      0 < unsettledContent setup timeouts leaks bounds horizon scheduler assessment who trace
  | _, .start, _ => zero_lt_one
  | _, .extend (source := before) (target := after) prior joint _ _, regular => by
      obtain ⟨regularPrior, regularStep⟩ := regular
      have earlier := unsettledContent_pos assessment who prior regularPrior
      change 0 < unsettledStep setup timeouts leaks assessment who
        (unsettledContent setup timeouts leaks bounds horizon scheduler assessment who prior)
          before joint
        after
      cases before with
      | none => exact earlier
      | some current =>
          cases after with
          | none => exact earlier
          | some next =>
              cases acting : current.actor with
              | some actor =>
                  simp only [unsettledStep, acting]
                  split_ifs with same
                  · exact earlier
                  · exact mul_pos earlier (regularStep actor acting same).2
              | none =>
                  simp only [unsettledStep, acting]
                  split
                  · exact zero_lt_one
                  · exact earlier

/-- **Completions of other players have positive intended mass.** Along a
regular native history whose completion of an event of a player other than
`who` reaches a forced state of `who`, the intended assessment at that
player's view of the decoded point gives the decoded action positive mass. -/
theorem completion_choice_pos (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) {current next : (application setup timeouts leaks).Control}
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some current))
    (joint : Player → Option (application setup timeouts leaks).Action)
    (legal : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Legal (some current)
      joint)
    (realized : some next ∈ ((onePacketProtocol setup timeouts leaks bounds horizon scheduler).step
      (some current) ⟨joint, legal⟩).support)
    (forcedNext : ForcedState setup timeouts leaks who (some next))
    (regular : RegularTrace setup timeouts leaks bounds horizon scheduler assessment who prior)
    (idle : current.actor = none) {event : (graph setup).EventId}
    (ready : current.execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.execution.application.config ∈
      (current.execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor) (other : actor ≠ who) :
    ((assessment.strategy actor (setup.protocolObserve actor
        (decodedPoint setup current.execution.application.config))).map Subtype.val)
      (decodeEventAction setup.program event action) ≠ 0 := by
  change some next ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
    scheduler
    (some current) joint).support at realized
  have forcedCurrent := forcedState_of_transition (timeouts := timeouts) prior joint realized
    forcedNext
  have invariant := periodInvariant (timeouts := timeouts) assessment who prior current rfl
    forcedCurrent
  have positive := unsettledContent_pos (timeouts := timeouts) assessment who prior regular
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) (failureProfile
    setup.program)
    (bounds.onePacketMenu timeouts leaks) horizon scheduler prior current rfl
  have rawPrior := (bounds.onePacketMenu timeouts leaks).toRawTrace
    (initialLaw setup) horizon scheduler prior
  have active := current.execution.application.active_of_ready_owned
    (legalFacts setup leaks horizon scheduler current rawPrior).quiescent ready acts
  have notFailing : ¬ Failing (decodeEventAction setup.program event action) := by
    intro failing
    obtain ⟨point, target, decodedCurrent, decodedNext, reached⟩ :=
      decodedPoint_step residual event ready action _ member
    have owned : eventOwner? setup.program ⟨event.val, event.isLt⟩ = some actor := by
      rw [eventOwner?_eq_actor]
      exact acts
    have owes := ProtocolState.owesFailure_of_decode_failing setup.program setup.namesNodup
      event.val _ _ _ _ _ _ _ point event.isLt actor _ target
      (decodedPoint_decode ready decodedCurrent) owned failing reached
    obtain ⟨found, foundDecoded, foundForced⟩ := (forcedState_iff_decodedPoint (timeouts :=
      timeouts) next).mp forcedNext
    rw [decodedNext, Option.some.injEq] at foundDecoded
    subst foundDecoded
    exact (foundForced.2 actor other).2 owes
  rcases transition_idle_cases (timeouts := timeouts) (initialLaw setup) horizon scheduler current
    idle joint realized
      with sameExecution | ⟨command, moved⟩
  · exact (config_ne_of_step member (by rw [sameExecution])).elim
  obtain ⟨value, _output, recorded⟩ :=
    current.execution.application.config.step_completion event ready action _ member
  let record := EventGraph.completion (graph setup) event
    (current.execution.application.config.actualDecision event action) value
  have fresh : record ∉ current.execution.application.config.history := by
    intro present
    exact ready.1 ((current.execution.application.config.history_exact event).mp
      (List.mem_map.mpr ⟨record, present, rfl⟩))
  have present : record ∈ next.execution.application.config.history := by
    rw [recorded]
    exact List.mem_append_right _ (List.mem_singleton_self record)
  have chosen : record.decision.bind (decodeEventAction setup.program record.event) =
      decodeEventAction setup.program event action := by
    change (current.execution.application.config.actualDecision event action).bind _ = _
    rw [current.execution.application.config.actualDecision_of_active event actor acts active,
      Option.bind_some]
    rfl
  obtain ⟨message, onLedger, sender, named, content, owned⟩ := completion_content
    current.execution next.execution command moved record fresh present acts (by
      rw [chosen]
      exact notFailing)
  rw [chosen] at content
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
    horizon scheduler (prior.extend joint legal realized)
  have facts := legalFacts setup leaks horizon scheduler next rawTrace
  have inputsEq := transition_idle_inputs (timeouts := timeouts) (initialLaw setup) horizon
    scheduler current idle joint
    realized
  have present : message ∈ current.execution.network.inputs := by
    rw [← inputsEq]
    obtain ⟨entry, entryPresent, material, _transmission, emitted, _packet⟩ :=
      facts.provenance.ledger message onLedger
    have recalled : message ∈ (application setup timeouts leaks).outputs
        (next.execution.logs message.sender) :=
      List.mem_filterMap.mpr ⟨entry, entryPresent, emitted⟩
    rw [← facts.inputs message.sender] at recalled
    exact (List.mem_filter.mp recalled).1
  rcases invariant.settled event ready actor acts other with ⟨_, nothing⟩ |
      ⟨recorded, recordedPresent, recordedSender, recordedNamed, sent, keep, fixed, eq⟩
  · exact (nothing message present sender named).elim
  · have sameMessage := invariant.unique recorded recordedPresent message
      present
      (recordedSender ▸ other) (recordedSender.trans sender.symm) event recordedNamed named
    subst sameMessage
    rw [eq, ← callContent_keep keep _ fun named' handle call =>
      fixed named' handle call (owned named' handle call), ← content] at positive
    intro zero
    rw [zero, ENNReal.toReal_zero] at positive
    exact lt_irrefl 0 positive

/-- At every actual initialized prefix the decoded source point is intended
for this player, including prefixes reached by automatic completion. -/
def OwnCompletionsIntended (who : Player) :
    ∀ {state}, (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state → Prop
  | _, .start => True
  | _, .extend (target := after) prior _ _ _ =>
      OwnCompletionsIntended who prior ∧
        ∀ control : (application setup timeouts leaks).Control, after = some control →
          ∀ point, decodedPoint setup control.execution.application.config = some point →
            ProtocolState.IntendedFor who setup.program point

/-- The current decoding is intended for the player at an initialized prefix. -/
theorem OwnCompletionsIntended.current {who : Player} {state}
    {trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state}
    (holds : OwnCompletionsIntended (timeouts := timeouts) who trace)
    (control : (application setup timeouts leaks).Control) (initialized : state = some control)
    (point : ProtocolState setup.program)
    (decoded : decodedPoint setup control.execution.application.config = some point) :
    ProtocolState.IntendedFor who setup.program point := by
  cases trace with
  | start => cases initialized
  | extend prior joint legal reached => exact holds.2 control initialized point decoded

omit [Fintype Player] in
theorem extendIntended?_isSome {history : setup.intendedProtocol.History}
    {choice : Option (OwnAction Player L)} {target : setup.ProtocolState}
    (legal : setup.intendedProtocol.Legal history.state (actingJoint setup history.state choice))
    (reached : target ∈ (setup.intendedProtocol.step history.state
      ⟨actingJoint setup history.state choice, legal⟩).support) :
    ∃ next, extendIntended? setup history choice target = some next := by
  unfold extendIntended?
  split
  · exact ⟨_, rfl⟩
  · contradiction

/-- **The intended replay exists along forced regular histories.** Along a
regular native history ending in a forced state of `who` whose own completions
decode to intended actions, the intended replay exists. -/
theorem intendedHistory?_isSome (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state)
    (control : (application setup timeouts leaks).Control), state = some control →
    ForcedState setup timeouts leaks who (some control) →
    RegularTrace setup timeouts leaks bounds horizon scheduler assessment who trace →
    OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon := horizon) (scheduler
      := scheduler)
      who trace →
      ∃ history, intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some history
  | _, .start, _, current, _, _, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, forced, regular, ownIntended => by
      obtain ⟨regularPrior, _⟩ := regular
      obtain ⟨ownPrior, ownStep⟩ := ownIntended
      have recursive := fun next same forcedNext =>
        intendedHistory?_isSome assessment who prior next same forcedNext
          regularPrior ownPrior
      subst current
      have realizedRaw : some control ∈ ((application setup timeouts leaks).transition (initialLaw
        setup)
          horizon scheduler before joint).support := realized
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none (timeouts := timeouts) prior
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup timeouts
              leaks)
              state⟩ : (application setup timeouts leaks).Control)).support at realizedRaw
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realizedRaw
          cases Option.some.inj same
          obtain ⟨initial, initialSupported, rfl⟩ := PMF.support_map .. ▸ supported
          have legalStart : setup.intendedProtocol.Legal setup.intendedProtocol.initHistory.state
              (actingJoint setup setup.intendedProtocol.initHistory.state none) :=
            setup.intendedProtocol.legal_of_legalOption (fun impossible => impossible)
              fun _ impossible => impossible
          have reachedStart : decodedPoint setup (EventGraphRuntime.State.initial
              (graph := graph setup) (setup.eventInputs initial)).config ∈
              (setup.intendedProtocol.step setup.intendedProtocol.initHistory.state
                ⟨_, legalStart⟩).support := by
            rw [decodedPoint_initial]
            change _ ∈ (setup.initialLaw.map fun initial =>
              some (ProtocolState.entry setup.program (Config.initial initial))).support
            exact (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, initialSupported, rfl⟩
          obtain ⟨next, extended⟩ := extendIntended?_isSome legalStart reachedStart
          exact ⟨next, extended⟩
      | some current =>
          have forcedCurrent := forcedState_of_transition (timeouts := timeouts) prior joint
            realizedRaw forced
          obtain ⟨found, foundDecoded, foundForced⟩ :=
            (forcedState_iff_decodedPoint (timeouts := timeouts) control).mp forced
          have sourceActive := ProtocolState.not_excluded_of_intendedFor who setup.program found
            (ownStep control rfl found foundDecoded)
          have active : who ∉ control.execution.application.config.defaulted := by
            change who ∉ control.execution.application.config.defaults.defaulted
            simpa only [ProtocolState.defaulted_eq_defaults, decodedPoint_defaults foundDecoded]
              using sourceActive
          have clear := defaulted_eq_empty_of_decodedForced foundDecoded foundForced active
          have priorClear : current.execution.application.config.defaulted = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro other present
            have later := (reactive_protocol_defaulted_mono timeouts) leaks (initialLaw setup)
              horizon scheduler current control joint realizedRaw present
            rw [clear] at later
            exact Finset.notMem_empty other later
          obtain ⟨previous, previousReplay⟩ := recursive current rfl forcedCurrent
          change ∃ history, (intendedHistory? setup timeouts leaks bounds horizon scheduler
            prior).bind
            (fun history => advanceIntended? setup timeouts leaks history (some current) (some
              control)) =
              some history
          rw [previousReplay, Option.bind_some]
          cases acting : current.actor with
          | some actor =>
              rw [transition_respond (timeouts := timeouts) current acting joint,
                PMF.mem_support_pure_iff]
                at realizedRaw
              cases Option.some.inj realizedRaw
              have kept := ((reactive_respond_application timeouts) leaks current.execution
                actor ((joint actor).getD ⟨none⟩)).1
              refine ⟨previous, ?_⟩
              change (match (current.execution.respond (application setup timeouts leaks) actor
                  ((joint actor).getD ⟨none⟩)).application.config.history.drop
                    current.execution.application.config.history.length with
                | [] => some previous
                | [record] => extendIntended? setup previous
                    (record.decision.bind (decodeEventAction setup.program record.event))
                    (decodedPoint setup (current.execution.respond (application setup timeouts
                      leaks) actor
                      ((joint actor).getD ⟨none⟩)).application.config)
                | _ => none) = some previous
              rw [kept, List.drop_length]
          | none =>
              obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts)
                (failureProfile setup.program)
                (bounds.onePacketMenu timeouts leaks) horizon scheduler prior current rfl
              have previousState : previous.state =
                  decodedPoint setup current.execution.application.config :=
                intendedHistory?_state (timeouts := timeouts) prior previousReplay
              rcases (reactive_protocol_config_eq_or_step_of_clear timeouts) leaks (initialLaw
                setup)
                  horizon scheduler current control joint realizedRaw clear with
                    same | ⟨event, ready, action, member⟩
              · refine ⟨previous, ?_⟩
                change (match control.execution.application.config.history.drop
                    current.execution.application.config.history.length with
                  | [] => some previous
                  | [record] => extendIntended? setup previous
                      (record.decision.bind (decodeEventAction setup.program record.event))
                      (decodedPoint setup control.execution.application.config)
                  | _ => none) = some previous
                rw [same, List.drop_length]
              · obtain ⟨value, _output, recorded⟩ :=
                  current.execution.application.config.step_completion event ready action _ member
                have decodedChoice :
                    (current.execution.application.config.actualDecision event action).bind
                        (decodeEventAction setup.program event) =
                      decodeEventAction setup.program event action := by
                  cases owned : (graph setup).actor? event with
                  | none =>
                      have noChoice := decodeEventAction_owner setup.program event action
                      rw [eventOwner?_eq_actor] at noChoice
                      change (decodeEventAction setup.program event action).map sourceActionOwner =
                        (graph setup).actor? event at noChoice
                      rw [owned] at noChoice
                      have silent := Option.map_eq_none_iff.mp noChoice
                      change ((graph setup).nodes event).actor = none at owned
                      simp only [EventGraph.Config.actualDecision,
                        EventGraph.EventCode.actualDecision,
                        owned, Option.bind_none, silent]
                  | some actor =>
                      have actorActive :
                          actor ∉ current.execution.application.config.defaulted := by
                        rw [priorClear]
                        exact Finset.notMem_empty _
                      rw [current.execution.application.config.actualDecision_of_active event actor
                        owned actorActive action, Option.bind_some]
                change ∃ history, (match control.execution.application.config.history.drop
                    current.execution.application.config.history.length with
                  | [] => some previous
                  | [record] => extendIntended? setup previous
                      (record.decision.bind (decodeEventAction setup.program record.event))
                      (decodedPoint setup control.execution.application.config)
                  | _ => none) = some history
                rw [recorded, List.drop_left]
                change ∃ history, extendIntended? setup previous
                    ((current.execution.application.config.actualDecision event action).bind
                      (decodeEventAction setup.program event))
                    (decodedPoint setup control.execution.application.config) = some history
                rw [decodedChoice]
                obtain ⟨point, target, decodedCurrent, decodedNext, reachedPoint⟩ :=
                  decodedPoint_step residual event ready action _ member
                have currentState : previous.state = some point :=
                  previousState.trans decodedCurrent
                have legalStep := intendedLegal_of_completion (history := previous) ready
                  decodedCurrent currentState
                  (choice := decodeEventAction setup.program event action) fun actor acts => by
                    by_cases own : actor = who
                    · subst actor
                      exact ProtocolState.intendedAvailable_of_decode_intendedFor setup.program
                        event.val _ _ _ _ _ _ _ point event.isLt who action target
                        (decodedPoint_decode ready decodedCurrent)
                        (ownPrior.current current rfl point decodedCurrent)
                        ((eventOwner?_eq_actor setup.program event).trans acts) reachedPoint
                        (ownStep control rfl target decodedNext)
                    · have positive := completion_choice_pos (timeouts := timeouts) assessment who
                        prior joint legal
                        realized forced regularPrior acting ready action member acts own
                      rw [decodedCurrent] at positive
                      exact intendedAvailable_of_pos assessment
                        ((decodedPoint_actor_of_history actor
                          ((bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
                            horizon scheduler prior) ready decodedCurrent).trans acts) positive
                have reachedStep : decodedPoint setup control.execution.application.config ∈
                    (setup.intendedProtocol.step previous.state ⟨_, legalStep⟩).support := by
                  change _ ∈ (setup.protocolStep previous.state (actingJoint setup previous.state
                    (decodeEventAction setup.program event action))).support
                  rw [currentState, protocolStep_actingJoint, decodedNext]
                  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨target, reachedPoint, rfl⟩
                exact extendIntended?_isSome legalStep reachedStep

section Assembly

variable {who : Player}
  {site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup timeouts leaks).PlayerEntry}
  {view : (application setup timeouts leaks).PlayerView}

open Classical in
/-- **Forced-belief inputs from forced regular histories.** At a forced
decision site of `who` whose view shows `who`'s own ready event and whose
projected view is an intended site, under a fully mixed intended assessment at
stage `n`, the replay projection supplies the source weights of
`Vegas.ForcedBeliefInputs` as soon as every regular history of the site ends in
a forced state of `who` and `who`'s own completions along it decode to
intended actions. The common fibers and the honest counterparts remain
inputs. -/
def ForcedBeliefInputs.ofForcedHistories
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup timeouts leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ} {n : ℕ}
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (decision : site.1 = some (past, view)) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (mixed : (sequence n).IsFullyMixed)
    (forcedHistories : ∀ history : (onePacketInformation setup timeouts leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace →
      ForcedState setup timeouts leaks who history.1.state)
    (ownIntended : ∀ history : (onePacketInformation setup timeouts leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who history.1.trace)
    (fiberMass : ℝ)
    (fiber : ∀ point, ∑ history with RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
          projected
          history = point,
      operationalWeight setup timeouts leaks who (steps.mass n)
        (operationalRecord setup timeouts leaks bounds horizon scheduler history.1.trace) =
          fiberMass)
    (counterpart : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory
        who site.1 →
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationHistory who
        site.1)
    (commonWeight : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        (counterpart history).1.trace)
    (irregular_le : ∀ history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
      (sequence n)
        who history.1.trace →
      ((onePacketInformation setup timeouts leaks bounds horizon scheduler).historyReachWeight
          (profiles n) history.1).toReal ≤ scale n ^ 3 * commonWeight history)
    (counterpart_ge : ∀ history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * floors n ^ depth * commonWeight history ≤
        slack * ((onePacketInformation setup timeouts leaks bounds horizon
          scheduler).historyReachWeight
          (profiles n) (counterpart history).1).toReal) :
    ForcedBeliefInputs setup timeouts leaks bounds horizon scheduler sequence profiles steps site
      sourceSite (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n :=
  ForcedBeliefInputs.ofForcedReplay (timeouts := timeouts) forced decision turn projected mixed
    forcedHistories
    (fun history regular => by
      have forcedHistory := forcedHistories history regular
      have own := ownIntended history regular
      obtain ⟨control, stateEq, _⟩ := state_of_decision (timeouts := timeouts) history decision
      exact intendedHistory?_isSome (timeouts := timeouts) (sequence n) who history.1.trace control
        stateEq
        (stateEq ▸ forcedHistory) regular own)
    fiberMass fiber counterpart commonWeight counterpart_regular irregular_le counterpart_ge

end Assembly

end Vegas

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForcedRegular

/-! # No other player's off-turn packet at a forced site

**Public event failures.** An event of a player is publicly failed at a native
state when it is completed with no accepted handle and, if it publishes, the
player's reveal has failed at the decoded point (`Vegas.PublicEventFailure`).
Both are read from the public contract view, and both persist along every
transition (`Vegas.publicEventFailure_transition`).

**Completions.** Every completed event with an actor was completed by a packet
of that actor on the ledger, or is publicly failed
(`Vegas.completedByOwner_of_trace`): a completion without the actor's packet
binds no handle, and at a publication it withholds.

**Submissions.** A one-packet submission names the event at its sender's turn,
or an earlier completed event of the sender for which the sender sent nothing,
by the count verdict's readiness token and first-packet test. Such an event is
publicly failed (`Vegas.submissionsAtTurnOrFailed_of_trace`).

**Forced sites.** At a forced decision input of `who`, every history shares
`who`'s public contract view with a forced history, at which every completed
binding of another player has an accepted handle and no other player's reveal
has failed. So along every history of the input, every submission of another
player names the event at that player's turn
(`Vegas.submittedAtTurn_of_forcedSite`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

variable (setup runtime) in
/-- **A public failure** of an event of `actor` at a native control state: the
event is completed, no handle is accepted for it, and if it publishes, `actor`'s
reveal has failed at the decoded point. -/
def PublicEventFailure (actor : Player) (event : (graph setup).EventId)
    (control : (application setup runtime leaks).Control) : Prop :=
  event ∈ control.execution.application.config.cut.completed ∧
    control.execution.application.accepted (.inr event) = none ∧
    ∀ payload, (graph setup).outputLayout event = .publication payload →
      ∀ point, decodedPoint setup control.execution.application.config = some point →
        ProtocolState.RevealFailed actor setup.program point

/-- **Public failures persist** along every transition. -/
theorem publicEventFailure_transition {actor : Player} {event : (graph setup).EventId}
    {current next : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some current))
    (joint : Player → Option (application setup runtime leaks).Action)
    (realized : some next ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler (some current) joint).support)
    (failure : PublicEventFailure setup runtime actor event current) :
    PublicEventFailure setup runtime actor event next := by
  obtain ⟨completed, vacant, failed⟩ := failure
  refine ⟨completed_transition (runtime := runtime) leaks joint realized completed, ?_,
    fun payload layout point decoded => ?_⟩
  · rcases acceptedKept_transition (runtime := runtime) leaks (initialLaw setup) horizon scheduler
      current next joint
        realized event with same | ⟨ready, _, _⟩
    · rw [same]
      exact vacant
    · exact (ready.1 completed).elim
  · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
      setup.program)
      (bounds.onePacketMenu runtime leaks) horizon scheduler prior current rfl
    rcases transition_configStep (initialLaw setup) horizon scheduler current
      next joint realized
        with same | ⟨stepEvent, ready, action, member⟩
    · rw [same] at decoded
      exact failed payload layout point decoded
    · obtain ⟨before, target, beforeEq, afterEq, reached⟩ :=
        decodedPoint_step residual stepEvent ready action _ member
      rw [afterEq, Option.some.injEq] at decoded
      subst decoded
      exact ProtocolState.revealFailed_step actor setup.program before _ target
        (failed payload layout before beforeEq) reached

omit [Fintype Player] in
private theorem ledger_transition {current next : (application setup runtime leaks).Control}
    (joint : Player → Option (application setup runtime leaks).Action)
    (realized : some next ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler (some current) joint).support) :
    ∀ message ∈ current.execution.network.ledger, message ∈ next.execution.network.ledger := by
  cases acting : current.actor with
  | some actor =>
      rw [transition_respond (runtime := runtime) current acting joint, PMF.mem_support_pure_iff]
        at realized
      cases Option.some.inj realized
      intro message member
      change message ∈ (current.execution.respond (application setup runtime leaks) actor
        ((joint actor).getD ⟨none⟩)).network.ledger
      rw [(application setup runtime leaks).respond_ledger]
      exact member
  | none =>
      rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon scheduler
        current acting joint
          realized with same | ⟨command, moved⟩
      · rw [same]
        exact fun _ member => member
      · exact (environment_ledger_receipts_grow (runtime := runtime) current.execution _ command
          moved).1

variable (setup runtime) in
/-- **Completions by their owners.** Every completed event with an actor was
completed by a packet of that actor on the ledger, or is publicly failed. -/
def CompletedByOwner (control : (application setup runtime leaks).Control) : Prop :=
  ∀ event ∈ control.execution.application.config.cut.completed, ∀ actor,
    (graph setup).actor? event = some actor →
      (∃ message ∈ control.execution.network.ledger, message.sender = actor ∧
        message.payload.call.event? (graph setup) = some event) ∨
      PublicEventFailure setup runtime actor event control

/-- **Completions by their owners along every history.** -/
theorem completedByOwner_of_trace : ∀ {state}
    (_ : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control), state = some control →
    CompletedByOwner setup runtime control
  | _, .start, _, current => by cases current
  | _, .extend (source := before) prior joint _ realized, control, current => by
      have recursive := fun next same => completedByOwner_of_trace prior next
        same
      subst current
      change some control ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
        scheduler before joint).support at realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
              state⟩ : (application setup runtime leaks).Control)).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          have ordered := (SourceResidual.initial setup (failureProfile setup.program)
            initial).checkpoint.ordered
          intro event completed
          exact absurd ((ordered.2 event).mp completed) (Nat.not_lt_zero _)
      | some current =>
          have earlier := recursive current rfl
          intro event completed actor acts
          by_cases before_ : event ∈ current.execution.application.config.cut.completed
          · rcases earlier event before_ actor acts with ⟨message, onLedger, sender, named⟩ |
                failure
            · exact Or.inl ⟨message, ledger_transition (runtime := runtime) joint realized message
                onLedger, sender,
                named⟩
            · exact Or.inr (publicEventFailure_transition (runtime := runtime) prior joint
                realized failure)
          · rcases transition_configStep (initialLaw setup) horizon scheduler
              current control
                joint realized with same | ⟨completedEvent, ready, action, member⟩
            · rw [same] at completed
              exact (before_ completed).elim
            · have which : event = completedEvent := by
                rw [current.execution.application.config.step_cut completedEvent ready action _
                  member, EventOrder.Cut.mem_complete] at completed
                exact completed.resolve_right before_
              subst which
              have idle : current.actor = none := by
                cases acting : current.actor with
                | none => rfl
                | some responder =>
                    exfalso
                    rw [transition_respond (runtime := runtime) current acting joint,
                      PMF.mem_support_pure_iff]
                      at realized
                    cases Option.some.inj realized
                    exact config_ne_of_step member
                      (runtime.reactive_respond_application leaks current.execution
                        responder _).1
              rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon
                scheduler current idle
                  joint realized with sameExecution | ⟨command, moved⟩
              · exact (config_ne_of_step member (by rw [sameExecution])).elim
              rcases completion_cases (runtime := runtime) current.execution control.execution
                command moved ready
                  action member acts with
                ⟨message, onLedger, sender, named, _⟩ | ⟨tables, failing⟩
              · exact Or.inl ⟨message, onLedger, sender, named⟩
              · right
                refine ⟨completed, ?_, fun payload layout point decoded => ?_⟩
                · have vacant : current.execution.application.accepted (.inr event) = none := by
                    by_contra present
                    exact ready.1 (accepted_completed (runtime := runtime) leaks prior current rfl
                      event present)
                  rw [tables]
                  exact vacant
                · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
                    (failureProfile setup.program) (bounds.onePacketMenu runtime leaks)
                    horizon scheduler prior current rfl
                  obtain ⟨before, target, decodedCurrent, decodedNext, reached⟩ :=
                    decodedPoint_step residual event ready action _ member
                  rw [decodedNext, Option.some.injEq] at decoded
                  subst decoded
                  have owned : eventOwner? setup.program ⟨event.val, event.isLt⟩ = some actor := by
                    rw [eventOwner?_eq_actor]
                    exact acts
                  exact ProtocolState.revealFailed_of_decode_failing setup.program event.val _ _ _
                    _ _ _ before event.isLt actor payload _ target
                    (decodedPoint_decode ready decodedCurrent) owned layout failing reached

/-- A one-packet submission names the event at its sender's turn, or a completed
event of the sender for which the sender has no packet on the ledger. -/
private theorem submission_atTurn_or_unsent {remaining : Nat} {who : Player}
    {execution : (application setup runtime leaks).Execution}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (action : (application setup runtime leaks).Action)
    (member : action ∈ bounds.onePacketActions runtime leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who))
    (event : (graph setup).EventId)
    (submitted : runtime.submittedEvent? leaks action = some event) :
    execution.application.publicView.ownTurn? who = some event ∨
      (event ∈ execution.application.config.cut.completed ∧
        (graph setup).actor? event = some who ∧
        ∀ message ∈ execution.network.ledger, message.sender = who →
          message.payload.call.event? (graph setup) ≠ some event) := by
  let app := application setup runtime leaks
  rcases ((bounds.mem_onePacketActions runtime leaks who _ _ action).mp member).2 with
    silent | ⟨material, transmits, permitted⟩
  · unfold EventGraphRuntime.submittedEvent? at submitted
    rw [silent] at submitted
    cases submitted
  have materialNamed : material.call.packet.event? (graph setup) = some event := by
    unfold EventGraphRuntime.submittedEvent? at submitted
    rw [transmits] at submitted
    exact submitted
  obtain ⟨inputRecall, serialRecall, _⟩ := runtime.countRecall_history leaks trace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  set envelope := runtime.localEnvelope leaks who (execution.recall who)
    (execution.observe app who) material with envelopeEq
  obtain ⟨tokenValid, correct, first⟩ := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨named, namedEvent, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp tokenValid
  have sameEvent : named = event := by
    have call : envelope.payload.call = material.call.packet := rfl
    rw [call, materialNamed] at namedEvent
    exact (Option.some.inj namedEvent).symm
  subst sameEvent
  have sender : envelope.sender = who := rfl
  have actor := countCallCorrect_actor _ envelope correct namedEvent
  rw [sender] at actor
  have issued : ∀ predecessor ∈ (graph setup).order.predecessors named,
      predecessor ∈ execution.application.config.cut.completed := by
    have token : execution.application.publicView.tokenFor envelope.payload.call =
        some ⟨named⟩ := tokenEq
    unfold PublicView.tokenFor at token
    rw [namedEvent, Option.bind_some] at token
    obtain ⟨_, complete⟩ := (PublicView.readinessToken?_eq_some_iff _ named ⟨named⟩).mp token
    intro predecessor predecessorMember
    exact (execution.application.config.history_exact predecessor).mp
      (complete predecessor predecessorMember)
  by_cases completed : named ∈ execution.application.config.cut.completed
  · refine Or.inr ⟨completed, actor, fun message onLedger messageSender messageNamed => ?_⟩
    have emitted : message ∈ execution.network.inputs := facts.carried.ledger message onLedger
    have recalled : message ∈ app.outputs (execution.recall who) := by
      rw [← inputRecall who]
      exact List.mem_filter.mpr ⟨emitted, by simp [messageSender]⟩
    have lower : message.id.2 < envelope.id.2 := by
      have bound := facts.serials.inputs message emitted
      change message.id.2 < execution.network.nextSerial message.sender at bound
      rw [messageSender, serialRecall who] at bound
      exact bound
    exact first message ⟨recalled, messageSender.trans sender.symm, lower⟩
      (messageNamed.trans namedEvent.symm)
  · left
    have ready : execution.application.config.cut.Ready named := ⟨completed, issued⟩
    refine PublicView.ownTurn?_of_ownTurn _ who named
      ⟨(execution.application.publicView_eventReady named).mpr ready, actor,
        fun other otherReady _ => ?_⟩
    exact ready_unique (setup := setup) _
      ((execution.application.publicView_eventReady other).mp otherReady) ready

variable (setup runtime) in
/-- **Submissions at turns.** Every submission recalled by a player names the
event at that player's turn when it was made, or an event of the player that is
publicly failed. -/
def SubmissionsAtTurnOrFailed (control : (application setup runtime leaks).Control) : Prop :=
  ∀ player, ∀ entry ∈ control.execution.recall player, ∀ event,
    runtime.submittedEvent? leaks entry.action = some event →
      entry.beforeView.application.publicView.ownTurn? player = some event ∨
        ((graph setup).actor? event = some player ∧
          PublicEventFailure setup runtime player event control)

/-- **Submissions are at turns along every history**, or name a publicly
failed event of their sender. -/
theorem submissionsAtTurnOrFailed_of_trace : ∀ {state}
    (_ : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control), state = some control →
    SubmissionsAtTurnOrFailed setup runtime control
  | _, .start, _, current => by cases current
  | _, .extend (source := before) prior joint legal realized, control, current => by
      have recursive := fun next same => submissionsAtTurnOrFailed_of_trace
        prior next same
      subst current
      have realizedRaw : some control ∈ ((application setup runtime leaks).transition (initialLaw
        setup)
          horizon scheduler before joint).support := realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
              state⟩ : (application setup runtime leaks).Control)).support at realizedRaw
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realizedRaw
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact fun _ _ member => (List.not_mem_nil member).elim
      | some current =>
          have earlier := recursive current rfl
          have persist : ∀ player event, ((graph setup).actor? event = some player ∧
              PublicEventFailure setup runtime player event current) →
              ((graph setup).actor? event = some player ∧
                PublicEventFailure setup runtime player event control) :=
            fun _ _ failure => ⟨failure.1,
              publicEventFailure_transition (runtime := runtime) prior joint realizedRaw failure.2⟩
          have rawPrior := (bounds.onePacketMenu runtime leaks).toRawTrace
            (initialLaw setup) horizon scheduler prior
          rcases current with ⟨remaining, acting, execution⟩
          cases acting with
          | some responder =>
              have localLegal := legal.2 responder
              cases selected : joint responder with
              | none =>
                  rw [selected] at localLegal
                  exact (localLegal (show (application setup runtime leaks).actor
                    (some ⟨remaining, some responder, execution⟩) = some responder from rfl)).elim
              | some action =>
                  rw [selected] at localLegal
                  have chosen : action ∈ bounds.onePacketActions runtime leaks responder
                      (execution.recall responder)
                      (execution.observe (application setup runtime leaks) responder) :=
                        localLegal.2
                  have responded : some control = some (⟨remaining, none,
                      execution.respond (application setup runtime leaks) responder action⟩ :
                        (application setup runtime leaks).Control) := by
                    change some control ∈ (PMF.pure (some (⟨remaining, none,
                      execution.respond (application setup runtime leaks) responder
                        ((joint responder).getD ⟨none⟩)⟩ :
                          (application setup runtime leaks).Control))).support at realizedRaw
                    rw [selected, Option.getD_some, PMF.mem_support_pure_iff] at realizedRaw
                    exact realizedRaw
                  cases Option.some.inj responded
                  intro player entry entryMember event submitted
                  change entry ∈ (execution.respond (application setup runtime leaks) responder
                    action).recall player at entryMember
                  rw [runtime.respond_recall leaks execution responder player action]
                    at entryMember
                  split at entryMember
                  · rename_i same
                    subst same
                    rcases List.mem_append.mp entryMember with old | new
                    · exact (earlier player entry old event submitted).imp id (persist _ _)
                    · cases List.mem_singleton.mp new
                      rcases submission_atTurn_or_unsent (runtime := runtime) rawPrior action
                        chosen event submitted with
                        turn | ⟨completed, owned, unsent⟩
                      · exact Or.inl turn
                      · refine Or.inr (persist _ _ ⟨owned, ?_⟩)
                        rcases completedByOwner_of_trace (runtime := runtime) prior _ rfl event
                          completed player owned
                          with ⟨message, onLedger, messageSender, messageNamed⟩ | failure
                        · exact (unsent message onLedger messageSender messageNamed).elim
                        · exact failure
                  · exact (earlier player entry entryMember event submitted).imp id (persist _ _)
          | none =>
              intro player entry entryMember event submitted
              rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon scheduler
                  ⟨remaining, none, execution⟩ rfl joint realizedRaw with same | ⟨command, moved⟩
              · rw [same] at entryMember
                exact (earlier player entry entryMember event submitted).imp id (persist _ _)
              · rw [(application setup runtime leaks).environmentStep_recall execution _ command
                  moved]
                  at entryMember
                exact (earlier player entry entryMember event submitted).imp id (persist _ _)

private theorem control_of_infoOf {who : Player}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (native : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    (seen : (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
      native.trace =
      some (past, view)) :
    ∃ control : (application setup runtime leaks).Control, native.state = some control ∧
      control.execution.observe (application setup runtime leaks) who = view := by
  obtain ⟨state, trace⟩ := native
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        exact ⟨control, rfl, (Prod.mk.inj (Option.some.inj seen)).2⟩
      · simp [ReactiveApplication.observe, active] at seen

/-- **No other player's off-turn packet at a forced site.** At a forced
decision input of `who`, along every history of the input, every submission of
another player names the event at that player's turn when it was made. -/
theorem submittedAtTurn_of_forcedSite {who : Player}
    {info : (onePacketInformation setup runtime leaks bounds horizon scheduler).InfoState who}
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler who info)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (decision : info = some (past, view))
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      info)
    {control : (application setup runtime leaks).Control} (current : history.1.state = some control)
    {player : Player} (other : player ≠ who) :
    ∀ entry ∈ control.execution.recall player, ∀ event,
      runtime.submittedEvent? leaks entry.action = some event →
        entry.beforeView.application.publicView.ownTurn? player = some event := by
  subst decision
  obtain ⟨witness, witnessInfo, witnessForced⟩ := forced
  obtain ⟨found, foundState, viewEq⟩ := control_of_infoOf (runtime := runtime) history.1 history.2
  rw [current, Option.some.injEq] at foundState
  subst foundState
  obtain ⟨witnessControl, witnessStateEq, witnessViewEq⟩ := control_of_infoOf (runtime := runtime)
    witness witnessInfo
  obtain ⟨⟨state, trace⟩, _⟩ := history
  change state = some control at current
  subst current
  obtain ⟨witnessState, witnessTrace⟩ := witness
  change witnessState = some witnessControl at witnessStateEq
  subst witnessStateEq
  have witnessRecord := publicRecord_of_forced (runtime := runtime) who witnessTrace
    witnessControl rfl witnessForced
  obtain ⟨witnessPoint, witnessDecoded, witnessForcedPoint⟩ :=
    (forcedState_iff_decodedPoint (runtime := runtime) witnessControl).mp witnessForced
  have sameView : control.execution.observe (application setup runtime leaks) who =
      witnessControl.execution.observe (application setup runtime leaks) who :=
    viewEq.trans witnessViewEq.symm
  have samePublic : control.execution.application.publicView =
      witnessControl.execution.application.publicView :=
    congrArg (fun observed : (application setup runtime leaks).PlayerView =>
      observed.application.publicView) sameView
  have sameAccepted : control.execution.application.accepted =
      witnessControl.execution.application.accepted :=
    congrArg PublicView.accepted samePublic
  have sameOrder : control.execution.application.config.history.map EventGraph.Completion.event =
      witnessControl.execution.application.config.history.map EventGraph.Completion.event :=
    congrArg (fun publicView : PublicView (graph setup) =>
      publicView.observation.completionOrder) samePublic
  have sameSource := (sourceViewOf_eq_decodedPoint (runtime := runtime) who trace).symm.trans
    ((congrArg (sourceViewOf setup runtime leaks who) sameView).trans
      (sourceViewOf_eq_decodedPoint (runtime := runtime) who witnessTrace))
  intro entry entryMember event submitted
  rcases submissionsAtTurnOrFailed_of_trace (runtime := runtime) trace control rfl player entry
    entryMember event
      submitted with turn | ⟨acts, completed, vacant, failed⟩
  · exact turn
  exfalso
  cases nodeView_eq : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      have sameOwner : owner = player :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans acts)
      subst sameOwner
      have witnessCompleted : event ∈ witnessControl.execution.application.config.cut.completed :=
        (witnessControl.execution.application.config.history_exact event).mp (by
          rw [← sameOrder]
          exact (control.execution.application.config.history_exact event).mpr completed)
      apply witnessRecord.1 event owner payload outputEq other witnessCompleted
      rw [← sameAccepted]
      exact vacant
  | resolve owner payload binding checks outputEq codeEq =>
      obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
        setup.program)
        (bounds.onePacketMenu runtime leaks) horizon scheduler trace control rfl
      have decoded := decodedPoint_eq residual
      have revealed := failed payload outputEq _ decoded
      rw [decoded, witnessDecoded] at sameSource
      have observed := Option.some.inj sameSource
      exact (witnessForcedPoint.2 player other).1
        (ProtocolState.RevealFailed.excluded setup.program _
          ((ProtocolState.revealFailed_iff_of_observe_eq player who setup.program _ _
            observed).mp revealed))
  | sample _ _ outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at acts
      cases acts

end Vegas

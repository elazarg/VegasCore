/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForcedRegular
import Vegas.Game.SourceServiceFacts

/-! # Foreign submissions at forced native inputs

A completed owned event has an actual packet by its owner on the ledger or a
publicly defaulted owner. Accepted records, expiry and automatic completion
establish this invariant under the sole native executor. One-packet readiness
credentials then place each recalled submission at its own turn unless its
owner has defaulted. Forced information rules out foreign public default.
-/

noncomputable section
namespace Vegas
open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph
variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

omit [Fintype Player] in
private theorem expired_owner_defaulted
    {remaining : Nat} {before after : (application setup runtime leaks).Execution}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, before⟩))
    (event : (graph setup).EventId) (actor : Player)
    (owned : (graph setup).actor? event = some actor)
    (unfinished : event ∉ before.application.config.cut.completed)
    (completed : event ∈ after.application.config.cut.completed)
    (entered : Nat) (activated : before.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ before.application.clock - entered)
    (reached : after ∈ (before.environmentStep (application setup runtime leaks)
      (.application (.expire event))).support) :
    actor ∈ after.application.config.defaulted := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have nativeTrace := trace
  have initialEq : initialLaw setup = (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := graph setup)) :=
    serviceInitialLaw_eq_inputs (mode := .sequential) setup
  rw [initialEq] at nativeTrace
  have valid : ExclusionEvidence 0 ∅ before.application :=
    ExclusionEvidence.history runtime leaks (setup.initialLaw.map setup.eventInputs)
      horizon scheduler nativeTrace
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
  change state ∈ ((environmentStep runtime before.application (.expire event)).map
    State.drain).support at changed
  obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
  change actor ∈ native.drain.config.defaulted
  change event ∈ native.drain.config.cut.completed at completed
  by_cases ready : before.application.config.cut.Ready event
  · have same : native = before.application.completeFailure event ready := by
      cases node : nodeView (graph setup) event with
      | sample payload law outputEq codeEq =>
          rw [nodeView_sample_actor outputEq codeEq] at owned
          cases owned
      | bind owner payload outputEq codeEq =>
          rw [environmentStep_expire_bind_eq runtime before.application event ready entered
            activated due owner payload outputEq codeEq node, PMF.mem_support_pure_iff] at moved
          simpa only [EventGraphRuntime.State.completeFailure, node] using moved
      | resolve owner payload binding checks outputEq codeEq =>
          rw [environmentStep_expire_resolve_eq runtime before.application event ready entered
            activated due owner payload binding checks outputEq codeEq node,
            PMF.mem_support_pure_iff] at moved
          simpa only [EventGraphRuntime.State.completeFailure, node] using moved
    rw [same, State.drain_defaulted]
    exact ((valid.completeFailure event ready actor owned).defaulted_zero actor).mpr
      ⟨event, owned, State.completeFailure_publicFailure _ valid.receipts event ready owned⟩
  · rw [environmentStep_expire_of_not_ready runtime before.application event ready,
      PMF.mem_support_pure_iff] at moved
    subst native
    rw [before.application.drain_eq_of_clear facts.quiescent] at completed
    exact (unfinished completed).elim


omit [Fintype Player] in
private theorem ledger_transition {current next : (application setup runtime leaks).Control}
    (joint : Player → Option (application setup runtime leaks).Action)
    (realized : some next ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler (some current) joint).support) :
    ∀ message ∈ current.execution.network.ledger, message ∈ next.execution.network.ledger := by
  let app := application setup runtime leaks
  cases acting : current.actor with
  | some actor =>
      rw [transition_respond (runtime := runtime) current acting joint, PMF.mem_support_pure_iff]
        at realized
      cases Option.some.inj realized
      intro message member
      rw [app.respond_ledger]
      exact member
  | none =>
      rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon scheduler
        current acting joint realized with same | ⟨command, moved⟩
      · rw [same]; exact fun _ member => member
      · apply app.environmentStep_cases current.execution next.execution command moved
          (predicate := fun _ after => current.execution.network.ledger ⊆ after.network.ledger)
        · exact List.Subset.refl _
        · intros; exact List.Subset.refl _
        · intro id
          change current.execution.network.ledger ⊆
            (current.execution.includePending app id).network.ledger
          rw [app.includePending_network]
          cases found : current.execution.network.lookup id with
          | none =>
              simp only [MessageNetwork.includePending, found]
              exact List.Subset.refl _
          | some message =>
              simp only [MessageNetwork.includePending, found]
              exact List.subset_append_left _ _
        · intros; exact List.Subset.refl _

private theorem completed_packet_or_defaulted : ∀ {state}
    (_ : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control), state = some control →
    ∀ event ∈ control.execution.application.config.cut.completed, ∀ actor,
      (graph setup).actor? event = some actor →
      (∃ message ∈ control.execution.network.ledger, message.sender = actor ∧
        message.payload.call.event? (graph setup) = some event) ∨
      actor ∈ control.execution.application.config.defaulted
  | _, .start, _, current => by cases current
  | _, .extend (source := before) prior joint _ realized, control, current => by
      have recursive := fun next same => completed_packet_or_defaulted prior next same
      subst current
      change some control ∈ ((application setup runtime leaks).transition (initialLaw setup)
        horizon scheduler before joint).support at realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
              state⟩ : (application setup runtime leaks).Control)).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          intro event completed
          exact (Finset.notMem_empty event completed).elim
      | some current =>
          intro event completed actor acts
          by_cases earlier : event ∈ current.execution.application.config.cut.completed
          · rcases recursive current rfl event earlier actor acts with
                ⟨message, onLedger, sender, named⟩ | inactive
            · exact Or.inl ⟨message, ledger_transition joint realized message onLedger,
                sender, named⟩
            · exact Or.inr (runtime.reactive_protocol_defaulted_mono leaks (initialLaw setup)
                horizon scheduler current control joint realized inactive)
          · have idle : current.actor = none := by
              cases acting : current.actor with
              | none => rfl
              | some responder =>
                  exfalso
                  rw [transition_respond (runtime := runtime) current acting joint,
                    PMF.mem_support_pure_iff] at realized
                  cases Option.some.inj realized
                  apply earlier
                  simpa only [(runtime.reactive_respond_application leaks current.execution
                    responder _).1] using completed
            rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon
              scheduler current idle joint realized with sameExecution | ⟨command, moved⟩
            · rw [sameExecution] at completed
              exact (earlier completed).elim
            obtain ⟨record, present, eventEq⟩ :=
              List.mem_map.mp ((control.execution.application.config.history_exact event).mpr
                completed)
            have fresh : record ∉ current.execution.application.config.history := by
              intro old
              apply earlier
              rw [← eventEq]
              exact (current.execution.application.config.history_exact record.event).mp
                (List.mem_map_of_mem (f := EventCompletion.event) old)
            subst event
            rcases owned_completion_cases current.execution control.execution command moved
                record fresh present acts with accepted | expired | automatic
            · obtain ⟨accepted⟩ := accepted
              exact Or.inl ⟨accepted.message, accepted.ledger, accepted.sender, accepted.named⟩
            · obtain ⟨commandEq, entered, activated, due, _action, _value, _expired, _recorded⟩ :=
                expired
              right
              have rawPrior := (bounds.onePacketMenu runtime leaks).toRawTrace
                (initialLaw setup) horizon scheduler prior
              have idleTrace : ((application setup runtime leaks).protocol (initialLaw setup)
                  horizon scheduler).Trace
                    (some ⟨current.remaining, none, current.execution⟩) := by
                rcases current with ⟨remaining, actor, execution⟩
                change actor = none at idle
                cases idle
                exact rawPrior
              rw [commandEq] at moved
              exact expired_owner_defaulted idleTrace record.event actor acts earlier completed
                entered activated due moved
            · obtain ⟨native, drained, _, _, _, _, inactive⟩ := automatic
              right
              rw [← drained, State.drain_defaulted]
              exact inactive


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
  have facts := legalFacts setup leaks horizon scheduler ⟨remaining, some who, execution⟩ trace
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
  have actor := correct.actor namedEvent
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
    obtain ⟨entry, recorded, material, _transmission, emitted, _packet⟩ :=
      facts.provenance.ledger message onLedger
    have recalled : message ∈ app.outputs (execution.recall who) := by
      exact List.mem_filterMap.mpr ⟨entry, messageSender ▸ recorded, emitted⟩
    have emitted : message ∈ execution.network.inputs := by
      rw [← inputRecall who] at recalled
      exact (List.mem_filter.mp recalled).1
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
    exact setup.eventGraph.sequentialize_ready_unique _
      ((execution.application.publicView_eventReady other).mp otherReady) ready


private theorem submissions_at_turn_or_defaulted : ∀ {state}
    (_ : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control), state = some control →
    ∀ player, ∀ entry ∈ control.execution.recall player, ∀ event,
      runtime.submittedEvent? leaks entry.action = some event →
        entry.beforeView.application.publicView.ownTurn? player = some event ∨
          player ∈ control.execution.application.config.defaulted
  | _, .start, _, current => by cases current
  | _, .extend (source := before) prior joint legal realized, control, current => by
      have recursive := fun next same => submissions_at_turn_or_defaulted
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
          have persist (player : Player) :
              player ∈ current.execution.application.config.defaulted →
                player ∈ control.execution.application.config.defaulted := by
            intro inactive
            exact runtime.reactive_protocol_defaulted_mono leaks (initialLaw setup) horizon
              scheduler current control joint realizedRaw inactive
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
                    · exact (earlier player entry old event submitted).imp id (persist player)
                    · cases List.mem_singleton.mp new
                      rcases submission_atTurn_or_unsent (runtime := runtime) rawPrior action
                        chosen event submitted with
                        turn | ⟨completed, owned, unsent⟩
                      · exact Or.inl turn
                      · rcases completed_packet_or_defaulted (runtime := runtime) prior _ rfl
                            event completed player owned with
                            ⟨message, onLedger, messageSender, messageNamed⟩ | inactive
                        · exact (unsent message onLedger messageSender messageNamed).elim
                        · exact Or.inr (persist player inactive)
                  · exact (earlier player entry entryMember event submitted).imp id (persist player)
          | none =>
              intro player entry entryMember event submitted
              rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon scheduler
                  ⟨remaining, none, execution⟩ rfl joint realizedRaw with same | ⟨command, moved⟩
              · rw [same] at entryMember
                exact (earlier player entry entryMember event submitted).imp id (persist player)
              · rw [(application setup runtime leaks).environmentStep_recall execution _ command
                  moved]
                  at entryMember
                exact (earlier player entry entryMember event submitted).imp id (persist player)

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
  have witnessRecord := publicRecord_of_forced (runtime := runtime) who witnessControl witnessForced
  have sameView : control.execution.observe (application setup runtime leaks) who =
      witnessControl.execution.observe (application setup runtime leaks) who :=
    viewEq.trans witnessViewEq.symm
  have samePublic : control.execution.application.publicView =
      witnessControl.execution.application.publicView :=
    congrArg (fun observed : (application setup runtime leaks).PlayerView =>
      observed.application.publicView) sameView
  have sameDefaults : control.execution.application.config.defaulted =
      witnessControl.execution.application.config.defaulted :=
    congrArg (fun publicView : PublicView (graph setup) => publicView.observation.defaulted)
      samePublic
  intro entry entryMember event submitted
  rcases submissions_at_turn_or_defaulted trace control rfl player entry entryMember event
      submitted with turn | inactive
  · exact turn
  · exact (witnessRecord player other (sameDefaults ▸ inactive)).elim

end Vegas

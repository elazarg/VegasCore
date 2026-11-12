module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketForcedRegular
public import Vegas.Game.SourceServiceFacts

@[expose] public section

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
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- A one-packet submission names the event at its sender's turn, or a completed
event of the sender for which the sender has no packet on the ledger. -/
private theorem submission_atTurn_or_unsent {remaining : Nat} {who : Player}
    {execution : (application setup timeouts leaks).Execution}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (action : (application setup timeouts leaks).Action)
    (member : action ∈ bounds.onePacketActions timeouts leaks who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who))
    (event : (graph setup).EventId)
    (submitted : (submittedEvent? timeouts) leaks action = some event) :
    execution.application.publicView.ownTurn? who = some event ∨
      (event ∈ execution.application.config.cut.completed ∧
        (graph setup).actor? event = some who ∧
        ∀ message ∈ execution.network.ledger, message.sender = who →
          message.payload.call.event? (graph setup) ≠ some event) := by
  let app := application setup timeouts leaks
  rcases ((bounds.mem_onePacketActions timeouts leaks who _ _ action).mp member).2 with
    silent | ⟨material, transmits, permitted⟩
  · unfold EventGraphRuntime.submittedEvent? at submitted
    rw [silent] at submitted
    cases submitted
  have materialNamed : material.call.packet.event? (graph setup) = some event := by
    unfold EventGraphRuntime.submittedEvent? at submitted
    rw [transmits] at submitted
    exact submitted
  obtain ⟨inputRecall, serialRecall, _⟩ := (countRecall_history timeouts) leaks trace
  have facts := legalFacts setup leaks horizon scheduler ⟨remaining, some who, execution⟩ trace
  set envelope := (localEnvelope timeouts) leaks who (execution.logs who)
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
    have recalled : message ∈ app.outputs (execution.logs who) := by
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
    (_ : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state)
    (control : (application setup timeouts leaks).Control), state = some control →
    ∀ player, ∀ entry ∈ control.execution.logs player, ∀ event,
      (submittedEvent? timeouts) leaks entry.action = some event →
        entry.beforeView.application.publicView.ownTurn? player = some event ∨
          player ∈ control.execution.application.config.defaulted
  | _, .start, _, current => by cases current
  | _, .extend (source := before) prior joint legal realized, control, current => by
      have recursive := fun next same => submissions_at_turn_or_defaulted
        prior next same
      subst current
      have realizedRaw : some control ∈ ((application setup timeouts leaks).transition (initialLaw
        setup)
          horizon scheduler before joint).support := realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup timeouts
              leaks)
              state⟩ : (application setup timeouts leaks).Control)).support at realizedRaw
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
            exact (reactive_protocol_defaulted_mono timeouts) leaks (initialLaw setup) horizon
              scheduler current control joint realizedRaw inactive
          have rawPrior := (bounds.onePacketMenu timeouts leaks).toRawTrace
            (initialLaw setup) horizon scheduler prior
          rcases current with ⟨remaining, acting, execution⟩
          cases acting with
          | some responder =>
              have localLegal := legal.2 responder
              cases selected : joint responder with
              | none =>
                  rw [selected] at localLegal
                  exact (localLegal (show (application setup timeouts leaks).actor
                    (some ⟨remaining, some responder, execution⟩) = some responder from rfl)).elim
              | some action =>
                  rw [selected] at localLegal
                  have chosen : action ∈ bounds.onePacketActions timeouts leaks responder
                      (execution.logs responder)
                      (execution.observe (application setup timeouts leaks) responder) :=
                        localLegal.2
                  have responded : some control = some (⟨remaining, none,
                      execution.respond (application setup timeouts leaks) responder action⟩ :
                        (application setup timeouts leaks).Control) := by
                    change some control ∈ (PMF.pure (some (⟨remaining, none,
                      execution.respond (application setup timeouts leaks) responder
                        ((joint responder).getD ⟨none⟩)⟩ :
                          (application setup timeouts leaks).Control))).support at realizedRaw
                    rw [selected, Option.getD_some, PMF.mem_support_pure_iff] at realizedRaw
                    exact realizedRaw
                  cases Option.some.inj responded
                  intro player entry entryMember event submitted
                  change entry ∈ (execution.respond (application setup timeouts leaks) responder
                    action).logs player at entryMember
                  rw [(respond_recall timeouts) leaks execution responder player action]
                    at entryMember
                  split at entryMember
                  · rename_i same
                    subst same
                    rcases List.mem_append.mp entryMember with old | new
                    · exact (earlier player entry old event submitted).imp id (persist player)
                    · cases List.mem_singleton.mp new
                      rcases submission_atTurn_or_unsent (timeouts := timeouts) rawPrior action
                        chosen event submitted with
                        turn | ⟨completed, owned, unsent⟩
                      · exact Or.inl turn
                      · rcases completed_packet_or_defaulted (timeouts := timeouts) rawPrior _ rfl
                            event completed player owned with
                            ⟨message, onLedger, messageSender, messageNamed⟩ | ⟨inactive, _⟩
                        · exact (unsent message onLedger messageSender messageNamed).elim
                        · exact Or.inr (persist player inactive)
                  · exact (earlier player entry entryMember event submitted).imp id (persist player)
          | none =>
              intro player entry entryMember event submitted
              rcases transition_idle_cases (timeouts := timeouts) (initialLaw setup) horizon
                scheduler
                  ⟨remaining, none, execution⟩ rfl joint realizedRaw with same | ⟨command, moved⟩
              · rw [same] at entryMember
                exact (earlier player entry entryMember event submitted).imp id (persist player)
              · rw [(application setup timeouts leaks).environmentStep_recall execution _ command
                  moved]
                  at entryMember
                exact (earlier player entry entryMember event submitted).imp id (persist player)

private theorem control_of_infoOf {who : Player}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (native : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).History)
    (seen : (onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf who
      native.trace =
      some (past, view)) :
    ∃ control : (application setup timeouts leaks).Control, native.state = some control ∧
      control.execution.observe (application setup timeouts leaks) who = view := by
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
    {info : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InfoState who}
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who info)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (decision : info = some (past, view))
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who
      info)
    {control : (application setup timeouts leaks).Control} (current : history.1.state = some
      control)
    {player : Player} (other : player ≠ who) :
    ∀ entry ∈ control.execution.logs player, ∀ event,
      (submittedEvent? timeouts) leaks entry.action = some event →
        entry.beforeView.application.publicView.ownTurn? player = some event := by
  subst decision
  obtain ⟨witness, witnessInfo, witnessForced⟩ := forced
  obtain ⟨found, foundState, viewEq⟩ := control_of_infoOf (timeouts := timeouts) history.1 history.2
  rw [current, Option.some.injEq] at foundState
  subst foundState
  obtain ⟨witnessControl, witnessStateEq, witnessViewEq⟩ := control_of_infoOf (timeouts := timeouts)
    witness witnessInfo
  obtain ⟨⟨state, trace⟩, _⟩ := history
  change state = some control at current
  subst current
  obtain ⟨witnessState, witnessTrace⟩ := witness
  change witnessState = some witnessControl at witnessStateEq
  subst witnessStateEq
  have witnessRecord := publicRecord_of_forced (timeouts := timeouts) who witnessControl
    witnessForced
  have sameView : control.execution.observe (application setup timeouts leaks) who =
      witnessControl.execution.observe (application setup timeouts leaks) who :=
    viewEq.trans witnessViewEq.symm
  have samePublic : control.execution.application.publicView =
      witnessControl.execution.application.publicView :=
    congrArg (fun observed : (application setup timeouts leaks).PlayerView =>
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

module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketReplayExists
public import Vegas.Game.OnePacketOwnIntended
public import Vegas.Game.OnePacketHonestForced
public import Vegas.Game.SourceDebtObservation
public import Vegas.Pending.ReactiveServiceConditions

@[expose] public section

/-! # Projected views of debt-free sites are intended decisions

**Owing a failure is a function of the observer's information.** The source
prefix decoder carries the registry and publication status of the program
point it reaches (`Vegas.decodeSourcePrefix?_staticAt`), so whether `who` owes
a failure at the decoded point of a native history is a function of `who`'s
projected view (`Vegas.owesFailure_iff_of_projectView_eq`), and all histories
of one decision input of `who` agree on it (`Vegas.owesFailure_iff_of_infoOf`).

**The intended replay of a debt-free history.** From a point of the intended
game, a completion whose decoded action is not an intended action of its actor
leaves that actor owing a failure
(`Vegas.SourceProgram.ProtocolState.intendedAvailable_of_decode_not_owes`), and
debts persist. So along a native history whose decoded point leaves nobody
owing, every decoded point is intended, every completion decodes to an intended
action, and the intended replay exists
(`Vegas.intendedHistory?_isSome_of_debtFree`). This needs no regularity of the
history.

**Projected decisions.** At a decision input of `who` showing `who`'s own
ready event, with a history in a forced state of `who` at which `who` owes no
failure, the projected view is a decision site of the intended game
(`Vegas.projectedDecision_of_debtFree`, `Vegas.projectedDecision_of_forcedAgent`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A debt-free completion is intended.** At a point of the intended game
decoded after `count` events, stepping with the decoded action of the event of
index `count`, owned by `actor`, to a point at which `actor` owes no failure
means the decoded action is an intended action of `actor`. -/
theorem intendedAvailable_of_decode_not_owes {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player) (state : ProtocolState program)
      (bound : count < eventCount program) (actor : Player)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
          some state →
      Intended program state →
      eventOwner? program ⟨count, bound⟩ = some actor →
      target ∈ (step program state
        (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support →
      ¬ OwesFailure actor program target →
      ∃ act, decodeEventAction program ⟨count, bound⟩ action = some act ∧
        act ∈ ProtocolView.intendedAvailable actor program (observe actor program state) := by
  intro count refs registry revelations outputs store history defaults state bound actor action
    target decoded intended owned reached notOwes
  have before := intendedFor_of_intended actor program state intended
  have after := (intendedFor_step actor program state _ target before reached).resolve_right notOwes
  exact intendedAvailable_of_decode_intendedFor program count refs registry revelations outputs
    store history defaults state bound actor action target decoded before owned reached after

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **Debt-freedom reaches back along native transitions.** If nobody owes a
failure at the decoded point after a native transition of the one-packet game,
nobody owes one at the decoded point before it. -/
theorem debtFree_of_transition {before after : (application setup timeouts leaks).Control}
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some before))
    (joint : Player → Option (application setup timeouts leaks).Action)
    (realized : some after ∈ ((application setup timeouts leaks).transition (initialLaw setup)
      horizon
      scheduler (some before) joint).support)
    (free : ∀ point, decodedPoint setup after.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) :
    ∀ point, decodedPoint setup before.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
  intro point decoded player
  exact notOwes_of_transition prior joint realized (fun found read => free found read player)
    point decoded

/-- **The intended replay exists along debt-free histories.** For a
well-formed setup, along a native history of the one-packet game whose decoded
point leaves nobody owing a failure, the intended replay exists. -/
theorem intendedHistory?_isSome_of_debtFree (wellFormed : setup.WellFormed) : ∀ {state}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state)
    (control : (application setup timeouts leaks).Control), state = some control →
    (∀ point, decodedPoint setup control.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) →
      ∃ history, intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some history
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, free => by
      have recursive := fun next same freeNext =>
        intendedHistory?_isSome_of_debtFree wellFormed prior next same freeNext
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
          exact extendIntended?_isSome legalStart reachedStart
      | some current =>
          have freeCurrent := debtFree_of_transition (timeouts := timeouts) prior joint realizedRaw
            free
          obtain ⟨afterRank, ⟨afterResidual⟩, afterHolds⟩ :=
            decodedState_intended_or_owes (timeouts := timeouts) wellFormed
              (failureProfile setup.program) (bounds.onePacketMenu timeouts leaks)
              horizon scheduler (prior.extend joint legal realized) control rfl
          have intendedAfter : ProtocolState.Intended setup.program
              (afterResidual.lift (ProtocolState.entry afterResidual.program
                afterResidual.source)) := by
            rcases afterHolds _ afterResidual.decode with intended | ⟨player, owed⟩
            · exact intended
            · exact (free _ (decodedPoint_eq afterResidual) player owed).elim
          have clear := defaulted_eq_empty_of_decodedIntended
            (decodedPoint_eq afterResidual) intendedAfter
          have priorClear : current.execution.application.config.defaulted = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro player present
            have later := (reactive_protocol_defaulted_mono timeouts) leaks (initialLaw setup)
              horizon scheduler current control joint realizedRaw present
            rw [clear] at later
            exact Finset.notMem_empty player later
          obtain ⟨previous, previousReplay⟩ :=
            recursive current rfl freeCurrent
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
                        EventGraph.EventCode.actualDecision, owned, Option.bind_none, silent]
                  | some actor =>
                      have active : actor ∉ current.execution.application.config.defaulted := by
                        rw [priorClear]
                        exact Finset.notMem_empty _
                      rw [current.execution.application.config.actualDecision_of_active event actor
                        owned active action, Option.bind_some]
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
                obtain ⟨intendedRank, ⟨intendedResidual⟩, intendedHolds⟩ :=
                  decodedState_intended_or_owes (timeouts := timeouts) wellFormed (failureProfile
                    setup.program)
                    (bounds.onePacketMenu timeouts leaks) horizon scheduler prior current
                    rfl
                have intendedPoint : ProtocolState.Intended setup.program point := by
                  have holds := intendedHolds _ intendedResidual.decode
                  have samePoint := Option.some.inj
                    ((decodedPoint_eq intendedResidual).symm.trans decodedCurrent)
                  subst samePoint
                  rcases holds with intended | ⟨player, owes⟩
                  · exact intended
                  · exact (freeCurrent _ (decodedPoint_eq intendedResidual) player owes).elim
                have legalStep := intendedLegal_of_completion (history := previous) ready
                  decodedCurrent currentState
                  (choice := decodeEventAction setup.program event action) fun actor acts => by
                    have owned : eventOwner? setup.program ⟨event.val, event.isLt⟩ =
                        some actor := by
                      rw [eventOwner?_eq_actor]
                      exact acts
                    exact ProtocolState.intendedAvailable_of_decode_not_owes setup.program
                      event.val _ _ _ _ _ _ _ point event.isLt actor action target
                      (decodedPoint_decode ready decodedCurrent) intendedPoint owned reachedPoint
                      (free target decodedNext actor)
                have reachedStep : decodedPoint setup control.execution.application.config ∈
                    (setup.intendedProtocol.step previous.state ⟨_, legalStep⟩).support := by
                  change _ ∈ (setup.protocolStep previous.state (actingJoint setup previous.state
                    (decodeEventAction setup.program event action))).support
                  rw [currentState, protocolStep_actingJoint, decodedNext]
                  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨target, reachedPoint, rfl⟩
                exact extendIntended?_isSome legalStep reachedStep

/-- **The projected view of a debt-free forced history is an intended
decision.** For a well-formed setup, at a decision input of `who` whose view
shows `who`'s own ready event, a history in a forced state of `who` at whose
decoded point `who` owes no failure makes the projected view a decision site
of the intended game. -/
theorem projectedDecision_of_debtFree (wellFormed : setup.WellFormed) {who : Player}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (native : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who
      (some (past, view)))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (forced : ForcedState setup timeouts leaks who native.1.state)
    (notOwed : ∀ point, nativeDecodedState setup timeouts leaks native.1.state = some point →
      ¬ ProtocolState.OwesFailure who setup.program point) :
    setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who (some (past,
      view))) := by
  obtain ⟨control, stateEq, viewEq⟩ := control_of_infoOf (timeouts := timeouts) native.1 native.2
  rw [stateEq] at forced notOwed
  obtain ⟨point, decoded, forcedPoint⟩ := (forcedState_iff_decodedPoint (timeouts := timeouts)
    control).mp forced
  have free : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
    intro found found_decoded player
    rw [decoded, Option.some.injEq] at found_decoded
    subst found_decoded
    by_cases same : player = who
    · subst same
      exact notOwed point decoded
    · exact (forcedPoint.2 player same).2
  obtain ⟨history, replayed⟩ := intendedHistory?_isSome_of_debtFree (timeouts := timeouts)
    wellFormed native.1.trace
    control stateEq free
  have historyState : history.state = some point :=
    (intendedHistory?_state (timeouts := timeouts) native.1.trace replayed).trans (by
      rw [stateEq]
      exact decoded)
  have seen := intendedHistory?_infoOf (timeouts := timeouts) native.1 native.2 replayed
  subst viewEq
  obtain ⟨publicReady, owned⟩ := PublicView.ownTurn?_spec _ who event turn
  have ready : control.execution.application.config.cut.Ready event :=
    (State.publicView_eventReady _ event).mp publicReady
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
    horizon scheduler native.1.trace
  have atControl : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) := stateEq ▸ rawTrace
  have facts := legalFacts setup leaks horizon scheduler control atControl
  have active := control.execution.application.active_of_ready_owned facts.quiescent ready owned
  have acting : ProtocolView.actor who setup.program
      (ProtocolState.observe who setup.program point) = some who := by
    rw [decodedPoint_actor who ready decoded, owned]
    simp [active]
  obtain ⟨joint, offered⟩ := ProtocolState.intendedProgress setup.program point
  have own := offered who
  cases chosen : joint who with
  | none =>
      rw [chosen] at own
      exact (own acting).elim
  | some action =>
      rw [chosen] at own
      refine ⟨⟨history, seen⟩, ?_, action, ?_⟩
      · change ¬ Option.elim history.state False (ProtocolState.terminal setup.program)
        rw [historyState]
        exact decodedPoint_not_terminal ready decoded
      · rw [← seen]
        change some action ∈ setup.intendedMenu who
          (setup.intendedModel.infoOf who history.trace)
        rw [setup.intended_info, historyState]
        exact own

/-- **Projected decisions at debt-free forced sites.** For a well-formed setup,
at a forced decision input of `who` whose view shows `who`'s own ready event,
if `who` owes no failure at the decoded point of any history of the input, the
projected view is a decision site of the intended game. By
`Vegas.owesFailure_iff_of_infoOf` one history suffices. -/
theorem projectedDecision_of_forcedAgent (wellFormed : setup.WellFormed) {who : Player}
    {info : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InfoState who}
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who info)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : info = some (past, view)) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (notOwed : ∀ history : (onePacketInformation setup timeouts leaks bounds horizon
        scheduler).InformationHistory who info,
      ∀ point, nativeDecodedState setup timeouts leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point) :
    setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who info) := by
  subst decision
  obtain ⟨native, seen, forcedNative⟩ := forced
  exact projectedDecision_of_debtFree (timeouts := timeouts) wellFormed ⟨native, seen⟩ turn
    forcedNative
    (notOwed ⟨native, seen⟩)

end Vegas

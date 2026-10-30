/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketReplayExists
import Vegas.Game.OnePacketHonestForced
import Vegas.Game.SourceDebtObservation
import Vegas.Pending.ReactiveServiceConditions

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
      (state : ProtocolState program) (bound : count < eventCount program) (actor : Player)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      Intended program state →
      eventOwner? program ⟨count, bound⟩ = some actor →
      target ∈ (step program state
        (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support →
      ¬ OwesFailure actor program target →
      ∃ act, decodeEventAction program ⟨count, bound⟩ action = some act ∧
        act ∈ ProtocolView.intendedAvailable actor program (observe actor program state) := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached notOwes
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported notOwes
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached notOwes
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change PublicationResult (L.Val payload) at action
          change ∃ act, some (OwnAction.commit owner name payload action) = some act ∧ _
          change ¬ OwesFailure owner (.commit name owner fresh guard next) (Sum.inr (entry next
            (commitSuccessor name guard ⟨cells, registry, revelations, history⟩
              (OwnAction.binding owner name payload
                (some (OwnAction.commit owner name payload action)))))) at notOwes
          rw [OwnAction.binding_commit] at notOwes
          cases action with
          | failure =>
              exact (notOwes (Or.inr (failedBinding_entry next _
                (Config.failedBinding_commit _ intended.1.unique fresh guard commitNames)))).elim
          | success value =>
              by_cases accepted : guard.predicts (sourceObserve owner cells) value = true
              · exact ⟨_, rfl, value,
                  (mem_intendedValues_self guard _ intended.2.1 value).mpr accepted, rfl⟩
              · exact (notOwes (Or.inl (indebted_entry next _
                  (intended.1.indebted_commit fresh guard value (by simpa using accepted))))).elim
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported notOwes
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached notOwes
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change Bool at action
          change ∃ act, some (OwnAction.reveal owner name action) = some act ∧ _
          cases action with
          | true => exact ⟨_, rfl, rfl⟩
          | false =>
              refine (notOwes (Or.inl (Or.inl ⟨rfl, ?_⟩))).elim
              rw [base_entry]
              exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended.2 owned supported fun owes => notOwes (owes.elim
              (fun indebted => Or.inl (Or.inr indebted)) (fun failed => Or.inr (Or.inr failed)))

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Debt-freedom reaches back along native transitions.** If nobody owes a
failure at the decoded point after a native transition of the one-packet game,
nobody owes one at the decoded point before it. -/
theorem debtFree_of_transition {before after : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some before))
    (joint : Player → Option (application setup runtime leaks).Action)
    (realized : some after ∈ ((application setup runtime leaks).transition (initialLaw setup)
      horizon
      scheduler (some before) joint).support)
    (free : ∀ point, decodedPoint setup after.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) :
    ∀ point, decodedPoint setup before.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
  intro point decoded player owes
  rcases transition_configStep (initialLaw setup) horizon scheduler before
    after joint realized
      with same | ⟨event, ready, action, member⟩
  · exact free point (by rw [same]; exact decoded) player owes
  · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
      setup.program)
      (bounds.onePacketMenu runtime leaks) horizon scheduler prior before rfl
    obtain ⟨current, target, beforeEq, afterEq, supported⟩ :=
      decodedPoint_step residual event ready action _ member
    rw [beforeEq, Option.some.injEq] at decoded
    subst decoded
    exact free target afterEq player (ProtocolState.owesFailure_step player setup.program current
      _ target owes supported)

/-- **The intended replay exists along debt-free histories.** For a
well-formed setup, along a native history of the one-packet game whose decoded
point leaves nobody owing a failure, the intended replay exists. -/
theorem intendedHistory?_isSome_of_debtFree (wellFormed : setup.WellFormed) : ∀ {state}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control), state = some control →
    (∀ point, decodedPoint setup control.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) →
      ∃ history, intendedHistory? setup runtime leaks bounds horizon scheduler trace = some history
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, free => by
      have recursive := fun next same freeNext =>
        intendedHistory?_isSome_of_debtFree wellFormed prior next same freeNext
      subst current
      have realizedRaw : some control ∈ ((application setup runtime leaks).transition (initialLaw
        setup)
          horizon scheduler before joint).support := realized
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none (runtime := runtime) prior
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
              state⟩ : (application setup runtime leaks).Control)).support at realizedRaw
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
          have freeCurrent := debtFree_of_transition (runtime := runtime) prior joint realizedRaw
            free
          obtain ⟨previous, previousReplay⟩ :=
            recursive current rfl freeCurrent
          change ∃ history, (intendedHistory? setup runtime leaks bounds horizon scheduler
            prior).bind
            (fun history => advanceIntended? setup runtime leaks history (some current) (some
              control)) =
              some history
          rw [previousReplay, Option.bind_some]
          cases acting : current.actor with
          | some actor =>
              rw [transition_respond (runtime := runtime) current acting joint,
                PMF.mem_support_pure_iff]
                at realizedRaw
              cases Option.some.inj realizedRaw
              have kept := (runtime.reactive_respond_application leaks current.execution
                actor ((joint actor).getD ⟨none⟩)).1
              refine ⟨previous, ?_⟩
              change (match (current.execution.respond (application setup runtime leaks) actor
                  ((joint actor).getD ⟨none⟩)).application.config.history.drop
                    current.execution.application.config.history.length with
                | [] => some previous
                | [⟨event, action⟩] => extendIntended? setup previous
                    (decodeEventAction setup.program event action)
                    (decodedPoint setup (current.execution.respond (application setup runtime
                      leaks) actor
                      ((joint actor).getD ⟨none⟩)).application.config)
                | _ => none) = some previous
              rw [kept, List.drop_length]
          | none =>
              obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
                (failureProfile setup.program)
                (bounds.onePacketMenu runtime leaks) horizon scheduler prior current rfl
              have previousState : previous.state =
                  decodedPoint setup current.execution.application.config :=
                intendedHistory?_state (runtime := runtime) prior previousReplay
              rcases transition_configStep (initialLaw setup) horizon
                scheduler current control
                  joint realizedRaw with same | ⟨event, ready, action, member⟩
              · refine ⟨previous, ?_⟩
                change (match control.execution.application.config.history.drop
                    current.execution.application.config.history.length with
                  | [] => some previous
                  | [⟨event, action⟩] => extendIntended? setup previous
                      (decodeEventAction setup.program event action)
                      (decodedPoint setup control.execution.application.config)
                  | _ => none) = some previous
                rw [same, List.drop_length]
              · have dropped : control.execution.application.config.history.drop
                    current.execution.application.config.history.length = [⟨event, action⟩] := by
                  rw [EventGraph.Config.step_history _ event ready action _ member,
                    List.drop_left]
                change ∃ history, (match control.execution.application.config.history.drop
                    current.execution.application.config.history.length with
                  | [] => some previous
                  | [⟨event, action⟩] => extendIntended? setup previous
                      (decodeEventAction setup.program event action)
                      (decodedPoint setup control.execution.application.config)
                  | _ => none) = some history
                rw [dropped]
                obtain ⟨point, target, decodedCurrent, decodedNext, reachedPoint⟩ :=
                  decodedPoint_step residual event ready action _ member
                have currentState : previous.state = some point :=
                  previousState.trans decodedCurrent
                obtain ⟨intendedRank, ⟨intendedResidual⟩, intendedHolds⟩ :=
                  decodedState_intended_or_owes (runtime := runtime) wellFormed (failureProfile
                    setup.program)
                    (bounds.onePacketMenu runtime leaks) horizon scheduler prior current
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
                      event.val _ _ _ _ _ _ point event.isLt actor action target
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
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (native : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      (some (past, view)))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (forced : ForcedState setup runtime leaks who native.1.state)
    (notOwed : ∀ point, nativeDecodedState setup runtime leaks native.1.state = some point →
      ¬ ProtocolState.OwesFailure who setup.program point) :
    setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who (some (past,
      view))) := by
  obtain ⟨control, stateEq, viewEq⟩ := control_of_infoOf (runtime := runtime) native.1 native.2
  rw [stateEq] at forced notOwed
  obtain ⟨point, decoded, forcedPoint⟩ := (forcedState_iff_decodedPoint (runtime := runtime)
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
  obtain ⟨history, replayed⟩ := intendedHistory?_isSome_of_debtFree (runtime := runtime)
    wellFormed native.1.trace
    control stateEq free
  have historyState : history.state = some point :=
    (intendedHistory?_state (runtime := runtime) native.1.trace replayed).trans (by
      rw [stateEq]
      exact decoded)
  have seen := intendedHistory?_infoOf (runtime := runtime) native.1 native.2 replayed
  subst viewEq
  obtain ⟨publicReady, owned⟩ := PublicView.ownTurn?_spec _ who event turn
  have ready : control.execution.application.config.cut.Ready event :=
    (State.publicView_eventReady _ event).mp publicReady
  have acting : ProtocolView.actor who setup.program
      (ProtocolState.observe who setup.program point) = some who :=
    (decodedPoint_actor who ready decoded).trans owned
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
    {info : (onePacketInformation setup runtime leaks bounds horizon scheduler).InfoState who}
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler who info)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (decision : info = some (past, view)) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (notOwed : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who info,
      ∀ point, nativeDecodedState setup runtime leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point) :
    setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who info) := by
  subst decision
  obtain ⟨native, seen, forcedNative⟩ := forced
  exact projectedDecision_of_debtFree (runtime := runtime) wellFormed ⟨native, seen⟩ turn
    forcedNative
    (notOwed ⟨native, seen⟩)

end Vegas

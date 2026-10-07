/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceSettledEvidence
import Vegas.Pending.ReactiveSettledCollection
import Vegas.Pending.ReactiveEventStability

/-! # Final rejection of a noncanonical commitment handle

Once a source event is ready, no other event of its owner can complete before
it: an owner has at most one ready event in every dependency mode, and other
completions do not change the owner's binding count. The event's binding
ordinal is therefore fixed at the current binding count. Completing
the event fixes the final record's count before it, and subsequent completions
only append to the record. These facts hold under arbitrary player responses
and scheduler commands, including acceptance of the wrong handle.

A bare commitment with a different handle consequently fails the actual
settled content check at every complete continuation. Authentic final-record
coverage supplies collection without inspecting private binding material.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph
  GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

private def bindingOrdinal (event : (serviceGraph setup mode).EventId) (who : Player) (serial : Nat)
    (state : EventGraphRuntime.State (serviceGraph setup mode)) : Prop :=
  (state.config.cut.Ready event ∧ state.publicView.bindingCount who = serial) ∨
    (event ∈ state.config.cut.completed ∧
      state.publicView.bindingCountBefore who event = serial)

private theorem bindingOrdinal_step
    {before after : EventGraphRuntime.State (serviceGraph setup mode)}
    (step : ContractStep before after) (event : (serviceGraph setup mode).EventId) (who : Player)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (serial : Nat) (held : bindingOrdinal event who serial before) :
    bindingOrdinal event who serial after := by
  rcases held with ⟨ready, counted⟩ | ⟨completed, counted⟩
  · rcases step with ⟨configEq, _⟩ | ⟨other, otherReady, action, supported⟩
    · left
      refine ⟨configEq ▸ ready, ?_⟩
      have observationEq : after.publicView.observation = before.publicView.observation := by
        change (serviceGraph setup mode).publicObserve after.config =
            (serviceGraph setup mode).publicObserve before.config
        rw [configEq]
      rw [PublicView.bindingCount_eq_countP, observationEq,
        ← PublicView.bindingCount_eq_countP]
      exact counted
    · by_cases same : other = event
      swap
      · left
        have extended : after.publicView.observation.completionOrder =
            before.publicView.observation.completionOrder ++ [other] := by
          change after.config.history.map Completion.event =
            before.config.history.map Completion.event ++ [other]
          rw [before.config.step_history other otherReady action after.config supported]
          simp
        refine ⟨?_, ?_⟩
        · rw [before.config.step_cut other otherReady action after.config supported]
          exact ready.after_complete otherReady (Ne.symm same)
        · have foreign : bindingOwnedBy (serviceGraph setup mode) who other = false := by
            unfold bindingOwnedBy
            cases layout : (serviceGraph setup mode).outputLayout other with
            | binding owner payload =>
                apply decide_eq_false
                rintro rfl
                exact same ((serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
                  before.config.cut ready otherReady owned
                  (actor?_of_outputLayout_binding _ layout))
            | publicData _ | privateInput _ _ | publication _ => rfl
          rw [PublicView.bindingCount_eq_countP, extended, List.countP_append,
            ← PublicView.bindingCount_eq_countP]
          simp [foreign, counted]
      subst other
      right
      refine ⟨?_, ?_⟩
      · rw [before.config.step_cut event otherReady action after.config supported]
        exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
      · have absent : event ∉ before.publicView.observation.completionOrder :=
          fun member => ready.1 ((before.config.history_exact event).mp member)
        have extended : after.publicView.observation.completionOrder =
            before.publicView.observation.completionOrder ++ event :: [] := by
          change after.config.history.map Completion.event =
            before.config.history.map Completion.event ++ [event]
          rw [before.config.step_history event otherReady action after.config supported]
          simp
        rw [PublicView.bindingCountBefore_complete before.publicView after.publicView who
          event absent [] extended]
        exact counted
  · right
    refine ⟨step.completed_mono completed, ?_⟩
    obtain ⟨rest, extended⟩ := step.order_extends
    have member : event ∈ before.publicView.observation.completionOrder :=
      (before.config.history_exact event).mpr completed
    rw [PublicView.bindingCountBefore_append before.publicView after.publicView who event
      member rest extended]
    exact counted

private theorem bindingOrdinal_respond
    (execution : (serviceApplication setup mode deadline leaks).Execution) (responder : Player)
    (response : (serviceApplication setup mode deadline leaks).Action) (event :
        (serviceGraph setup mode).EventId)
    (who : Player) (serial : Nat) (held : bindingOrdinal event who serial execution.application) :
    bindingOrdinal event who serial
      (execution.respond
          (serviceApplication setup mode deadline leaks) responder response).application := by
  obtain ⟨configEq, publicEq⟩ :=
    (serviceRuntime setup mode deadline).reactive_respond_application leaks execution responder
        response
  rcases held with ⟨ready, counted⟩ | ⟨completed, counted⟩
  · exact Or.inl ⟨configEq ▸ ready, by rw [publicEq]; exact counted⟩
  · exact Or.inr ⟨configEq ▸ completed, by rw [publicEq]; exact counted⟩

private def ordinalAtState (event : (serviceGraph setup mode).EventId) (who : Player)
    (serial : Nat) :
    (serviceApplication setup mode deadline leaks).ProtocolState → Prop
  | none => False
  | some control => bindingOrdinal event who serial control.execution.application

private theorem ordinalAtState_transition
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (event : (serviceGraph setup mode).EventId) (who : Player)
    (owned : (serviceGraph setup mode).actor? event = some who) (serial : Nat)
    (before after : (serviceApplication setup mode deadline leaks).ProtocolState)
    (joint : Player → Option (serviceApplication setup mode deadline leaks).Action)
    (held : ordinalAtState event who serial before)
    (reached : after ∈ ((serviceApplication setup mode deadline leaks).transition
        (serviceInitialLaw setup mode) horizon
      scheduler before joint).support) : ordinalAtState event who serial after := by
  cases before with
  | none => exact held.elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some responder =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact bindingOrdinal_respond execution responder _ event who serial held
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact held
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              exact bindingOrdinal_step
                (contractStep_environment
                    (serviceRuntime setup mode deadline) leaks execution next command supported)
                event who owned serial held

private theorem ordinalAtState_reaches
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {first last :
      ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).History}
    {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin
      fuel first last) (event : (serviceGraph setup mode).EventId) (who : Player)
    (owned : (serviceGraph setup mode).actor? event = some who) (serial : Nat)
    (held : ordinalAtState event who serial first.state) :
    ordinalAtState event who serial last.state := by
  induction path with
  | refl => exact held
  | step joint legal reached rest ih =>
      exact ih (ordinalAtState_transition event who owned serial _ _ joint held reached)

/-- An actual ready source event fixes the binding count before it in every
later record that completed that event. Earlier misses are counted normally;
no canonical-policy or dense-preparation premise is needed. -/
theorem ready_bindingCountBefore_reaches
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {first last :
      ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).History}
    {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (serviceApplication setup mode deadline leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (event : (serviceGraph setup mode).EventId) (who : Player)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (ready : before.execution.application.config.cut.Ready event)
    (completed : event ∈ after.execution.application.config.cut.completed) :
    after.execution.application.publicView.bindingCountBefore who event =
      before.execution.application.publicView.bindingCount who := by
  have initial : ordinalAtState event who
      (before.execution.application.publicView.bindingCount who) first.state := by
    rw [firstState]
    exact Or.inl ⟨ready, rfl⟩
  have final := ordinalAtState_reaches path event who owned _ initial
  rw [lastState] at final
  rcases final with ⟨unfinished, _⟩ | ⟨_, counted⟩
  · exact (unfinished.1 completed).elim
  · exact counted

/-- A commitment to a noncanonical handle fails the actual final content
check, whether the runtime accepted or rejected it. The arbitrary private
material attached to submission is irrelevant to this signed verdict. -/
theorem noncanonicalCommitment_forbidden_reaches
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {first last :
      ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).History}
    {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (serviceApplication setup mode deadline leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (event : (serviceGraph setup mode).EventId)
    (ready : before.execution.application.config.cut.Ready event)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (owned : (serviceGraph setup mode).actor? event = some message.sender)
    (candidate : Handle (serviceGraph setup mode))
    (committed : message.payload.call = .commitment event candidate)
    (different : candidate ≠ (message.sender,
      .prepared (before.execution.application.publicView.bindingCount message.sender)))
    (complete : after.execution.application.config.cut.Terminal) :
    ¬ ((serviceRuntime setup mode deadline).settledRecord leaks after.execution).SettledContent
        message ∧
      ((serviceRuntime setup mode deadline).settledRecord leaks after.execution).permits message =
          false := by
  have completed : event ∈ after.execution.application.config.cut.completed := by
    rw [complete]
    exact Finset.mem_univ event
  have counted := ready_bindingCountBefore_reaches path before after firstState lastState
    event message.sender owned ready completed
  have contentFails : ¬
      ((serviceRuntime setup mode deadline).settledRecord leaks after.execution).SettledContent
      message := by
    intro content
    unfold SettledRecord.SettledContent at content
    rw [committed] at content
    have canonical := content.2
    change candidate = (message.sender,
      .prepared (after.execution.application.publicView.bindingCountBefore message.sender event))
      at canonical
    rw [counted] at canonical
    exact different canonical
  refine ⟨contentFails, SettledRecord.permits_eq_false_of_settled _ message event ?_ ?_
    (fun accepted => contentFails accepted.2)⟩
  · rw [committed]
    rfl
  · exact (after.execution.application.config.history_exact event).mpr completed

variable [Fintype Player]

/-- A persisted noncanonical commitment at a ready source prefix has the
final-record backend's collection bound under every later behavioral policy.
Complete play derives the verdict; it is not an additional audit premise. -/
theorem noncanonicalCommitment_collection_continuation
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (completes : CompletesPlay (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler)
    (service : EvidenceReportService
      (SettledRecord (serviceGraph setup mode) × Message Player (WitnessedPacket
          (serviceGraph setup mode))))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player,
      (menu.information (serviceInitialLaw setup mode) horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol
        (serviceInitialLaw setup mode) horizon scheduler).History)
    (long : 2 * horizon + 1 ≤ history.trace.length + fuel)
    (before : (serviceApplication setup mode deadline leaks).Control) (current : history.state =
        some before)
    (record : (serviceApplication setup mode deadline leaks).TrafficRecord)
    (present : record ∈ (serviceApplication setup mode deadline leaks).stateTraffic history.state)
    (event : (serviceGraph setup mode).EventId)
    (ready : before.execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some record.envelope.sender)
    (candidate : Handle (serviceGraph setup mode)) (committed : record.envelope.payload.call =
      .commitment event candidate)
    (different : candidate ≠ (record.envelope.sender,
      .prepared (before.execution.application.publicView.bindingCount record.envelope.sender))) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      expect ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioralFrom
        profile fuel history)
        (fun final => TerminalAudit.charge
            ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
          ((serviceRuntime setup mode deadline).serviceAudit leaks fun settled =>
            (serviceApplication setup mode deadline leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) service.sample)
          final.state record.envelope.sender) := by
  let app := serviceApplication setup mode deadline leaks
  let model := menu.information (serviceInitialLaw setup mode) horizon scheduler
  let protocol := menu.protocol (serviceInitialLaw setup mode) horizon scheduler
  apply (serviceRuntime setup mode deadline).settledPacket_collection_continuation leaks menu
      (serviceInitialLaw setup mode)
    horizon scheduler service observationRate deliveryRate delivery_nonnegative coverage
    profile fuel history record present
  intro final supported after finalState
  have stopped : app.terminal final.state := by
    rcases protocol.runRandomizedFor_terminal_or_length (model.randomizedChooser profile)
        fuel history final supported with terminal | length
    · exact terminal
    · have traceBound := app.trace_bound (serviceInitialLaw setup mode) horizon scheduler
        (menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler final.trace)
      rw [menu.toRawTrace_length] at traceBound
      have exhausted : app.rank horizon final.state = 0 := by omega
      exact (app.rank_zero horizon final.state).mp exhausted
  have rawTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some after) :=
    finalState ▸ menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler final.trace
  have complete := completes after rawTrace (finalState ▸ stopped)
  have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser profile)
    fuel history final supported
  exact (noncanonicalCommitment_forbidden_reaches
    (menu.reaches_raw
        (serviceInitialLaw setup mode) horizon scheduler path) before after current finalState
    event ready record.envelope owned candidate committed different complete).2

end Vegas

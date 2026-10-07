/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion
import Vegas.Game.SourceServiceReachedDecoding

/-! # A decided owner completes its event with its decision, whatever else completes

An owner decides a fixed action at one of its events, a binding or a
disclosure: at its first turn there it transmits the compiled decision, and it
never submits for the event otherwise (`Vegas.DecidesAt`). Other players are
arbitrary and other events may complete meanwhile, in any dependency mode.
Under the asynchronous contract with `delay + bound < deadline`, along every
run the event completes, if at all, with exactly the decided action, unless
that action is ineffective at the configuration, as a disclosure whose opening
the owner's stored commitment cannot realize
(`Vegas.DecidedEventPhase.runUntil`): only the owner's packet can be accepted for
the event, it realizes the decided action, and expiry would need the deadline to
have passed after the owner's protected first-turn call, which is accepted
first. A disclosure's realization reads only fields of its predecessors, which
no event completing meanwhile changes.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A policy of `owner` decides `action` at `event`: at a first turn there,
before submitting for the event and while an inclusion fits the deadline, it
transmits the compiled decision; and a response submitting for the event is
that decision at such a turn. -/
structure DecidesAt (policy : (serviceApplication setup mode deadline leaks).Policy)
    (bound : (serviceGraph setup mode).EventId → Nat) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event) :
    Prop where
  first : ∀ past view, serviceTurn setup mode deadline leaks owner event past view = some 0 →
    (serviceRuntime setup mode deadline).eventRecorded leaks past event = false →
    view.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline) bound
      event →
    ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner past view event
      action).transmission ≠ none →
    policy past view = PMF.pure ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks
      owner past view event action)
  only : ∀ past view response, response ∈ (policy past view).support →
    (serviceRuntime setup mode deadline).submittedEvent? leaks response = some event →
    serviceTurn setup mode deadline leaks owner event past view = some 0 ∧
      (serviceRuntime setup mode deadline).eventRecorded leaks past event = false ∧
      response = (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner past view
        event action

/-- Deciding at the first turn decides at the event. -/
theorem decidedTurnPolicy_decidesAt (bound : (serviceGraph setup mode).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) :
    DecidesAt (decidedTurnPolicy (deadline := deadline) setup leaks bound owner event action)
      bound owner event action where
  first past view first unrecorded fits loud := by
    unfold decidedTurnPolicy
    rw [(serviceApplication setup mode deadline leaks).turnScheduledPolicy_selected _ (0 : Fin 1)
      _ _ _ _ first]
    unfold decidedOpportunity
    simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fits, loud]
  only past view response chosen submitted :=
    decidedTurnPolicy_submission chosen submitted

/-- For a binding event, realization does not depend on the configuration. -/
theorem RealizesAt.bind_config {first second : (serviceGraph setup mode).Config}
    {state : EventGraphRuntime.State (serviceGraph setup mode)}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    {entry : (serviceApplication setup mode deadline leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (realized : RealizesAt leaks first state event action entry message) :
    RealizesAt leaks second state event action entry message := by
  revert realized
  unfold RealizesAt
  cases nodeView (serviceGraph setup mode) event with
  | bind => exact id
  | resolve _ _ _ _ resolveEq _ =>
      rw [outputEq] at resolveEq
      cases resolveEq
  | sample _ _ sampleEq _ =>
      rw [outputEq] at sampleEq
      cases sampleEq


/-- A configuration step keeps the fields an event reads once its predecessors
have completed. -/
theorem readFields_kept {config next : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId}
    (preds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
      prior ∈ config.cut.completed)
    (step : ConfigStep setup config next) :
    EventGraph.Store.AgreeOn config.store next.store
      ((serviceGraph setup mode).nodes event).readFields := by
  intro field read
  rcases step with same | ⟨other, ready, action, member⟩
  · rw [same]
  · unfold EventGraph.Config.step at member
    rw [PMF.support_map] at member
    obtain ⟨value, _, rfl⟩ := member
    have available := (serviceGraph setup mode).reads_available event field read
    cases field with
    | inl input => rfl
    | inr producer =>
        have done := preds producer available
        have different : producer ≠ other := fun same => ready.1 (same ▸ done)
        rw [EventGraph.Config.store_output, EventGraph.Config.store_output,
          EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different]

/-- Realization moves along a configuration step once the event's predecessors
have completed. -/
theorem RealizesAt.configStep {config next : (serviceGraph setup mode).Config}
    {state : EventGraphRuntime.State (serviceGraph setup mode)}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    {entry : (serviceApplication setup mode deadline leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (preds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
      prior ∈ config.cut.completed)
    (step : ConfigStep setup config next)
    (realized : RealizesAt leaks config state event action entry message) :
    RealizesAt leaks next state event action entry message := by
  have agree := readFields_kept preds step
  revert realized
  unfold RealizesAt
  cases node : nodeView (serviceGraph setup mode) event with
  | bind => exact id
  | sample => exact id
  | resolve owner payload binding checks outputEq codeEq =>
      have reads : ((serviceGraph setup mode).nodes event).readFields =
          insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
        (EventGraph.EventCode.readFields_cast outputEq
          ((serviceGraph setup mode).nodes event)).symm.trans
          (congrArg EventGraph.EventCode.readFields codeEq)
      rw [reads] at agree
      rintro ⟨isTrue, handle, value, call, owner', associated, fixed, stored, result, resolved⟩
      refine ⟨isTrue, handle, value, call, owner', associated, fixed, ?_, result, ?_⟩
      · rw [← binding.get?_congr _ _ (agree binding.field (Finset.mem_insert_self _ _))]
        exact stored
      · rw [← EventGraph.EventCode.resolveOutput?_congr binding checks true _ _ agree]
        exact resolved

/-- Effectiveness is the same on both sides of a configuration step once the
event's predecessors have completed. -/
theorem EffectiveAction.configStep_iff {config next : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    (preds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
      prior ∈ config.cut.completed)
    (step : ConfigStep setup config next) :
    EffectiveAction next event action ↔ EffectiveAction config event action := by
  have agree := readFields_kept preds step
  unfold EffectiveAction
  cases node : nodeView (serviceGraph setup mode) event with
  | bind => exact Iff.rfl
  | sample => exact Iff.rfl
  | resolve owner payload binding checks outputEq codeEq =>
      have reads : ((serviceGraph setup mode).nodes event).readFields =
          insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
        (EventGraph.EventCode.readFields_cast outputEq
          ((serviceGraph setup mode).nodes event)).symm.trans
          (congrArg EventGraph.EventCode.readFields codeEq)
      rw [reads] at agree
      dsimp only
      rw [EventGraph.EventCode.resolveOutput?_congr binding checks true _ _ agree]

/-- A canonical decision that submits for its event is effective at the
configuration it was made at. -/
theorem effective_of_submits (execution : (serviceApplication setup mode deadline leaks).Execution)
    (owner : Player) (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (action : (serviceGraph setup mode).Action event)
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks
      ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner past
        (execution.observe (serviceApplication setup mode deadline leaks) owner) event action) =
      some event) :
    EffectiveAction execution.application.config event action := by
  unfold EffectiveAction
  cases node : nodeView (serviceGraph setup mode) event with
  | bind => trivial
  | sample => trivial
  | resolve actor payload binding checks outputEq codeEq =>
      intro isTrue
      have actorEq : owner = actor :=
        (Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)).symm
      subst actorEq
      have notBind : ∀ owner payload outputEq codeEq,
          nodeView (serviceGraph setup mode) event ≠ .bind owner payload outputEq codeEq := by
        intro _ _ _ _ bind
        rw [node] at bind
        cases bind
      rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_eq_of_not_bind leaks owner
        past _ event action notBind] at submitted
      cases sent : reactiveResolutionPacket owner event payload binding checks outputEq action
          (execution.observe (serviceApplication setup mode deadline leaks) owner).application with
      | some packet =>
          unfold reactiveResolutionPacket at sent
          simp only [isTrue, ↓reduceIte] at sent
          cases resolved : EventGraph.EventCode.resolveOutput? binding checks true
              (execution.observe (serviceApplication setup mode deadline leaks)
                owner).application.observation.store with
          | none => simp [resolved] at sent
          | some result =>
              cases result with
              | failure => simp [resolved] at sent
              | success value =>
                  refine ⟨value, ?_⟩
                  rw [← EventGraph.EventCode.resolveOutput?_playerStore (owner := owner)]
                  exact resolved
      | none =>
          exfalso
          have silent : (serviceRuntime setup mode deadline).serviceDecision leaks owner past
              (execution.observe (serviceApplication setup mode deadline leaks) owner) event
                action = ⟨none⟩ := by
            unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision
            simp only [node, sent, Option.map_none]
            rfl
          rw [silent] at submitted
          cases submitted

/-- A configuration step keeps every completed event completed. -/
theorem ConfigStep.completed_mono {config next : (serviceGraph setup mode).Config}
    (step : ConfigStep setup config next) {event : (serviceGraph setup mode).EventId}
    (done : event ∈ config.cut.completed) : event ∈ next.cut.completed := by
  rcases step with same | ⟨other, ready, action, member⟩
  · rw [same]
    exact done
  · rw [config.step_cut other ready action _ member, EventOrder.Cut.mem_complete]
    exact Or.inr done

/-- **The decided phase.** Facts of play since `start` while `owner` decides
`action` at its `event`: every turn of the owner there saw the event's
predecessors completed; every response of the owner submitting for the event
did so at a first turn there, as an acceptable fresh call of an effective action
realizing it while the event is pending; every first turn there after `start`
at which the action is effective submitted for it; and once the event has
completed, it completed with the action, which is effective, or the action is
ineffective and the event expired. -/
structure DecidedEventPhase (bound : (serviceGraph setup mode).EventId → Nat)
    (start : (serviceApplication setup mode deadline leaks).Execution) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop where
  recallPrefix : ∀ who, start.recall who <+: execution.recall who
  atFirst : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
    serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0
  predsDone : ∀ entry ∈ execution.recall owner,
    entry.beforeView.application.publicView.ownTurn? owner = some event →
    ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
      prior ∈ execution.application.config.cut.completed
  submitted : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
    ∃ message, entry.emitted = some message ∧
      FreshCall setup leaks owner event bound entry message ∧
      EffectiveAction execution.application.config event action ∧
      (event ∉ execution.application.config.cut.completed →
        RealizesAt leaks execution.application.config execution.application event action entry
          message)
  firstTurn : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (start.recall owner).length ≤ before.length →
    serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0 →
    EffectiveAction execution.application.config event action →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event
  completed : event ∈ execution.application.config.cut.completed →
    ((⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
        execution.application.config.history ∧
      EffectiveAction execution.application.config event action) ∨
    (¬ EffectiveAction execution.application.config event action ∧
      ∃ expired, ExpiryAction event expired ∧
        (⟨event, expired⟩ : (serviceGraph setup mode).Completion) ∈
          execution.application.config.history)

/-- At a start where the event is unfinished and untouched, the decided phase
holds trivially. -/
theorem DecidedEventPhase.initial (bound : (serviceGraph setup mode).EventId → Nat)
    {start : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} (action : (serviceGraph setup mode).Action event)
    (untouched : Untouched setup leaks event start)
    (submissions : OwnSubmissionsAtTurn setup leaks start owner)
    (unfinished : event ∉ start.application.config.cut.completed) :
    DecidedEventPhase bound start owner event action start := by
  have tooLong : ∀ before entry after, start.recall owner = before ++ entry :: after →
      (start.recall owner).length ≤ before.length → False := by
    intro before entry after split long
    have := congrArg List.length split
    simp only [List.length_append, List.length_cons] at this
    omega
  have never : ∀ before entry after, start.recall owner = before ++ entry :: after →
      (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
      False := by
    intro before entry after split submitted
    have member : entry ∈ start.recall owner := by rw [split]; simp
    exact start_entry_unready untouched member (submissions entry member event submitted)
  exact ⟨fun _ => List.prefix_refl _,
    fun before entry after split submitted => (never before entry after split submitted).elim,
    fun entry member turn => (start_entry_unready untouched member turn).elim,
    fun before entry after split submitted => (never before entry after split submitted).elim,
    fun before entry after split long => (tooLong before entry after split long).elim,
    fun completed => (unfinished completed).elim⟩

/-- The history only grows across a scheduler command. -/
theorem environmentStep_history_mono
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
    (reached : next ∈
      (execution.environmentStep (serviceApplication setup mode deadline leaks) command).support)
    {completion : (serviceGraph setup mode).Completion}
    (member : completion ∈ execution.application.config.history) :
    completion ∈ next.application.config.history := by
  rcases completionStep_reactive_environmentStep (serviceRuntime setup mode deadline) leaks
      execution next command reached with ⟨configEq, _, _⟩ | ⟨other, ready, action, stepped, _, _⟩
  · rw [configEq]
    exact member
  · rw [execution.application.config.step_history other ready action _ stepped]
    exact List.mem_append_left _ member

/-- **A scheduler command completing the decided event completes it with the
decided action, unless the action is ineffective.** Only the owner's packet can
be accepted for the event, and it realizes the action; expiry of an effective
action would need the deadline to have passed after the owner's protected
first-turn call. -/
theorem DecidedEventPhase.complete_environment {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) {remaining : Nat}
    {start execution next : (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (nonsample : ∀ payload, (serviceGraph setup mode).outputLayout event ≠ .publicData payload)
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (phase : DecidedEventPhase bound start owner event action execution)
    (submissions : OwnSubmissionsAtTurn setup leaks execution owner)
    (answered : ActivationsAnswered setup leaks execution)
    (untouched : Untouched setup leaks event start)
    (command : (serviceApplication setup mode deadline leaks).Command)
    (moved : next ∈
      (execution.environmentStep (serviceApplication setup mode deadline leaks) command).support)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (finished : event ∈ next.application.config.cut.completed) :
    ((⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
        next.application.config.history ∧
      EffectiveAction next.application.config event action) ∨
    (¬ EffectiveAction next.application.config event action ∧
      ∃ expired, ExpiryAction event expired ∧
        (⟨event, expired⟩ : (serviceGraph setup mode).Completion) ∈
          next.application.config.history) := by
  let app := serviceApplication setup mode deadline leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  cases command with
  | activate who =>
      rw [activation_application setup leaks execution next who moved] at finished
      exact (unfinished finished).elim
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact (unfinished finished).elim
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
        at finished ⊢
      cases found : execution.network.lookup id with
      | none =>
          simp only [found] at finished
          exact (unfinished finished).elim
      | some message =>
          simp only [found] at finished ⊢
          cases reactiveAccepted : app.handle execution.application message with
          | none =>
              rw [reactiveAccepted] at finished
              exact (unfinished finished).elim
          | some state =>
              rw [reactiveAccepted] at finished
              have accepted := reactiveHandle_call reactiveAccepted
              obtain ⟨named, namedEq, namedReady, namedAction, namedMember⟩ :=
                handle_config_mem_step (serviceRuntime setup mode deadline) _ _ _ accepted
              have namedIs : named = event := by
                change event ∈ state.config.cut.completed at finished
                rw [execution.application.config.step_cut named namedReady namedAction _
                  namedMember, EventOrder.Cut.mem_complete] at finished
                rcases finished with same | old
                · exact same.symm
                · exact (unfinished old).elim
              subst namedIs
              have sender := handle_sender_actor (serviceRuntime setup mode deadline) _ _ _
                accepted named namedEq
              have senderEq : message.sender = owner :=
                Option.some.inj (sender.symm.trans owned)
              obtain ⟨entry, member, material, transmission, emittedEq, _, _, packet⟩ :=
                facts.provenance.pending message (List.mem_of_find?_eq_some found)
              rw [senderEq] at member
              have submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks
                  entry.action = some named := by
                rw [issued_submittedEvent transmission packet]
                exact namedEq
              obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
              obtain ⟨packetMessage, emittedP, call, effectiveThen, realized⟩ :=
                phase.submitted before entry after split submitted
              rw [emittedEq] at emittedP
              cases Option.some.inj emittedP
              have included := include_realized execution facts.eventStable
                execution.application.config rfl named namedReady owner owned action entry member
                call.ready message senderEq (realized unfinished) state accepted
              left
              refine ⟨?_, (EffectiveAction.configStep_iff (fun _ pred => namedReady.2 pred)
                (Or.inr ⟨named, namedReady, action, included⟩)).mpr effectiveThen⟩
              change (⟨named, action⟩ : (serviceGraph setup mode).Completion) ∈
                state.config.history
              rw [execution.application.config.step_history named namedReady action _ included]
              exact List.mem_append_right _ (List.mem_singleton_self _)
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (environmentStep (serviceRuntime setup mode deadline) execution.application
        command).support at changed
      change event ∈ state.config.cut.completed at finished
      cases command with
      | advanceClock =>
          exfalso
          simp only [environmentStep, PMF.mem_support_pure_iff] at changed
          subst changed
          exact unfinished finished
      | executeSample sampled =>
          exfalso
          rcases (environmentStep_executeSample_config_activated _ _ _ sampled changed).2 with
            ⟨stutter, _⟩ | ⟨sampledReady, sampledAction, sampledStep, _⟩
          · rw [stutter] at finished
            exact unfinished finished
          · have sampledIs : sampled = event := by
              rw [execution.application.config.step_cut sampled sampledReady sampledAction _
                sampledStep, EventOrder.Cut.mem_complete] at finished
              rcases finished with same | old
              · exact same.symm
              · exact (unfinished old).elim
            subst sampledIs
            rw [environmentStep_executeSample_of_nonsample _ _ _ sampledReady (by
              intro samplePayload law sampleEq _ _
              exact nonsample samplePayload sampleEq), PMF.mem_support_pure_iff] at changed
            subst changed
            exact unfinished finished
      | expire expired =>
          obtain ⟨ready, expiredIs, configStep⟩ : execution.application.config.cut.Ready expired ∧
              expired = event ∧ ConfigStep setup execution.application.config state.config := by
            rcases (environmentStep_expire_config_activated _ _ _ expired changed).2 with
              ⟨stutter, _⟩ | ⟨expiredReady, expiredAction, expiredStep, _⟩
            · rw [stutter] at finished
              exact (unfinished finished).elim
            · refine ⟨expiredReady, ?_, Or.inr ⟨expired, expiredReady, expiredAction,
                expiredStep⟩⟩
              rw [execution.application.config.step_cut expired expiredReady expiredAction _
                expiredStep, EventOrder.Cut.mem_complete] at finished
              rcases finished with same | old
              · exact same.symm
              · exact (unfinished old).elim
          subst expiredIs
          have changedConfig : state.config ≠ execution.application.config := by
            intro same
            rw [same] at finished
            exact unfinished finished
          obtain ⟨⟨entered, activated, late⟩, expiredSteps⟩ :=
            expire_completion _ _ expired ready changed changedConfig
          by_cases effective : EffectiveAction execution.application.config expired action
          swap
          · right
            refine ⟨fun effectiveNext => effective ((EffectiveAction.configStep_iff
              (fun _ member => ready.2 member) configStep).mp effectiveNext), ?_⟩
            obtain ⟨expiredAction, expiry⟩ :
                ∃ expiredAction, ExpiryAction expired expiredAction := by
              unfold EffectiveAction at effective
              unfold ExpiryAction
              cases node : nodeView (serviceGraph setup mode) expired with
              | bind => rw [node] at effective; exact (effective trivial).elim
              | sample => rw [node] at effective; exact (effective trivial).elim
              | resolve _ _ _ _ outputEq _ =>
                  exact ⟨cast (congrArg EventGraph.EventField.Action outputEq.symm) false, by
                    simp only [cast_cast, cast_eq]⟩
            refine ⟨expiredAction, expiry, ?_⟩
            change (⟨expired, expiredAction⟩ : (serviceGraph setup mode).Completion) ∈
              state.config.history
            rw [execution.application.config.step_history expired ready expiredAction _
              (expiredSteps expiredAction expiry)]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          exfalso
          have bounded := timely expired (by rw [owned]; rfl)
          obtain ⟨turnEntry, turnMember, turn⟩ := opportunity_turn contract trace answered
            owned ready entered activated (by omega)
          obtain ⟨before, first, after, split, firstTurn⟩ :=
            exists_first_turn (execution.recall owner) ⟨turnEntry, turnMember, turn⟩
          have long : (start.recall owner).length ≤ before.length := by
            by_contra short
            exact start_entry_unready untouched
              (mem_start_of_short (phase.recallPrefix owner) split (by omega))
              (sourceServiceTurn_first firstTurn).1
          have submittedFirst := phase.firstTurn before first after split long firstTurn
            effective
          obtain ⟨packet, emittedFirst, call, _⟩ :=
            phase.submitted before first after split submittedFirst
          have firstMember : first ∈ execution.recall owner := by rw [split]; simp
          have sole : ∀ other' ∈ before ++ after,
              ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other' expired
                packet.id := by
            intro other' otherMember ⟨otherEnvelope, emittedOther, _, addressed, different⟩
            have otherRecall : other' ∈ execution.recall owner := by
              rw [split]
              rcases List.mem_append.mp otherMember with left | right
              · exact List.mem_append_left _ left
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
            have output : otherEnvelope ∈ app.outputs (execution.recall owner) :=
              List.mem_filterMap.mpr ⟨other', otherRecall, emittedOther⟩
            rw [← facts.inputs owner] at output
            have inputMember := (List.mem_filter.mp output).1
            have issuerOwner : otherEnvelope.sender = owner :=
              of_decide_eq_true (List.mem_filter.mp output).2
            obtain ⟨issuer, issuerMember, material, transmission, issuerEmitted, _, _,
              issuerPacket⟩ := facts.provenance.inputs otherEnvelope inputMember
            have issuerSubmitted : (serviceRuntime setup mode deadline).submittedEvent? leaks
                issuer.action = some expired := by
              rw [issued_submittedEvent transmission issuerPacket]
              exact addressed
            rw [issuerOwner] at issuerMember
            obtain ⟨issuerBefore, issuerAfter, issuerSplit⟩ :=
              List.mem_iff_append.mp issuerMember
            have issuerFirst := phase.atFirst issuerBefore issuer issuerAfter issuerSplit
              issuerSubmitted
            have firstAgain := phase.atFirst before first after split submittedFirst
            have lengths : issuerBefore.length = before.length := by
              rcases Nat.lt_trichotomy issuerBefore.length before.length with
                less | equal | greater
              · exfalso
                obtain ⟨_, bound, entryAt⟩ := split_take issuerSplit
                obtain ⟨takeEq, _, _⟩ := split_take split
                have inBefore : issuer ∈ before := by
                  rw [takeEq, ← entryAt]
                  exact List.mem_iff_getElem.mpr ⟨issuerBefore.length, by simp; omega, by simp⟩
                exact (sourceServiceTurn_first firstAgain).2 issuer inBefore
                  (submissions issuer issuerMember expired issuerSubmitted)
              · exact equal
              · exfalso
                obtain ⟨_, bound, entryAt⟩ := split_take split
                obtain ⟨takeEq, _, _⟩ := split_take issuerSplit
                have inBefore : first ∈ issuerBefore := by
                  rw [takeEq, ← entryAt]
                  exact List.mem_iff_getElem.mpr ⟨before.length, by simp; omega, by simp⟩
                exact (sourceServiceTurn_first issuerFirst).2 first inBefore
                  (submissions first firstMember expired submittedFirst)
            obtain ⟨_, _, issuerAt⟩ := split_take issuerSplit
            obtain ⟨_, _, firstAt⟩ := split_take split
            have sameEntry : issuer = first := by
              rw [← issuerAt, ← firstAt]
              simp only [lengths]
            rw [sameEntry, emittedFirst] at issuerEmitted
            exact different (by rw [Option.some.inj issuerEmitted])
          have settled := settlesFreshCalls_history setup leaks contract.inclusion owner expired
            owned trace before first after packet split call sole
          obtain ⟨enteredThen, activatedThen, early⟩ := call.fits.exists
          have kept := (facts.eventStable owner first firstMember expired call.ready
            unfinished).choose_spec.2.2.1 owner owned enteredThen activatedThen
          rw [activated, Option.some.injEq] at kept
          subst kept
          have receipt := (prescribed_packet_settles setup leaks contract.inclusion trace expired
            owner owned before after first packet split call sole).1
            (by change _ < execution.application.clock; omega)
          exact unfinished (settled.2.2 receipt)

/-- **The decided phase is preserved** by every round, whatever the other
players do. -/
theorem DecidedEventPhase.round {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) {remaining : Nat}
    {start execution next : (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (nonsample : ∀ payload, (serviceGraph setup mode).outputLayout event ≠ .publicData payload)
    (loud : ¬ SilentAction event action)
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (phase : DecidedEventPhase bound start owner event action execution)
    (submissions : OwnSubmissionsAtTurn setup leaks execution owner)
    (answered : ActivationsAnswered setup leaks execution)
    (untouched : Untouched setup leaks event start)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (decides : DecidesAt (players owner) bound owner event action)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    DecidedEventPhase bound start owner event action next := by
  let app := serviceApplication setup mode deadline leaks
  have roundStep := round_configStep setup leaks scheduler players execution next reached
  -- An entry at a turn of the owner at the event saw its predecessors completed.
  have turnPreds : ∀ before entry after, execution.recall owner = before ++ entry :: after →
      serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0 →
      ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
        prior ∈ execution.application.config.cut.completed := by
    intro before entry after split first
    have member : entry ∈ execution.recall owner := by rw [split]; simp
    exact phase.predsDone entry member (sourceServiceTurn_first first).1
  -- The completion field moves along the round's configuration step.
  have historyStep : ∀ completion ∈ execution.application.config.history,
      completion ∈ next.application.config.history := by
    intro completion member
    rcases roundStep with same | ⟨other, ready, otherAction, stepped⟩
    · rw [same]
      exact member
    · rw [execution.application.config.step_history other ready otherAction _ stepped]
      exact List.mem_append_left _ member
  have completedStep : event ∈ execution.application.config.cut.completed →
      ((⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
          next.application.config.history ∧
        EffectiveAction next.application.config event action) ∨
      (¬ EffectiveAction next.application.config event action ∧
        ∃ expired, ExpiryAction event expired ∧
          (⟨event, expired⟩ : (serviceGraph setup mode).Completion) ∈
            next.application.config.history) := by
    intro done
    have preds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
        prior ∈ execution.application.config.cut.completed := fun _ member =>
      execution.application.config.cut.predecessor_closed done member
    rcases phase.completed done with ⟨member, effective⟩ | ⟨ineffective, expired, expiry, member⟩
    · exact Or.inl ⟨historyStep _ member,
        (EffectiveAction.configStep_iff preds roundStep).mpr effective⟩
    · exact Or.inr ⟨fun effective => ineffective
        ((EffectiveAction.configStep_iff preds roundStep).mp effective),
        expired, expiry, historyStep _ member⟩
  -- Old submissions keep realizing the action while the event is pending.
  have submittedOld : ∀ before entry after, execution.recall owner = before ++ entry :: after →
      (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
      ∃ message, entry.emitted = some message ∧
        FreshCall setup leaks owner event bound entry message ∧
        EffectiveAction next.application.config event action ∧
        (event ∉ next.application.config.cut.completed →
          RealizesAt leaks next.application.config next.application event action entry
            message) := by
    intro before entry after split submitted
    obtain ⟨message, emitted, call, effective, realized⟩ :=
      phase.submitted before entry after split submitted
    refine ⟨message, emitted, call, (EffectiveAction.configStep_iff
      (turnPreds before entry after split (phase.atFirst before entry after split submitted))
      roundStep).mpr effective, fun pending => ?_⟩
    have pendingNow : event ∉ execution.application.config.cut.completed := fun done =>
      pending (roundStep.completed_mono done)
    exact ((realized pendingNow).round reached).configStep
      (turnPreds before entry after split (phase.atFirst before entry after split submitted))
      roundStep
  have predsOld : ∀ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event →
      ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
        prior ∈ next.application.config.cut.completed := fun entry member turn prior pred =>
    roundStep.completed_mono (phase.predsDone entry member turn prior pred)
  have firstTurnOld : ∀ before entry after, execution.recall owner = before ++ entry :: after →
      (start.recall owner).length ≤ before.length →
      serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0 →
      EffectiveAction next.application.config event action →
      (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event := by
    intro before entry after split long first effective
    exact phase.firstTurn before entry after split long first
      ((EffectiveAction.configStep_iff (turnPreds before entry after split first)
        roundStep).mp effective)
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro who
      rw [recallEq]
      exact phase.recallPrefix who
    · rw [recallEq]
      exact phase.atFirst
    · rw [recallEq]
      exact predsOld
    · rw [recallEq]
      exact submittedOld
    · rw [recallEq]
      exact firstTurnOld
    · intro finished
      by_cases done : event ∈ execution.application.config.cut.completed
      · exact completedStep done
      · exact phase.complete_environment contract timely owned nonsample trace submissions
          answered untouched command moved done finished
  have activate : command = .activate who := by
    cases command with
    | activate actor => cases active; rfl
    | «include» => cases active
    | application => cases active
    | wait => cases active
  subst activate
  have sameApp := activation_application setup leaks execution middle who moved
  have configNext : (middle.respond app who response).application.config =
      execution.application.config := by
    rw [((serviceRuntime setup mode deadline).reactive_respond_application leaks middle who
      response).1, sameApp]
  have completedNext : event ∈ (middle.respond app who response).application.config.cut.completed →
      ((⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
          (middle.respond app who response).application.config.history ∧
        EffectiveAction (middle.respond app who response).application.config event action) ∨
      (¬ EffectiveAction (middle.respond app who response).application.config event action ∧
        ∃ expired, ExpiryAction event expired ∧
          (⟨event, expired⟩ : (serviceGraph setup mode).Completion) ∈
            (middle.respond app who response).application.config.history) := by
    intro finished
    rw [configNext] at finished ⊢
    exact phase.completed finished
  have prefixNext : ∀ player, execution.recall player <+:
      (middle.respond app who response).recall player := by
    intro player
    have extended := respond_recall_prefix middle who player response
    rw [recallEq] at extended
    exact extended
  by_cases isOwner : who = owner
  swap
  · have ownerRecall : (middle.respond app who response).recall owner = execution.recall owner := by
      rw [app.respond_recall_other middle who owner (Ne.symm isOwner) response, recallEq]
    refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_, ?_, ?_, ?_,
      completedNext⟩
    · rw [ownerRecall]
      exact phase.atFirst
    · rw [ownerRecall]
      exact predsOld
    · rw [ownerRecall]
      exact submittedOld
    · rw [ownerRecall]
      exact firstTurnOld
  subst isOwner
  rw [recallEq] at chosen
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon scheduler
      remaining execution middle (.activate who) trace selected moved
  have readyOf (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) : execution.application.config.cut.Ready event := by
    have view := (sourceServiceTurn_first first).1
    have readyView := (PublicView.ownTurn?_spec _ who event view).1
    change middle.application.publicView.EventReady event at readyView
    rw [sameApp] at readyView
    exact (execution.application.publicView_eventReady event).mp readyView
  have firstDecision (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0)
      (effective : EffectiveAction execution.application.config event action) :=
    let early := first_turn_early contract trace answered owned (readyOf first) first
    canonicalServiceDecision_submits (bound := bound) middleTrace event owned
      (by rw [sameApp]; exact readyOf first) early.choose
      (by rw [sameApp]; exact early.choose_spec.1)
      action (by rw [sameApp]; exact effective) loud
  have firstFits (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      middle.application.clock -
          (first_turn_early contract trace answered owned (readyOf first) first).choose +
        bound event < (serviceRuntime setup mode deadline).deadline event := by
    have early :=
      (first_turn_early contract trace answered owned (readyOf first) first).choose_spec.2
    have bounded := timely event (by rw [owned]; rfl)
    rw [sameApp]
    omega
  have fitsFirst (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      PublicView.InclusionFitsDeadline (serviceRuntime setup mode deadline) bound
        (middle.observe app who).application.publicView event := by
    obtain ⟨entered, activated, early⟩ :=
      first_turn_early contract trace answered owned (readyOf first) first
    have bounded := timely event (by rw [owned]; rfl)
    unfold PublicView.InclusionFitsDeadline
    change (match middle.application.activatedAt event with
      | none => False
      | some entered => middle.application.clock - entered + bound event <
          (serviceRuntime setup mode deadline).deadline event)
    rw [sameApp, activated]
    change execution.application.clock - entered + bound event <
        (serviceRuntime setup mode deadline).deadline event
    omega
  have unrecorded (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who) event =
      false := by
    cases recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (execution.recall who) event
    · rfl
    · unfold EventGraphRuntime.eventRecorded at recorded
      obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
      exact ((sourceServiceTurn_first first).2 entry member
        (submissions entry member event (of_decide_eq_true submitted))).elim
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
  rw [recallEq] at recalled
  refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_, ?_, ?_, ?_,
    completedNext⟩
  · intro before entry after split submitted
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      exact (decides.only _ _ response chosen submitted).1
    · exact phase.atFirst before entry rest oldSplit.symm submitted
  · intro entry member turn prior pred
    rw [configNext]
    rw [recalled] at member
    rcases List.mem_append.mp member with old | new
    · exact phase.predsDone entry old turn prior pred
    · rw [List.mem_singleton] at new
      subst new
      have turnNow : middle.application.publicView.ownTurn? who = some event := turn
      have readyView := (PublicView.ownTurn?_spec _ who event turnNow).1
      change middle.application.publicView.EventReady event at readyView
      rw [sameApp] at readyView
      exact ((execution.application.publicView_eventReady event).mp readyView).2 pred
  · intro before entry after split submitted
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      obtain ⟨first, _, decided⟩ := decides.only _ _ response chosen submitted
      have effective : EffectiveAction execution.application.config event action := by
        have made := effective_of_submits middle who (execution.recall who) event owned action
          (by rw [← decided]; exact submitted)
        rw [sameApp] at made
        exact made
      obtain ⟨material, decision, callOf, realized⟩ := firstDecision first effective
      have call := callOf (firstFits first)
      rw [recallEq] at decision call realized
      have responseEq : response = ⟨some material⟩ := decided.trans decision
      subst responseEq
      have submitRecall := respond_submit_recall middle who material
      rw [recallEq, recalled] at submitRecall
      have lastEq := List.append_cancel_left submitRecall
      simp only [List.cons.injEq, and_true] at lastEq
      rw [lastEq]
      rw [decision] at call realized
      refine ⟨_, rfl, call, by rw [configNext]; exact effective, fun _ => ?_⟩
      rw [configNext, ← sameApp]
      exact realized
    · obtain ⟨message, emittedOld, call, effective, realized⟩ :=
        phase.submitted before entry rest oldSplit.symm submitted
      refine ⟨message, emittedOld, call, by rw [configNext]; exact effective, fun pending => ?_⟩
      rw [configNext] at pending ⊢
      exact (realized pending).round reached
  · intro before entry after split long first effective
    rw [configNext] at effective
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      obtain ⟨material, decision, callOf, _⟩ := firstDecision first effective
      have call := callOf (firstFits first)
      rw [recallEq] at decision call
      have transmits : ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
          (execution.recall who) (middle.observe app who) event action).transmission ≠ none := by
        rw [decision]
        exact Option.some_ne_none _
      rw [decides.first _ _ first (unrecorded first) (fitsFirst first) transmits,
        PMF.mem_support_pure_iff] at chosen
      rw [chosen, decision, submittedEvent_submit]
      exact call.addressed
    · exact phase.firstTurn before entry rest oldSplit.symm long first effective

/-- Along every run, the decided phase holds at every stopped point. -/
theorem DecidedEventPhase.runUntil {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {start : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (nonsample : ∀ payload, (serviceGraph setup mode).outputLayout event ≠ .publicData payload)
    (loud : ¬ SilentAction event action)
    (untouched : Untouched setup leaks event start)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (decides : DecidesAt (players owner) bound owner event action)
    (atTurn : SubmitsAtTurn setup leaks (players owner) owner)
    (stop : (serviceApplication setup mode deadline leaks).Execution → Prop) [DecidablePred stop] :
    ∀ (count remaining : Nat)
        (execution : (serviceApplication setup mode deadline leaks).Execution),
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
            horizon scheduler).Trace (some ⟨remaining + count, none, execution⟩) → DecidedEventPhase
        bound start owner event action execution → OwnSubmissionsAtTurn setup leaks execution
        owner → ActivationsAnswered setup leaks execution → ∀ stopped ∈
        ((serviceApplication setup mode deadline leaks).runUntil scheduler players stop count
            execution).support,
        DecidedEventPhase bound start owner event action stopped := by
  let app := serviceApplication setup mode deadline leaks
  intro count
  induction count with
  | zero =>
      intro remaining execution _ phase _ _ stopped reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact phase
  | succ count ih =>
      intro remaining execution trace phase submissions answered stopped reached
      by_cases halt : stop execution
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact phase
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨middleTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon
          scheduler players (remaining + count) execution middle trace moved
        exact ih remaining middle middleTrace
          (phase.round contract timely owned nonsample loud (remaining := remaining + count) trace
            submissions answered untouched decides moved)
          (round_ownSubmissionsAtTurn setup leaks atTurn submissions moved)
          (round_activationsAnswered setup leaks answered moved) stopped rest

/-- A binding is owned by its binding owner, is no sample, and its decision is
never silent nor ineffective. -/
theorem binding_decision_facts {event : (serviceGraph setup mode).EventId} {owner : Player}
    {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (action : (serviceGraph setup mode).Action event) :
    (serviceGraph setup mode).actor? event = some owner ∧
      (∀ payload, (serviceGraph setup mode).outputLayout event ≠ .publicData payload) ∧
      ¬ SilentAction event action ∧
      ∀ config : (serviceGraph setup mode).Config, EffectiveAction config event action := by
  refine ⟨(serviceGraph setup mode).actor?_of_outputLayout_binding outputEq,
    (fun payload same => by rw [outputEq] at same; cases same), ?_, fun config => ?_⟩
  · unfold SilentAction
    cases node : nodeView (serviceGraph setup mode) event with
    | bind => exact id
    | resolve _ _ _ _ resolveEq _ =>
        rw [outputEq] at resolveEq
        cases resolveEq
    | sample => exact id
  · unfold EffectiveAction
    cases node : nodeView (serviceGraph setup mode) event with
    | bind => trivial
    | resolve _ _ _ _ resolveEq _ =>
        rw [outputEq] at resolveEq
        cases resolveEq
    | sample => trivial

/-- A decided binding that has completed completed with its decided value. -/
theorem DecidedEventPhase.binding_completed {bound : (serviceGraph setup mode).EventId → Nat}
    {start execution : (serviceApplication setup mode deadline leaks).Execution}
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {action : (serviceGraph setup mode).Action event}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (phase : DecidedEventPhase bound start owner event action execution)
    (done : event ∈ execution.application.config.cut.completed) :
    (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
      execution.application.config.history :=
  ((phase.completed done).resolve_right fun ineffective =>
    ineffective.1 ((binding_decision_facts outputEq action).2.2.2 _)).1

end Vegas

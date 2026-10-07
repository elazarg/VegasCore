/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion

/-! # A decided binding completes with its decided value, whatever else completes

An owner decides a fixed value at one of its binding events: at its first turn
there it transmits the compiled commitment of that value, and it never submits
for the event otherwise (`Vegas.DecidesAt`). Other players are arbitrary and
other events may complete meanwhile, in any dependency mode. Under the
asynchronous contract with `delay + bound < deadline`, along every run the
event completes, if at all, with exactly the decided value
(`Vegas.BindingPhase.runUntil`): only the owner's packet can be accepted for the
event, it realizes the decided value, and expiry would need the deadline to
have passed after the owner's protected first-turn call, which is accepted
first.
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

/-- **The decided binding phase.** Facts of play since `start` while `owner`
decides `action` at its binding `event`: every response of the owner
submitting for the event did so at a first turn there, as an acceptable fresh
call realizing the action; every first turn there after `start` submitted for
it; and once the event has completed, it completed with the action. -/
structure BindingPhase (bound : (serviceGraph setup mode).EventId → Nat)
    (start : (serviceApplication setup mode deadline leaks).Execution) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop where
  recallPrefix : ∀ who, start.recall who <+: execution.recall who
  atFirst : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
    serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0
  submitted : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
    ∃ message, entry.emitted = some message ∧
      FreshCall setup leaks owner event bound entry message ∧
      RealizesAt leaks start.application.config execution.application event action entry message
  firstTurn : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (start.recall owner).length ≤ before.length →
    serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0 →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event
  completed : event ∈ execution.application.config.cut.completed →
    (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ execution.application.config.history

/-- At a start where the event is unfinished and untouched, the decided
binding phase holds trivially. -/
theorem BindingPhase.initial (bound : (serviceGraph setup mode).EventId → Nat)
    {start : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} (action : (serviceGraph setup mode).Action event)
    (untouched : Untouched setup leaks event start)
    (submissions : OwnSubmissionsAtTurn setup leaks start owner)
    (unfinished : event ∉ start.application.config.cut.completed) :
    BindingPhase bound start owner event action start := by
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

/-- **A scheduler command completing the decided binding completes it with
the decided action.** Only the owner's packet can be accepted for the event,
and it realizes the action; expiry would need the deadline to have passed after
the owner's protected first-turn call. -/
theorem BindingPhase.complete_environment {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) {remaining : Nat}
    {start execution next : (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event} {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (phase : BindingPhase bound start owner event action execution)
    (submissions : OwnSubmissionsAtTurn setup leaks execution owner)
    (answered : ActivationsAnswered setup leaks execution)
    (untouched : Untouched setup leaks event start)
    (command : (serviceApplication setup mode deadline leaks).Command)
    (moved : next ∈
      (execution.environmentStep (serviceApplication setup mode deadline leaks) command).support)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (finished : event ∈ next.application.config.cut.completed) :
    (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ next.application.config.history := by
  let app := serviceApplication setup mode deadline leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have owned := (serviceGraph setup mode).actor?_of_outputLayout_binding outputEq
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
              obtain ⟨packetMessage, emittedP, call, realized⟩ :=
                phase.submitted before entry after split submitted
              rw [emittedEq] at emittedP
              cases Option.some.inj emittedP
              have included := include_realized execution facts.eventStable
                execution.application.config rfl named namedReady owner owned action entry member
                call.ready message senderEq (RealizesAt.bind_config outputEq realized) state
                accepted
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
      exfalso
      cases command with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff] at changed
          subst changed
          exact unfinished finished
      | executeSample sampled =>
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
              rw [outputEq] at sampleEq
              cases sampleEq), PMF.mem_support_pure_iff] at changed
            subst changed
            exact unfinished finished
      | expire expired =>
          obtain ⟨ready, expiredIs⟩ : execution.application.config.cut.Ready expired ∧
              expired = event := by
            rcases (environmentStep_expire_config_activated _ _ _ expired changed).2 with
              ⟨stutter, _⟩ | ⟨expiredReady, expiredAction, expiredStep, _⟩
            · rw [stutter] at finished
              exact (unfinished finished).elim
            · refine ⟨expiredReady, ?_⟩
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
          obtain ⟨⟨entered, activated, late⟩, _⟩ :=
            expire_completion _ _ expired ready changed changedConfig
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

/-- **The decided binding phase is preserved** by every round, whatever the
other players do. -/
theorem BindingPhase.round {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) {remaining : Nat}
    {start execution next : (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event} {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (phase : BindingPhase bound start owner event action execution)
    (submissions : OwnSubmissionsAtTurn setup leaks execution owner)
    (answered : ActivationsAnswered setup leaks execution)
    (untouched : Untouched setup leaks event start)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (decides : DecidesAt (players owner) bound owner event action)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    BindingPhase bound start owner event action next := by
  let app := serviceApplication setup mode deadline leaks
  have owned := (serviceGraph setup mode).actor?_of_outputLayout_binding outputEq
  have effectiveAny : ∀ config : (serviceGraph setup mode).Config,
      EffectiveAction config event action := by
    intro config
    unfold EffectiveAction
    cases node : nodeView (serviceGraph setup mode) event with
    | bind => trivial
    | resolve _ _ _ _ resolveEq _ =>
        rw [outputEq] at resolveEq
        cases resolveEq
    | sample => trivial
  have loud : ¬ SilentAction event action := by
    unfold SilentAction
    cases node : nodeView (serviceGraph setup mode) event with
    | bind => exact id
    | resolve _ _ _ _ resolveEq _ =>
        rw [outputEq] at resolveEq
        cases resolveEq
    | sample => exact id
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro who
      rw [recallEq]
      exact phase.recallPrefix who
    · rw [recallEq]
      exact phase.atFirst
    · intro before entry after split submitted
      rw [recallEq] at split
      obtain ⟨message, emitted, call, realized⟩ :=
        phase.submitted before entry after split submitted
      exact ⟨message, emitted, call, realized.round reached⟩
    · rw [recallEq]
      exact phase.firstTurn
    · intro finished
      by_cases done : event ∈ execution.application.config.cut.completed
      · exact environmentStep_history_mono moved (phase.completed done)
      · exact phase.complete_environment contract timely outputEq trace submissions answered
          untouched command moved done finished
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
      (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
        (middle.respond app who response).application.config.history := by
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
    refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_, ?_, ?_,
      completedNext⟩
    · rw [ownerRecall]
      exact phase.atFirst
    · intro before entry after split submitted
      rw [ownerRecall] at split
      obtain ⟨message, emitted, call, realized⟩ :=
        phase.submitted before entry after split submitted
      exact ⟨message, emitted, call, realized.round reached⟩
    · rw [ownerRecall]
      exact phase.firstTurn
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
      (middle.observe app who) = some 0) :=
    let early := first_turn_early contract trace answered owned (readyOf first) first
    canonicalServiceDecision_submits (bound := bound) middleTrace event owned
      (by rw [sameApp]; exact readyOf first) early.choose
      (by rw [sameApp]; exact early.choose_spec.1)
      action (effectiveAny _) loud
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
  refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_, ?_, ?_,
    completedNext⟩
  · intro before entry after split submitted
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      exact (decides.only _ _ response chosen submitted).1
    · exact phase.atFirst before entry rest oldSplit.symm submitted
  · intro before entry after split submitted
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      obtain ⟨first, _, decided⟩ := decides.only _ _ response chosen submitted
      obtain ⟨material, decision, callOf, realized⟩ := firstDecision first
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
      exact ⟨_, rfl, call, RealizesAt.bind_config outputEq realized⟩
    · obtain ⟨message, emittedOld, call, realized⟩ :=
        phase.submitted before entry rest oldSplit.symm submitted
      exact ⟨message, emittedOld, call, realized.round reached⟩
  · intro before entry after split long first
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      obtain ⟨material, decision, callOf, _⟩ := firstDecision first
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
    · exact phase.firstTurn before entry rest oldSplit.symm long first

/-- Along every run, the decided binding phase holds at every stopped point. -/
theorem BindingPhase.runUntil {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {start : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (untouched : Untouched setup leaks event start)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (decides : DecidesAt (players owner) bound owner event action)
    (atTurn : SubmitsAtTurn setup leaks (players owner) owner)
    (stop : (serviceApplication setup mode deadline leaks).Execution → Prop) [DecidablePred stop] :
    ∀ (count remaining : Nat)
        (execution : (serviceApplication setup mode deadline leaks).Execution),
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
            horizon scheduler).Trace (some ⟨remaining + count, none, execution⟩) → BindingPhase
        bound start owner event action execution → OwnSubmissionsAtTurn setup leaks execution
        owner → ActivationsAnswered setup leaks execution → ∀ stopped ∈
        ((serviceApplication setup mode deadline leaks).runUntil scheduler players stop count
            execution).support,
        BindingPhase bound start owner event action stopped := by
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
          (phase.round contract timely outputEq (remaining := remaining + count) trace
            submissions answered untouched decides moved)
          (round_ownSubmissionsAtTurn setup leaks atTurn submissions moved)
          (round_activationsAnswered setup leaks answered moved) stopped rest

end Vegas

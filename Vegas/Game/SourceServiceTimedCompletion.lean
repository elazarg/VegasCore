/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion

/-! # A fixed decision under arbitrary timing completes with it or by expiry

From a completion boundary, suppose the owner of the current event decides a
fixed action but chooses freely when to submit it: each of its responses is
silence or, at an own turn at which its recall has not yet submitted for the
event, the compiled decision of that action (`Vegas.DecidesWithTiming`).
Whatever the other players do, under the asynchronous contract every stopped
point has completed the event either with that action or with the action by
which expiry completes it (`Vegas.timed_completion_of_follows`).

* Every packet the owner submits for the event realizes the action
  (`Vegas.canonicalServiceDecision_submits`), at whichever turn it is sent.
* Another player's packet for the event is never accepted, so the event
  completes through an accepted packet of the owner, with the action, or by
  expiry, with the expiry action.

Nothing here constrains when the owner submits; a submission after the first
turn may miss the deadline, and the event then expires.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A response of `owner` that decides `action` at `event` with some timing:
silence, or, at an own turn at `event` with no submission for the event in the
recall, the compiled decision of `action`. -/
def TimedDecision (owner : Player) (event : (graph setup).EventId)
    (action : (graph setup).Action event) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action) :
    Prop :=
  response = ⟨none⟩ ∨
    (view.application.publicView.ownTurn? owner = some event ∧
      (runtime setup).eventRecorded leaks past event = false ∧
      response = (runtime setup).canonicalServiceDecision leaks owner past view event action)

/-- Every response of the policy decides `action` at `event` with some timing. -/
def DecidesWithTiming (policy : (application setup leaks).Policy) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event) : Prop :=
  ∀ past view, ∀ response ∈ (policy past view).support,
    TimedDecision owner event action past view response

/-- A policy deciding with some timing submits only at its own turns. -/
theorem DecidesWithTiming.submitsAtTurn {policy : (application setup leaks).Policy}
    {owner : Player} {event : (graph setup).EventId} {action : (graph setup).Action event}
    (follows : DecidesWithTiming policy owner event action) :
    SubmitsAtTurn setup leaks policy owner := by
  intro past view response chosen other submitted
  rcases follows past view response chosen with silent | ⟨turn, _, decision⟩
  · subst silent
    simp [EventGraphRuntime.submittedEvent?] at submitted
  · subst decision
    rw [submittedEvent_canonicalServiceDecision setup leaks owner past view event action other
      submitted]
    exact turn

/-- Every owned event has an action by which expiry completes it. -/
theorem exists_expiryAction {event : (graph setup).EventId} {owner : Player}
    (owned : (graph setup).actor? event = some owner) :
    ∃ action : (graph setup).Action event, ExpiryAction event action := by
  unfold ExpiryAction
  cases node : nodeView (graph setup) event with
  | bind actor payload outputEq codeEq =>
      exact ⟨cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)), by simp⟩
  | resolve actor payload binding checks outputEq codeEq =>
      exact ⟨cast (congrArg EventGraph.EventField.Action outputEq.symm) false, by simp⟩
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none

/-- A packet realizing an action is a call for its event. -/
theorem RealizesAt.addressed {config : (graph setup).Config}
    {state : EventGraphRuntime.State (graph setup)} {event : (graph setup).EventId}
    {action : (graph setup).Action event} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))}
    (realized : RealizesAt leaks config state event action entry message) :
    message.payload.call.event? (graph setup) = some event := by
  revert realized
  unfold RealizesAt
  cases nodeView (graph setup) event with
  | bind actor payload outputEq codeEq =>
      rintro ⟨handle, call, _⟩
      rw [call]
      rfl
  | resolve actor payload binding checks outputEq codeEq =>
      rintro ⟨_, handle, value, call, _⟩
      rw [call]
      rfl
  | sample => exact False.elim

/-- **The timed phase.** Facts of play since the completion boundary `start`
when the owner decides `action` with some timing: recalls only grow, and every
response submitting for the event was sent where the event was ready and
realizes the action. -/
structure TimedPhase (start : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event)
    (execution : (application setup leaks).Execution) : Prop where
  recallPrefix : ∀ who, start.recall who <+: execution.recall who
  submitted : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (runtime setup).submittedEvent? leaks entry.action = some event →
    ∃ message, entry.emitted = some message ∧ message.sender = owner ∧
      entry.beforeView.application.publicView.EventReady event ∧
      RealizesAt leaks start.application.config execution.application event action entry message

/-- At the boundary the timed phase holds: no recorded response submitted for
an event that no recorded response saw as its turn. -/
theorem TimedPhase.initial {start : (application setup leaks).Execution} {owner : Player}
    {event : (graph setup).EventId} (action : (graph setup).Action event)
    (untouched : Untouched setup leaks event start)
    (submissions : OwnSubmissionsAtTurn setup leaks start owner) :
    TimedPhase start owner event action start := by
  refine ⟨fun _ => List.prefix_refl _, ?_⟩
  intro before entry after split submitted
  have member : entry ∈ start.recall owner := by rw [split]; simp
  exact (untouched owner entry member
    (PublicView.ownTurn?_spec _ owner event (submissions entry member event submitted)).1).elim

/-- **The timed phase is preserved** by every round before completion. -/
theorem TimedPhase.round {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {remaining : Nat} {start execution next : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId} {action : (graph setup).Action event}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (phase : TimedPhase start owner event action execution)
    (same : execution.application.config = start.application.config)
    (ready : start.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (effective : EffectiveAction start.application.config event action)
    {players : Player → (application setup leaks).Policy}
    (follows : DecidesWithTiming (players owner) owner event action)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    TimedPhase start owner event action next := by
  let app := application setup leaks
  have readyNow : execution.application.config.cut.Ready event := by rw [same]; exact ready
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · refine ⟨?_, ?_⟩
    · intro who
      rw [recallEq]
      exact phase.recallPrefix who
    · intro before entry after split submitted
      rw [recallEq] at split
      obtain ⟨message, emitted, authored, seen, realized⟩ :=
        phase.submitted before entry after split submitted
      exact ⟨message, emitted, authored, seen, realized.round reached⟩
  have activate : command = .activate who := by
    cases command with
    | activate actor => cases active; rfl
    | «include» => cases active
    | application => cases active
    | wait => cases active
  subst activate
  have sameApp := activation_application setup leaks execution middle who moved
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
    refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_⟩
    intro before entry after split submitted
    rw [ownerRecall] at split
    obtain ⟨message, emitted, authored, seen, realized⟩ :=
      phase.submitted before entry after split submitted
    exact ⟨message, emitted, authored, seen, realized.round reached⟩
  subst isOwner
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler remaining
    execution middle (.activate who) trace selected moved
  have readyMiddle : middle.application.config.cut.Ready event := by rw [sameApp]; exact readyNow
  have effectiveMiddle : EffectiveAction middle.application.config event action := by
    rw [sameApp, same]
    exact effective
  obtain ⟨_, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler trace).1
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event readyNow
    (by rw [owned]; rfl)
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
  rw [recallEq] at recalled
  refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_⟩
  intro before entry after split submitted
  rw [recalled] at split
  rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
  · subst beforeEq entryEq
    rcases follows _ _ response chosen with silent | ⟨_, _, decided⟩
    · subst silent
      simp [EventGraphRuntime.submittedEvent?] at submitted
    · have loud : ¬ SilentAction event action := by
        intro silent
        have quiet := canonicalServiceDecision_silent (leaks := leaks) who (middle.recall who)
          (middle.observe app who) event action silent
        rw [← decided] at quiet
        change (runtime setup).submittedEvent? leaks ⟨response.transmission⟩ = _ at submitted
        rw [quiet] at submitted
        cases submitted
      obtain ⟨material, decision, _, realized⟩ := canonicalServiceDecision_submits
        (bound := fun _ => 0) middleTrace event owned readyMiddle entered
        (by rw [sameApp]; exact activated) action effectiveMiddle loud
      have responseEq : response = ⟨some material⟩ := decided.trans decision
      subst responseEq
      have submitRecall := respond_submit_recall middle who material
      rw [recallEq, recalled] at submitRecall
      have lastEq := List.append_cancel_left submitRecall
      simp only [List.cons.injEq, and_true] at lastEq
      rw [lastEq]
      rw [decision] at realized
      refine ⟨_, rfl, rfl, (middle.application.publicView_eventReady event).mpr readyMiddle, ?_⟩
      rw [sameApp, same] at realized
      exact realized
  · obtain ⟨message, emittedOld, authored, seen, realized⟩ :=
      phase.submitted before entry rest oldSplit.symm submitted
    exact ⟨message, emittedOld, authored, seen, realized.round reached⟩

/-- **The completing round.** A round of the timed phase that changes the
configuration completes the event with the decided action or with an expiry
action. -/
theorem TimedPhase.complete_round {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {remaining : Nat} {start execution next : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId} {action : (graph setup).Action event}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (phase : TimedPhase start owner event action execution)
    (same : execution.application.config = start.application.config)
    (ready : start.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    {players : Player → (application setup leaks).Policy}
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support)
    (changed : next.application.config ≠ start.application.config) :
    next.application.config ∈ (start.application.config.step event ready action).support ∨
      ∃ expired, ExpiryAction event expired ∧
        next.application.config ∈ (start.application.config.step event ready expired).support := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyNow : execution.application.config.cut.Ready event := by rw [same]; exact ready
  have soleOf (other : (graph setup).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    (soleReady_of_ready setup execution.application readyNow).2 other
      ((execution.application.publicView_eventReady other).mpr otherReady)
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have configNext : next.application.config = middle.application.config := by
    rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
    · rfl
    · exact ((runtime setup).reactive_respond_application leaks middle who response).1
  rw [configNext] at changed ⊢
  rw [← same] at changed
  cases command with
  | activate who =>
      rw [activation_application setup leaks execution middle who moved] at changed
      exact (changed rfl).elim
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact (changed rfl).elim
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending at changed ⊢
      cases found : execution.network.lookup id with
      | none =>
          simp only [found] at changed
          exact (changed rfl).elim
      | some message =>
          simp only [found] at changed ⊢
          cases reactiveAccepted : (application setup leaks).handle execution.application
              message with
          | none =>
              rw [reactiveAccepted] at changed
              exact (changed rfl).elim
          | some state =>
              left
              have accepted := reactiveHandle_call reactiveAccepted
              change state.config ∈ _
              obtain ⟨named, namedEq, namedReady, _, _⟩ :=
                handle_config_mem_step (runtime setup) _ _ _ accepted
              have namedIs := soleOf named namedReady
              subst namedIs
              have sender := handle_sender_actor (runtime setup) _ _ _ accepted named namedEq
              have senderEq : message.sender = owner :=
                Option.some.inj (sender.symm.trans owned)
              obtain ⟨entry, member, material, transmission, emittedEq, _, _, packet⟩ :=
                facts.provenance.pending message (List.mem_of_find?_eq_some found)
              rw [senderEq] at member
              have submitted : (runtime setup).submittedEvent? leaks entry.action = some named := by
                rw [issued_submittedEvent transmission packet]
                exact namedEq
              obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
              obtain ⟨packetMessage, emittedP, _, seen, realized⟩ :=
                phase.submitted before entry after split submitted
              rw [emittedEq] at emittedP
              cases Option.some.inj emittedP
              exact include_realized execution facts.stable start.application.config same named
                ready owner owned action entry member seen message senderEq realized state
                accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, stepped, rfl⟩ := PMF.support_map .. ▸ supported
      change state.config ≠ _ at changed
      change state.config ∈ _ ∨ ∃ expired, _ ∧ state.config ∈ _
      change state ∈ (environmentStep (runtime setup) execution.application command).support
        at stepped
      cases command with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff] at stepped
          subst stepped
          exact (changed rfl).elim
      | executeSample other =>
          by_cases otherReady : execution.application.config.cut.Ready other
          · have otherIs := soleOf other otherReady
            subst otherIs
            rw [environmentStep_executeSample_of_nonsample _ _ _ otherReady (by
              intro payload law outputEq codeEq viewEq
              have none := nodeView_sample_actor outputEq codeEq
              rw [owned] at none
              cases none), PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim
          · rw [environmentStep_executeSample_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim
      | expire other =>
          by_cases otherReady : execution.application.config.cut.Ready other
          · have otherIs := soleOf other otherReady
            subst otherIs
            obtain ⟨_, finish⟩ := expire_completion _ _ other readyNow stepped changed
            obtain ⟨expired, expiring⟩ := exists_expiryAction owned
            right
            exact ⟨expired, expiring, mem_step_of_eq same readyNow ready (finish expired expiring)⟩
          · rw [environmentStep_expire_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim

/-- Along a run in which the owner decides with some timing, every point keeps
the boundary configuration or has completed the event with the decided action
or with an expiry action. -/
theorem TimedPhase.runUntil {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {start : (application setup leaks).Execution} {owner : Player}
    {event : (graph setup).EventId} {action : (graph setup).Action event}
    (ready : start.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (effective : EffectiveAction start.application.config event action)
    {players : Player → (application setup leaks).Policy}
    (follows : DecidesWithTiming (players owner) owner event action) :
    ∀ (count remaining : Nat) (execution : (application setup leaks).Execution),
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining + count, none, execution⟩) →
      TimedPhase start owner event action execution →
      execution.application.config = start.application.config →
      ∀ stopped ∈ ((application setup leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) count execution).support,
        stopped.application.config = start.application.config ∨
          stopped.application.config ∈
            (start.application.config.step event ready action).support ∨
          ∃ expired, ExpiryAction event expired ∧
            stopped.application.config ∈
              (start.application.config.step event ready expired).support := by
  let app := application setup leaks
  intro count
  induction count with
  | zero =>
      intro remaining execution _ _ same stopped reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Or.inl same
  | succ count ih =>
      intro remaining execution trace phase same stopped reached
      by_cases halt : event ∈ execution.application.config.cut.completed
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact Or.inl same
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨middleTrace⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler
          players (remaining + count) execution middle trace moved
        by_cases unchanged : middle.application.config = start.application.config
        · exact ih remaining middle middleTrace
            (phase.round (remaining := remaining + count) trace same ready owned effective follows
              moved) unchanged stopped rest
        · have completed := phase.complete_round (remaining := remaining + count) trace same
            ready owned moved unchanged
          have finished : event ∈ middle.application.config.cut.completed := by
            rcases completed with decided | ⟨expired, _, expiredMember⟩
            · rw [start.application.config.step_cut event ready action _ decided,
                EventOrder.Cut.mem_complete]
              exact Or.inl rfl
            · rw [start.application.config.step_cut event ready expired _ expiredMember,
                EventOrder.Cut.mem_complete]
              exact Or.inl rfl
          rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ middle finished] at rest
          cases (PMF.mem_support_pure_iff _ _).mp rest
          exact Or.inr completed

/-- **Timed completion against any other players.** From a completion boundary
of any players at which the owner has submitted only at its own turns, under
complete play, if the owner decides an effective action with some timing, then
whatever the other players do every stopped point has completed the event,
with that action or with an expiry action. -/
theorem timed_completion_of_follows {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {reachers : Player → (application setup leaks).Policy}
    (event : (graph setup).EventId) (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler reachers event.val start)
    (bounded : start.environmentRecall.length ≤ horizon)
    (ready : start.application.config.cut.Ready event)
    {owner : Player} (owned : (graph setup).actor? event = some owner)
    (ownStart : OwnSubmissionsAtTurn setup leaks start owner)
    (action : (graph setup).Action event)
    (effective : EffectiveAction start.application.config event action)
    {players : Player → (application setup leaks).Policy}
    (follows : DecidesWithTiming (players owner) owner event action)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    stopped.application.config ∈ (start.application.config.step event ready action).support ∨
      ∃ expired, ExpiryAction event expired ∧
        stopped.application.config ∈
          (start.application.config.step event ready expired).support := by
  let app := application setup leaks
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    reachers _ bounded start boundary.supported
  have untouched := boundary.untouched event rfl
  rcases TimedPhase.runUntil ready owned effective follows
      (horizon - start.environmentRecall.length) 0 start
      (by simpa only [Nat.zero_add] using startTrace)
      (TimedPhase.initial action untouched ownStart) rfl stopped reached with
    unchanged | completed
  · exfalso
    have notDone : event ∉ stopped.application.config.cut.completed := by
      rw [unchanged]
      exact ready.1
    exact notDone (runUntilHorizon_completes complete bounded startTrace stopped reached)
  · exact completed

end Vegas

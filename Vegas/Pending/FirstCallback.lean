module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ActivationRecall
public import Vegas.Pending.TurnClient
public import Vegas.Pending.EffectiveAction
public import Interaction.ReactiveStopping
public import Interaction.ReactiveRawRoundTrace

@[expose] public section

/-! # Waiting for the first callback of a solitary owned event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

variable {inputs : PMF graph.Inputs}

local notation "app" => (reactiveApplication timeouts) leaks

/-- The opportunity requirement: an owner whose ready event's deadline is
past its reaction bound has had a turn there. -/
private theorem opportunity_turn {event : graph.EventId}
    (ownerSolitary : graph.OwnerSolitary event)
    {horizon : Nat}
    {scheduler : (app).Scheduler}
    {delay bound : graph.EventId → Nat}
    (contract : AsyncContract timeouts leaks
        (inputs.map State.initial) horizon scheduler delay bound) {remaining : Nat}
    {execution : (app).Execution}
    (trace :
        ((app).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered timeouts leaks execution) {owner : Player}
    (owned : graph.actor? event = some owner)
    (ready : execution.application.config.cut.Ready event) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (late : entered + delay event < execution.application.clock) :
    ∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event := by
  have facts := legalFacts timeouts leaks inputs horizon scheduler _ trace
  obtain ⟨scheduled, member, activate, _, seenReady⟩ := contract.opportunity _ trace event owner
    entered owned ((execution.application.publicView_eventReady event).mpr ready) activated late
  obtain ⟨answer, answerMember, viewEq⟩ := answered scheduled member owner activate
  have seen : answer.beforeView.application.publicView.EventReady event := by
    rw [viewEq]
    exact seenReady
  exact ⟨answer, answerMember,
    ownTurn?_of_entry_ready timeouts leaks execution facts.eventStable owner answer
      answerMember event ownerSolitary owned seen ready⟩

/-- The first ready own turn is protected under the reaction and inclusion
budget. The view may be the freshly sampled activation view: only its first
turn count is needed, while the clock and readiness come from the actual raw
scheduler boundary. -/
theorem firstTurn_inclusionFits {event : graph.EventId}
    (ownerSolitary : graph.OwnerSolitary event)
    {horizon : Nat}
    {scheduler : (app).Scheduler}
    {delay bound : graph.EventId → Nat}
    (contract : AsyncContract timeouts leaks
        (inputs.map State.initial) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    {remaining : Nat} {execution : (app).Execution}
    (trace :
        ((app).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered timeouts leaks execution)
    {owner : Player}
    (owned : graph.actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (app).PlayerView}
    (first : turnIndex timeouts leaks owner event (execution.logs owner) view =
        some 0) :
    execution.application.publicView.InclusionFitsDeadline timeouts
        bound event := by
  obtain ⟨inputs, _, invariant⟩ :=
    (reactive_history_invariant timeouts) leaks
      inputs horizon scheduler trace
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
    (by rw [owned]; rfl)
  have early : execution.application.clock ≤ entered + delay event := by
    by_contra late
    obtain ⟨answer, member, turn⟩ := opportunity_turn timeouts leaks ownerSolitary contract trace
      answered owned ready entered activated (by omega)
    exact (turnIndex_first first).2 answer member turn
  have budget := timely event (by rw [owned]; rfl)
  change (match execution.application.activatedAt event with
    | none => False
    | some started => execution.application.clock - started + bound event <
        timeouts.duration event)
  rw [activated]
  omega


private theorem first_of_never
    (execution : (app).Execution) (owner : Player)
    (event : graph.EventId)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    turnIndex timeouts leaks owner event (execution.logs owner)
      (execution.observe (app) owner) = some 0 := by
  change (if execution.application.publicView.ownTurn? owner = some event then
    some ((execution.logs owner).countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? owner = some event)) else none) =
        some 0
  simp only [turn, ↓reduceIte, Option.some.injEq]
  rw [List.countP_eq_zero]
  intro entry member
  simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using never entry member

private theorem waiting_no_pending
    {horizon : Nat} {scheduler : (app).Scheduler}
    (control : (app).Control)
    (trace : ((app).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId)
    (truthful : OwnSubmissionsAtTurn timeouts leaks control.execution owner)
    (never : ∀ entry ∈ control.execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    ∀ message ∈ control.execution.network.pending, message.sender = owner →
      message.payload.call.event? graph ≠ some event := by
  have facts := legalFacts timeouts leaks inputs horizon scheduler control trace
  intro message pending sender named
  obtain ⟨entry, entryPresent, material, transmitted, _emitted, state, known, packet⟩ :=
    facts.provenance.pending message pending
  have old : entry ∈ control.execution.logs owner := sender ▸ entryPresent
  have call : material.call.packet = message.payload.call :=
    congrArg (fun value => value.call) packet
  have submitted : (submittedEvent? timeouts) leaks entry.action = some event := by
    simp only [EventGraphRuntime.submittedEvent?, transmitted]
    rw [call]
    exact named
  exact never entry old (truthful entry old event submitted)

/-- A protected first response determines the completion law from the preceding
scheduler boundary. -/
theorem first_callback_runUntil
    {horizon : Nat} (scheduler : (app).Scheduler)
    (players : Player → (app).Policy)
    (delay bound : graph.EventId → Nat)
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (contract : AsyncContract timeouts leaks
      (inputs.map State.initial) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner) (solitary :
      graph.Solitary event)
    (action : graph.Action event)
    (atResponse : ∀ remaining (execution : (app).Execution),
      ((app).protocol
        (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩) →
      ∀ ready : execution.application.config.cut.Ready event,
      turnIndex timeouts leaks owner event (execution.logs owner)
        (execution.observe (app) owner) = some 0 →
      execution.application.publicView.InclusionFitsDeadline timeouts bound event →
      OwnSubmissionsAtTurn timeouts leaks execution owner →
      (∀ entry ∈ execution.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event) →
      EffectiveAction execution.application.config event action →
      ∀ response ∈ (players owner (execution.logs owner)
          (execution.observe (app) owner)).support,
        (((app).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) remaining
          (execution.respond (app) owner response)).bind fun
            final =>
          continuation final.application.config) =
        (execution.application.config.step event ready action).bind fun after =>
          continuation after) :
    ∀ remaining (execution : (app).Execution),
      ((app).protocol
        (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨remaining, none, execution⟩) →
      ∀ ready : execution.application.config.cut.Ready event,
      OwnSubmissionsAtTurn timeouts leaks execution owner →
      (∀ entry ∈ execution.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event) →
      ActivationsAnswered timeouts leaks execution →
      EffectiveAction execution.application.config event action →
      (((app).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) remaining execution).bind
        fun final => continuation final.application.config) =
        (execution.application.config.step event ready action).bind fun after =>
          continuation after := by
  classical
  let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
  have stepEq {before after : graph.Config} (same : after = before)
      (readyBefore : before.cut.Ready event) (readyAfter : after.cut.Ready event) :
      (after.step event readyAfter action).bind continuation =
        (before.step event readyBefore action).bind continuation := by
    subst after
    rfl
  intro remaining
  induction remaining with
  | zero =>
      intro execution trace ready _ _ _ _
      have terminal := contract.completes _ trace (by exact ⟨rfl, rfl⟩)
      exact (ready.1 (by rw [terminal]; exact Finset.mem_univ _)).elim
  | succ remaining ih =>
      intro execution trace ready truthful never answered effective
      have turn := execution.application.ownTurn?_of_ready solitary.ownerSolitary ready owned
      have first := first_of_never timeouts leaks execution owner event turn never
      have fits := firstTurn_inclusionFits timeouts leaks solitary.ownerSolitary contract timely
        trace answered owned ready first
      have facts := legalFacts timeouts leaks inputs horizon scheduler _ trace
      have safe := waiting_no_pending timeouts leaks _ trace owner event truthful never
      have pending : ¬ stop execution := ready.1
      change ((app).runUntil scheduler players stop (remaining + 1) execution).bind
        (fun final => continuation final.application.config) = _
      rw [ReactiveApplication.runUntil, ite_eq_right pending, PMF.bind_bind]
      apply (bind_congr_on_support _ fun next reached => ?_).trans (PMF.bind_const _ _)
      obtain ⟨command, selected, middle, moved, cases⟩ := round_cases timeouts leaks reached
      have sameMiddle := environment_waiting_config_of_solitary timeouts leaks execution middle
        command event solitary owner ready owned fits.withinDeadline facts.quiescent safe moved
      have recallEq := (app).environmentStep_recall execution middle command moved
      have readyMiddle : middle.application.config.cut.Ready event := sameMiddle.symm ▸ ready
      obtain ⟨nextTrace⟩ := (app).raw_trace_round
        (inputs.map State.initial) horizon scheduler players
        remaining execution next trace reached
      have truthfulMiddle : OwnSubmissionsAtTurn timeouts leaks middle owner := by
        intro entry present
        rw [recallEq] at present
        exact truthful entry present
      rcases cases with ⟨_, nextEq⟩ | ⟨who, active, response, member, nextEq⟩
      · subst next
        exact (ih middle nextTrace readyMiddle truthfulMiddle
          (by simpa only [recallEq] using never)
          (round_activationsAnswered timeouts leaks answered reached)
          (sameMiddle.symm ▸ effective)).trans (stepEq sameMiddle ready readyMiddle)
      · subst next
        by_cases same : who = owner
        · subst who
          have commandEq : command = .activate owner := by
            cases command <;> simp_all [ReactiveApplication.Command.actor?]
          have appEq := activation_application timeouts leaks execution middle owner
            (commandEq ▸ moved)
          have firstMiddle := first_of_never timeouts leaks middle owner event
            (middle.application.ownTurn?_of_ready solitary.ownerSolitary readyMiddle owned)
            (by simpa only [recallEq] using never)
          have fitsMiddle : middle.application.publicView.InclusionFitsDeadline timeouts bound
              event := by rw [appEq]; exact fits
          obtain ⟨middleTrace⟩ := (app).raw_trace_environment
            (inputs.map State.initial) horizon scheduler
            remaining execution middle command trace selected moved
          rw [active] at middleTrace
          exact (atResponse remaining middle middleTrace readyMiddle firstMiddle fitsMiddle
            truthfulMiddle
            (by simpa only [recallEq] using never)
            (sameMiddle.symm ▸ effective) response member).trans
              (stepEq sameMiddle ready readyMiddle)
        · have sameNext : (middle.respond (app) who response).application.config =
              execution.application.config :=
            (((reactive_respond_application timeouts) leaks middle who response).1).trans sameMiddle
          have ownerRecall := (app).respond_recall_other middle who owner (Ne.symm same) response
          have nextRecall : (middle.respond (app) who response).logs owner =
              execution.logs owner := ownerRecall.trans (congrFun recallEq owner)
          have readyNext : (middle.respond (app) who response).application.config.cut.Ready event :=
            sameNext.symm ▸ ready
          exact (ih _ nextTrace readyNext (by
              intro entry present
              rw [nextRecall] at present
              exact truthful entry present)
            (by
              intro entry present
              rw [nextRecall] at present
              exact never entry present)
            (round_activationsAnswered timeouts leaks answered reached)
            (sameNext.symm ▸ effective)).trans (stepEq sameNext ready readyNext)

end Vegas.EventGraphRuntime

module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.AsyncDeviationForeign

@[expose] public section

/-! # Turns read from the environment's recall

Every recorded response answers an activation recorded by the environment, at
the environment's public view, and every recorded activation has such a
response. So whether an owner has had a turn at an event is read from the
environment's recall alone: two executions with one environment recall agree on
which owners have had a turn at which events.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Every recorded response answers a recorded activation of its player at the
environment's public view. -/
def ResponsesActivated (execution : (serviceApplication setup mode duration leaks).Execution) :
    Prop := ∀ who, ∀ answer ∈ execution.logs who, ∃ entry ∈ execution.environmentRecall,
    entry.command = .activate who ∧
      answer.beforeView.application.publicView = entry.beforeView.application

/-- Every round keeps recorded responses answering recorded activations. -/
theorem round_responsesActivated
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy}
    {execution next : (serviceApplication setup mode duration leaks).Execution}
    (valid : ResponsesActivated setup leaks execution)
    (reached : next ∈
        ((serviceApplication setup mode duration leaks).round scheduler players
        execution).support) :
    ResponsesActivated setup leaks next := by
  let app := serviceApplication setup mode duration leaks
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recorded := app.dispatch_environmentRecall players command execution next dispatched
  obtain ⟨middle', moved', resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle' command moved'
  have older (entry : app.EnvironmentEntry) (member : entry ∈ execution.environmentRecall) :
      entry ∈ next.environmentRecall := by
    rw [recorded]
    exact List.mem_append_left _ member
  intro who answer member
  change next ∈ (app.resume players (command.actor? app) middle').support at resumed
  cases actor : command.actor? app with
  | none =>
      rw [actor] at resumed
      simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      subst resumed
      rw [recallEq] at member
      obtain ⟨entry, entryMember, activated, viewEq⟩ := valid who answer member
      exact ⟨entry, older entry entryMember, activated, viewEq⟩
  | some player =>
      rw [actor] at resumed
      change next ∈ (app.invoke players player middle').support at resumed
      rw [ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, _, rfl⟩ := resumed
      have activated : command = .activate player := by
        cases command <;> first | (cases actor; rfl) | cases actor
      subst activated
      by_cases same : who = player
      · subst same
        obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle' who response
        rw [recalled] at member
        rcases List.mem_append.mp member with prior | fresh
        · rw [recallEq] at prior
          obtain ⟨entry, entryMember, activatedEntry, viewEq⟩ := valid who answer prior
          exact ⟨entry, older entry entryMember, activatedEntry, viewEq⟩
        · rw [List.mem_singleton] at fresh
          subst fresh
          have sameApp := activation_application setup leaks execution middle' who moved'
          refine ⟨⟨execution.observeEnvironment app, .activate who⟩, ?_, rfl, ?_⟩
          · rw [recorded]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · change middle'.application.publicView = execution.application.publicView
            rw [sameApp]
      · rw [app.respond_recall_other middle' player who same response, recallEq] at member
        obtain ⟨entry, entryMember, activatedEntry, viewEq⟩ := valid who answer member
        exact ⟨entry, older entry entryMember, activatedEntry, viewEq⟩

variable {setup leaks} in
/-- In completed rounds every recorded response answers a recorded activation. -/
theorem roundsFrom_responsesActivated
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy} (count : Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (supported : execution ∈
        ((serviceApplication setup mode duration leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support) :
    ResponsesActivated setup leaks execution := by
  let app := serviceApplication setup mode duration leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      intro who answer member
      cases member
  | succ count ih =>
      rw [app.roundsFrom_succ (serviceInitialLaw setup mode) scheduler players count] at supported
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      exact round_responsesActivated setup leaks (ih prior priorMem) moved

variable {setup leaks}

/-- **Turns are read from the environment's recall.** An owner has had no turn
at an event exactly when no recorded activation of it saw that event as its
turn. -/
theorem ownerTurns_eq_zero_iff
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (answered : ActivationsAnswered setup leaks execution)
    (activated : ResponsesActivated setup leaks execution) (owner : Player)
    (event : (serviceGraph setup mode).EventId) :
    ownerTurns owner event execution = 0 ↔
      ∀ entry ∈ execution.environmentRecall, entry.command = .activate owner →
        entry.beforeView.application.ownTurn? owner ≠ some event := by
  unfold ownerTurns
  rw [List.countP_eq_zero]
  constructor
  · intro none entry member command turn
    obtain ⟨answer, answerMember, viewEq⟩ := answered entry member owner command
    exact none answer answerMember (by rw [viewEq, turn]; exact decide_eq_true rfl)
  · intro none answer member turn
    obtain ⟨entry, entryMember, command, viewEq⟩ := activated owner answer member
    apply none entry entryMember command
    rw [← viewEq]
    exact of_decide_eq_true turn

/-- Two executions with one environment recall agree on which owners have had
a turn at which events. -/
theorem ownerTurns_eq_zero_congr
    {left right : (serviceApplication setup mode duration leaks).Execution}
    (leftAnswered : ActivationsAnswered setup leaks left)
    (leftActivated : ResponsesActivated setup leaks left)
    (rightAnswered : ActivationsAnswered setup leaks right)
    (rightActivated : ResponsesActivated setup leaks right)
    (recalls : left.environmentRecall = right.environmentRecall) (owner : Player)
    (event : (serviceGraph setup mode).EventId) :
    ownerTurns owner event left = 0 ↔ ownerTurns owner event right = 0 := by
  rw [ownerTurns_eq_zero_iff leftAnswered leftActivated,
    ownerTurns_eq_zero_iff rightAnswered rightActivated, recalls]

end Vegas

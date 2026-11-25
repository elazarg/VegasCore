module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ExecutionFacts
public import Interaction.ReactiveRecallInvariant

@[expose] public section

/-! # Answered activations in completed graph service rounds -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- One round: a scheduler command, its environment step, and the response of
the activated player, if any. -/
theorem round_cases {scheduler : (app).Scheduler}
    {players : Player → (app).Policy}
    {execution next : (app).Execution}
    (reached : next ∈
        ((app).round scheduler players
        execution).support) :
    ∃ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (app))).support,
      ∃ middle ∈
          (execution.environmentStep (app)
              command).support,
          (command.actor? (app) = none ∧ next = middle) ∨ ∃
          who, command.actor? (app) = some who ∧ ∃ response
          ∈ (players who (middle.logs who)
              (middle.observe (app) who)).support,
              next = middle.respond (app) who
                  response := by
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  refine ⟨command, selected, middle, moved, ?_⟩
  change next ∈ ((app).resume players (command.actor? (app)) middle).support at resumed
  cases actor : command.actor? (app) with
  | none =>
      rw [actor] at resumed
      simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      exact Or.inl ⟨rfl, resumed⟩
  | some who =>
      rw [actor] at resumed
      change next ∈ ((app).invoke players who middle).support at resumed
      rw [ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, chosen, rfl⟩ := resumed
      exact Or.inr ⟨who, rfl, response, chosen, rfl⟩

/-- An activation leaves the application unchanged. -/
theorem activation_application
    (execution middle : (app).Execution) (who : Player)
    (moved : middle ∈
        (execution.environmentStep (app)
        (.activate who)).support) :
    middle.application = execution.application := by
  unfold ReactiveApplication.Execution.environmentStep at moved
  rw [PMF.support_map] at moved
  obtain ⟨updated, supported, rfl⟩ := moved
  rw [PMF.support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Every recorded activation was answered by its player at the public view
the scheduler saw. -/
def ActivationsAnswered (execution : (app).Execution) :
    Prop := ∀ entry ∈ execution.environmentRecall, ∀ who, entry.command = .activate who → ∃ answer ∈
    execution.logs who, answer.beforeView.application.publicView = entry.beforeView.application

/-- Every round answers its activation at the scheduler's public view. -/
theorem round_activationsAnswered
    {scheduler : (app).Scheduler}
    {players : Player → (app).Policy}
    {execution next : (app).Execution}
    (valid : ActivationsAnswered timeouts leaks execution)
    (reached : next ∈
        ((app).round scheduler players
        execution).support) :
    ActivationsAnswered timeouts leaks next := by
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recorded := (app).dispatch_environmentRecall players command execution next dispatched
  obtain ⟨middle', moved', resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := (app).environmentStep_recall execution middle' command moved'
  have grows : ∀ who, execution.logs who ⊆ next.logs who := by
    intro who
    change next ∈ ((app).resume players (command.actor? (app)) middle').support at resumed
    cases actor : command.actor? (app) with
    | none =>
        rw [actor] at resumed
        simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
        subst resumed
        rw [recallEq]
    | some player =>
        rw [actor] at resumed
        change next ∈ ((app).invoke players player middle').support at resumed
        rw [ReactiveApplication.invoke, PMF.support_map] at resumed
        obtain ⟨response, _, rfl⟩ := resumed
        rw [← recallEq]
        exact (app).respond_recall_mono middle' player who response
  intro entry member who activated
  rw [recorded] at member
  rcases List.mem_append.mp member with prior | fresh
  · obtain ⟨answer, answered, viewEq⟩ := valid entry prior who activated
    exact ⟨answer, grows who answered, viewEq⟩
  · rw [List.mem_singleton] at fresh
    subst fresh
    change command = .activate who at activated
    subst activated
    have sameApp := activation_application timeouts leaks execution middle' who moved'
    change next ∈ ((app).resume players (some who) middle').support at resumed
    change next ∈ ((app).invoke players who middle').support at resumed
    rw [ReactiveApplication.invoke, PMF.support_map] at resumed
    obtain ⟨response, _, rfl⟩ := resumed
    obtain ⟨emitted, recalled, _⟩ := respond_recall_self timeouts leaks middle' who response
    refine ⟨⟨middle'.observe (app) who, response, emitted⟩, ?_, ?_⟩
    · rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · change middle'.application.publicView = execution.application.publicView
      rw [sameApp]

variable {timeouts leaks} {initial : PMF (State graph)} in
/-- Every activation in completed rounds has an actual response in own recall,
even if that response was silent or sent a packet for a different event. -/
theorem roundsFrom_activationsAnswered
    {scheduler : (app).Scheduler}
    {players : Player → (app).Policy} (count : Nat)
    (execution : (app).Execution)
    (supported : execution ∈
        ((app).roundsFrom initial
        scheduler players count).support) :
    ActivationsAnswered timeouts leaks execution := by
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      intro entry member
      cases member
  | succ count ih =>
      rw [(app).roundsFrom_succ initial scheduler players count] at supported
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      exact round_activationsAnswered timeouts leaks (ih prior priorMem) moved

end Vegas.EventGraphRuntime

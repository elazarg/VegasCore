/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveRiskPersistence

/-! # No new owner binding miss while an owned ready event survives -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Ordered concurrent completions cannot introduce another binding miss for the
owner of a ready event that remains unfinished. -/
theorem CompletionStep.unmissed_of_ready_survives
    (ordered : graph.RevealRelaxedOrdered) {before after : State graph}
    (step : CompletionStep before after) (event : graph.EventId) (owner : Player)
    (ready : before.config.cut.Ready event) (owned : graph.actor? event = some owner)
    (unfinished : event ∉ after.config.cut.completed)
    (unmissed : before.publicView.missedBindingBy owner = false) :
    after.publicView.missedBindingBy owner = false := by
  classical
  apply decide_eq_false
  rintro ⟨missing, missingOwner, missed⟩
  have beforeMissed : before.publicView.missedBinding missing = true := by
    cases kind : graph.outputLayout missing with
    | publicData payload | privateInput actor payload | publication payload =>
        simp only [PublicView.missedBinding, kind, Bool.false_eq_true] at missed
    | binding actor payload =>
        obtain ⟨completed, absent⟩ := (after.publicView_missedBinding missing actor payload kind).mp
          missed
        apply (before.publicView_missedBinding missing actor payload kind).mpr
        rcases step with ⟨configEq, acceptedEq, _⟩ |
          ⟨changed, changedReady, action, supported, _, acceptedChanged⟩
        · exact ⟨configEq ▸ completed, acceptedEq ▸ absent⟩
        · have different : missing ≠ changed := by
            intro same
            subst missing
            have equal := ordered.ready_actor_unique before.config.cut ready changedReady owned
              missingOwner
            exact unfinished (equal ▸ completed)
          have cutEq := before.config.step_cut changed changedReady action after.config supported
          have completedBefore : missing ∈ before.config.cut.completed := by
            rw [cutEq, EventOrder.Cut.mem_complete] at completed
            exact completed.resolve_left different
          have acceptedEq : after.accepted (.inr missing) = before.accepted (.inr missing) := by
            by_contra differs
            exact different (Sum.inr.inj (acceptedChanged (.inr missing) differs).2)
          exact ⟨completedBefore, acceptedEq ▸ absent⟩
  have contradiction := PublicView.missedBindingBy_of_event before.publicView owner missing
    missingOwner beforeMissed
  rw [unmissed] at contradiction
  cases contradiction

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem resume_public_state (players : Player → (runtime.reactiveApplication leaks).Policy)
    (actor : Option Player) (execution next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈
      ((runtime.reactiveApplication leaks).resume players actor execution).support) :
    next.application.config = execution.application.config ∧
      next.application.publicView = execution.application.publicView := by
  cases actor with
  | none => cases (PMF.mem_support_pure_iff _ _).mp reached; exact ⟨rfl, rfl⟩
  | some who =>
      obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact runtime.reactive_respond_application leaks execution who action

/-- The owner's public binding-clear condition persists through any actual
supported dispatch while its currently ready event remains unfinished. -/
theorem unmissed_dispatch_of_ready_survives
    (ordered : graph.RevealRelaxedOrdered)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (event : graph.EventId) (owner : Player)
    (ready : execution.application.config.cut.Ready event)
    (owned : graph.actor? event = some owner)
    (unmissed : execution.application.publicView.missedBindingBy owner = false)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support)
    (unfinished : event ∉ next.application.config.cut.completed) :
    next.application.publicView.missedBindingBy owner = false := by
  obtain ⟨observed, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have same := resume_public_state runtime leaks players (command.actor? _) observed next resumed
  have persists := (runtime.completionStep_reactive_environmentStep leaks execution observed command
    moved).unmissed_of_ready_survives ordered event owner ready owned
      (same.1 ▸ unfinished) unmissed
  rwa [same.2]

/-- A binding miss cannot disappear during a supported dispatch, including
activation responses and rejected inclusions. -/
theorem unmissed_before_dispatch
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support) (owner : Player)
    (unmissed : next.application.publicView.missedBindingBy owner = false) :
    execution.application.publicView.missedBindingBy owner = false := by
  obtain ⟨observed, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have same := resume_public_state runtime leaks players (command.actor? _) observed next resumed
  cases before : execution.application.publicView.missedBindingBy owner with
  | false => rfl
  | true =>
      have persists := runtime.publicMiss_environment leaks owner before moved
      rw [← same.2, unmissed] at persists
      cases persists

end Vegas.EventGraphRuntime

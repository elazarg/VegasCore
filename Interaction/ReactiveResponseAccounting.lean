/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory

/-! # Response counts in actual reactive histories

Every scheduler activation either awaits its one response or has added that
response to the player's recall. This conservation law counts the commands in
the actual environment transcript and permits arbitrary conditional scheduling.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def activationHistory (execution : app.Execution) : List Principal :=
  execution.environmentRecall.filterMap (fun entry => entry.command.actor? app)

theorem environmentStep_environmentRecall (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] := by
  obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ reached
  rfl

private theorem activationHistory_count_append (execution next : app.Execution)
    (command : app.Command)
    (advanced : next.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩]) (who : Principal) :
    (app.activationHistory next).count who = (app.activationHistory execution).count who +
      if command.actor? app = some who then 1 else 0 := by
  unfold activationHistory
  rw [advanced, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.count_append]
  cases actorEq : command.actor? app with
  | none => simp
  | some owner => by_cases same : owner = who <;> simp [same]

private def Accounted (state : app.ProtocolState) : Prop :=
  match state with
  | none => True
  | some control =>
      (∀ who, (control.execution.recall who).length +
        (if control.actor = some who then 1 else 0) =
          (app.activationHistory control.execution).count who) ∧
      (∀ who, control.actor = some who → ∃ past view command,
        control.execution.environmentRecall = past ++ [⟨view, command⟩] ∧
          command.actor? app = some who)

private theorem accounted_history (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state), Accounted app state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := accounted_history initial horizon scheduler before
      have reached : target ∈ (app.transition initial horizon scheduler source joint).support :=
        realized
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact ⟨fun _ => rfl, fun _ impossible => by cases impossible⟩
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some owner =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              refine ⟨?_, fun _ impossible => by cases impossible⟩
              intro who
              simpa only [app.respond_recall_length, app.respond_environmentRecall,
                activationHistory, Option.some.injEq, reduceCtorEq, ↓reduceIte, Nat.add_zero]
                  using inherited.1 who
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, _selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have recalled := app.environmentStep_recall execution next command supported
                  have advanced := app.environmentStep_environmentRecall execution next command
                    supported
                  refine ⟨?_, ?_⟩
                  · intro who
                    rw [recalled, app.activationHistory_count_append execution next command
                      advanced who]
                    have counts := inherited.1 who
                    simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero] at counts
                    rw [counts]
                  · intro who active
                    exact ⟨execution.environmentRecall, execution.observeEnvironment app,
                      command, advanced, active⟩

/-- Counts the player's completed responses and the currently pending
response against activations in the actual environment transcript. -/
theorem response_count_history (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) (who : Principal) :
    (control.execution.recall who).length + (if control.actor = some who then 1 else 0) =
      (app.activationHistory control.execution).count who :=
  (accounted_history app initial horizon scheduler trace).1 who

/-- An active callback was introduced by the final recorded environment
command, even when earlier commands and activation decisions were conditional. -/
theorem active_environment_entry (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (active : control.actor = some who) :
    ∃ past view command, control.execution.environmentRecall = past ++ [⟨view, command⟩] ∧
      command.actor? app = some who :=
  (accounted_history app initial horizon scheduler trace).2 who active

end Interaction.ReactiveApplication

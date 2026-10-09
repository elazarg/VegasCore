/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePassiveContinuation

/-! # Private recall after a player's last callback

Erasing one player's private recall is a total proof projection. It retains
the complete physical application, network and knowledge, public receipts,
scheduler recall, and every other player's exact recall. Once the scheduler
never activates that player again, this projection commutes with every
remaining round under arbitrary policies of the other players.

The projected state need not be a legal game history. The original game and
its information remain unchanged; the projection only compares continuations.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def Execution.eraseRecall (execution : app.Execution) (owner : Principal) : app.Execution :=
  { execution with «recall» := fun who => if who = owner then [] else execution.recall who }

@[simp] theorem eraseRecall_observe (execution : app.Execution) (owner who : Principal) :
    (execution.eraseRecall app owner).observe app who = execution.observe app who := rfl

@[simp] theorem eraseRecall_observeEnvironment (execution : app.Execution) (owner : Principal) :
    (execution.eraseRecall app owner).observeEnvironment app = execution.observeEnvironment app :=
  rfl

theorem eraseRecall_recall_other (execution : app.Execution) (owner who : Principal)
    (different : who ≠ owner) :
    (execution.eraseRecall app owner).recall who = execution.recall who := by
  simp only [Execution.eraseRecall, ite_eq_right different]

theorem eraseRecall_environmentStep (execution : app.Execution) (owner : Principal)
    (command : app.Command) :
    (execution.environmentStep app command).map (fun next => next.eraseRecall app owner) =
      (execution.eraseRecall app owner).environmentStep app command := by
  cases command with
  | wait => simp only [Execution.environmentStep, PMF.pure_map]; rfl
  | activate who => simp only [Execution.environmentStep, PMF.map_comp]; rfl
  | application command => simp only [Execution.environmentStep, PMF.map_comp]; rfl
  | «include» id =>
      simp only [Execution.eraseRecall, Execution.environmentStep, PMF.pure_map,
        Execution.includePending, MessageNetwork.includePending]
      cases execution.network.lookup id <;> rfl

theorem eraseRecall_respond_other (execution : app.Execution) (owner who : Principal)
    (different : who ≠ owner) (response : app.Action) :
    (execution.respond app who response).eraseRecall app owner =
      (execution.eraseRecall app owner).respond app who response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [Execution.respond, Execution.eraseRecall]
      congr 1
      funext observer
      by_cases focal : observer = owner
      · subst observer
        simp only [↓reduceIte, Ne.symm different, ↓reduceIte]
      · by_cases acting : observer = who
        · subst observer
          simp only [↓reduceIte, different, Execution.observe]
        · simp only [focal, acting, ↓reduceIte]
  | some submission =>
      simp only [Execution.respond, Execution.eraseRecall]
      congr 1
      funext observer
      by_cases focal : observer = owner
      · subst observer
        simp only [↓reduceIte, Ne.symm different, ↓reduceIte]
      · by_cases acting : observer = who
        · subst observer
          simp only [↓reduceIte, different, Execution.observe]
        · simp only [focal, acting, ↓reduceIte]

theorem eraseRecall_resume (players : Principal → app.Policy) (actor : Option Principal)
    (owner : Principal) (absent : actor ≠ some owner) (execution : app.Execution) :
    (app.resume players actor execution).map (fun next => next.eraseRecall app owner) =
      app.resume players actor (execution.eraseRecall app owner) := by
  cases actor with
  | none => simp only [resume, PMF.pure_map]
  | some who =>
      have different : who ≠ owner := fun equal => absent (congrArg some equal)
      simp only [resume, invoke, PMF.map_comp, eraseRecall_recall_other app _ _ _ different,
        eraseRecall_observe]
      apply map_congr_on_support
      intro response _
      exact eraseRecall_respond_other app execution owner who different response

theorem eraseRecall_dispatch (players : Principal → app.Policy) (command : app.Command)
    (owner : Principal) (absent : command.actor? app ≠ some owner) (execution : app.Execution) :
    (app.dispatch players command execution).map (fun next => next.eraseRecall app owner) =
      app.dispatch players command (execution.eraseRecall app owner) := by
  rw [dispatch, PMF.map_bind]
  calc
    _ = (execution.environmentStep app command).bind (fun next =>
        app.resume players (command.actor? app) (next.eraseRecall app owner)) := by
      apply bind_congr_on_support
      intro next _
      exact eraseRecall_resume app players (command.actor? app) owner absent next
    _ = ((execution.environmentStep app command).map
        (fun next => next.eraseRecall app owner)).bind
          (app.resume players (command.actor? app)) := by rw [PMF.bind_map]; rfl
    _ = _ := by rw [eraseRecall_environmentStep]; rfl

variable (scheduler : app.Scheduler) (cursor : Nat) (owner : Principal)
  (absent : ∀ past view, cursor ≤ past.length →
    ∀ command ∈ (scheduler past view).support, command.actor? app ≠ some owner)

include absent in
theorem eraseRecall_round (players : Principal → app.Policy) (execution : app.Execution)
    (later : cursor ≤ execution.environmentRecall.length) :
    (app.round scheduler players execution).map (fun next => next.eraseRecall app owner) =
      app.round scheduler players (execution.eraseRecall app owner) := by
  rw [round, PMF.map_bind]
  change _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind _
  apply bind_congr_on_support
  intro command selected
  exact eraseRecall_dispatch app players command owner (absent _ _ later command selected) execution

include absent in
/-- Exact total projection of the remaining physical execution law. The
other players retain their original policies and every observation. -/
theorem eraseRecall_runRounds (players : Principal → app.Policy) (count : Nat)
    (execution : app.Execution) (later : cursor ≤ execution.environmentRecall.length) :
    (app.runRounds scheduler players count execution).map (fun next => next.eraseRecall app owner) =
      app.runRounds scheduler players count (execution.eraseRecall app owner) := by
  induction count generalizing execution with
  | zero => simp only [runRounds, PMF.pure_map]
  | succ count ih =>
      rw [runRounds, PMF.map_bind]
      calc
        _ = (app.round scheduler players execution).bind (fun next =>
            app.runRounds scheduler players count (next.eraseRecall app owner)) := by
          apply bind_congr_on_support
          intro next reached
          apply ih
          have length := app.round_environmentRecall_length scheduler players execution next reached
          omega
        _ = ((app.round scheduler players execution).map
            (fun next => next.eraseRecall app owner)).bind
              (app.runRounds scheduler players count) := by rw [PMF.bind_map]; rfl
        _ = _ := by rw [eraseRecall_round app scheduler cursor owner absent players execution later]
                    rfl

include absent in
/-- Changing only the inactive owner's private recall preserves every
projected terminal law, even while other players continue to react. -/
theorem continuation_eq_of_erasedRecall_eq (players : Principal → app.Policy) (count : Nat)
    (first second : app.Execution) (later : cursor ≤ first.environmentRecall.length)
    (same : first.eraseRecall app owner = second.eraseRecall app owner) :
    (app.runRounds scheduler players count first).map (fun next => next.eraseRecall app owner) =
      (app.runRounds scheduler players count second).map
        (fun next => next.eraseRecall app owner) := by
  have secondLater : cursor ≤ second.environmentRecall.length := by
    have recalls := congrArg (fun execution : app.Execution => execution.environmentRecall) same
    change first.environmentRecall = second.environmentRecall at recalls
    rwa [← recalls]
  rw [eraseRecall_runRounds app scheduler cursor owner absent players count first later,
    eraseRecall_runRounds app scheduler cursor owner absent players count second secondLater, same]

end Interaction.ReactiveApplication

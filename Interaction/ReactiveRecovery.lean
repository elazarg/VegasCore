/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveRecall

/-! # Completing a policy after its own deviations

A player can check its own recorded responses against the prescribed policy at
the views where they were chosen. Recovery changes the policy only after an
unsupported response. This is a definition of a total strategy, with no extra
runtime state, observations, or player activations.

Starting with consistent recall, recovery preserves the entire execution law.
This does not assert optimality of the recovery continuation.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} {app : ReactiveApplication Principal}

/-- Consistency checks actions at their original local views and recall prefixes.
It does not compare random choices with fresh draws from the policy. -/
inductive Policy.Consistent (policy : app.Policy) : List app.PlayerEntry → Prop
  | nil : Consistent policy []
  | snoc {history : List app.PlayerEntry} (entry : app.PlayerEntry)
      (prior : Consistent policy history)
      (supported : entry.action ∈ (policy history entry.beforeView).support) :
      Consistent policy (history ++ [entry])

theorem Policy.consistent_snoc_iff (policy : app.Policy)
    (history : List app.PlayerEntry) (entry : app.PlayerEntry) :
    policy.Consistent (history ++ [entry]) ↔ policy.Consistent history ∧
      entry.action ∈ (policy history entry.beforeView).support := by
  constructor
  · generalize eq : history ++ [entry] = total
    intro valid
    cases valid with
    | nil => simp at eq
    | @snoc earlier last prior supported =>
        have lengths := congrArg List.length eq
        have same := List.append_inj eq (by simpa using lengths)
        rcases same with ⟨rfl, lastEq⟩
        cases List.singleton_inj.mp lastEq
        exact ⟨prior, supported⟩
  · rintro ⟨prior, supported⟩
    exact .snoc entry prior supported

theorem Policy.Consistent.of_append {policy : app.Policy}
    {before after : List app.PlayerEntry} (valid : policy.Consistent (before ++ after)) :
    policy.Consistent before := by
  induction after using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using valid
  | append_singleton last rest ih =>
      rw [← List.append_assoc, Policy.consistent_snoc_iff] at valid
      exact ih valid.1

open Classical in
def Policy.recover (prescribed recovery : app.Policy) : app.Policy :=
  fun history view => if prescribed.Consistent history then prescribed history view
    else recovery history view

theorem Policy.recover_eq (prescribed recovery : app.Policy)
    (history : List app.PlayerEntry) (view : app.PlayerView)
    (consistent : prescribed.Consistent history) :
    prescribed.recover recovery history view = prescribed history view := by
  simp only [recover, consistent, ↓reduceIte]

theorem Policy.recover_eq_recovery (prescribed recovery : app.Policy)
    (history : List app.PlayerEntry) (view : app.PlayerView)
    (inconsistent : ¬ prescribed.Consistent history) :
    prescribed.recover recovery history view = recovery history view := by
  simp only [recover, inconsistent, ↓reduceIte]

variable [DecidableEq Principal]

/-- Opponents need not follow the prescribed policy. Only the focal player's
own supported actions enter its consistency check. -/
theorem Policy.recover_invariant (prescribed recovery : app.Policy) (who : Principal)
    (players : Principal → app.Policy) (focal : players who = prescribed.recover recovery) :
    app.PolicyInvariant players
      (fun execution => prescribed.Consistent (execution.recall who)) where
  respond execution actor action valid supported := by
    by_cases same : who = actor
    · subst actor
      rw [focal, prescribed.recover_eq recovery _ _ valid] at supported
      rcases action with ⟨transmission⟩
      cases transmission with
      | none =>
          simpa only [Execution.respond, ↓reduceIte] using
            Policy.Consistent.snoc (policy := prescribed)
              ⟨execution.observe app who, ⟨none⟩, none⟩ valid supported
      | some transmission =>
          cases transmission <;> simp only [Execution.respond, ↓reduceIte] <;>
            exact .snoc _ valid supported
    · rw [app.respond_recall_other execution actor who same action]
      exact valid
  environment execution next command valid reached := by
    rw [app.environmentStep_recall execution next command reached]
    exact valid

/-- An existing policy invariant remains available after completing the focal
policy. The additional premise records where that completion agrees with it. -/
theorem PolicyInvariant.recover {players : Principal → app.Policy}
    {predicate : app.Execution → Prop} (invariant : app.PolicyInvariant players predicate)
    (who : Principal) (recovery : app.Policy) :
    app.PolicyInvariant (Function.update players who ((players who).recover recovery))
      (fun execution => predicate execution ∧ (players who).Consistent (execution.recall who)) := by
  let repaired := Function.update players who ((players who).recover recovery)
  have consistent := (players who).recover_invariant recovery who repaired
    (Function.update_self ..)
  refine ⟨?_, ?_⟩
  · intro execution actor action valid supported
    refine ⟨invariant.respond execution actor action valid.1 ?_,
      consistent.respond execution actor action valid.2 supported⟩
    by_cases same : actor = who
    · subst actor
      simpa only [Function.update_self, Policy.recover_eq _ _ _ _ valid.2] using supported
    · simpa only [Function.update_of_ne same] using supported
  · intro execution next command valid reached
    exact ⟨invariant.environment execution next command valid.1 reached,
      consistent.environment execution next command valid.2 reached⟩

/-- Policies that agree on an invariant set produce exactly the same round
law there, including player recall, leaked messages, and scheduler recall. -/
theorem PolicyInvariant.runRounds_congr {players : Principal → app.Policy}
    {predicate : app.Execution → Prop} (invariant : app.PolicyInvariant players predicate)
    (other : Principal → app.Policy)
    (agree : ∀ execution, predicate execution → ∀ who,
      players who (execution.recall who) (execution.observe app who) =
        other who (execution.recall who) (execution.observe app who))
    (scheduler : app.Scheduler) (count : Nat) (execution : app.Execution)
    (valid : predicate execution) :
    app.runRounds scheduler players count execution =
      app.runRounds scheduler other count execution := by
  have resumeEq (actor : Option Principal) (current : app.Execution)
      (ok : predicate current) : app.resume players actor current =
        app.resume other actor current := by
    cases actor with
    | none => rfl
    | some who =>
        exact congrArg (fun law => law.map (current.respond app who)) (agree current ok who)
  have dispatchEq (command : app.Command) (current : app.Execution)
      (ok : predicate current) : app.dispatch players command current =
        app.dispatch other command current := by
    apply FinDist.bind_congr
    intro next reached
    exact resumeEq _ next (invariant.environment current next command ok reached)
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      have stepEq : app.round scheduler players execution =
          app.round scheduler other execution :=
        FinDist.bind_congr fun command _ => dispatchEq command execution valid
      change (app.round scheduler players execution).bind _ =
        (app.round scheduler other execution).bind _
      rw [← stepEq]
      apply FinDist.bind_congr
      intro next reached
      obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      exact ih next (invariant.dispatch command execution next valid moved)

/-- Completing one player's policy changes no initialized execution law,
even with arbitrary opponents, scheduler, and passive observation rule. The
stronger statement applies at every execution with consistent own recall. -/
theorem Policy.recover_runRounds (players : Principal → app.Policy) (who : Principal)
    (recovery : app.Policy) (scheduler : app.Scheduler) (count : Nat)
    (execution : app.Execution) (valid : (players who).Consistent (execution.recall who)) :
    app.runRounds scheduler (Function.update players who ((players who).recover recovery))
      count execution = app.runRounds scheduler players count execution := by
  apply ((players who).recover_invariant recovery who _ (Function.update_self ..)).runRounds_congr
    players ?_ scheduler count execution valid
  intro current consistent actor
  by_cases same : actor = who
  · subst actor
    simpa only [Function.update_self] using
      (players who).recover_eq recovery _ _ consistent
  · simp only [Function.update_of_ne same]

/-- Agreement on an execution invariant also preserves canonical state laws
at intermediate scheduler and player states, for every fuel bound. -/
theorem PolicyInvariant.canonical_run_congr {players : Principal → app.Policy}
    {predicate : app.Execution → Prop} (invariant : app.PolicyInvariant players predicate)
    (other : Principal → app.Policy)
    (agree : ∀ execution, predicate execution → ∀ who,
      players who (execution.recall who) (execution.observe app who) =
        other who (execution.recall who) (execution.observe app who))
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (setup : ∀ state ∈ initial.support, predicate (Execution.initial app state)) (fuel : Nat) :
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun who => app.encodePolicy (players who))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        ExecutionProtocol.History.state) =
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun who => app.encodePolicy (other who))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        ExecutionProtocol.History.state) := by
  rw [app.run_map_state, app.run_map_state]
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      apply FinDist.bind_congr
      intro before reached
      have valid := invariant.canonical_run initial horizon scheduler setup fuel before
        (by rwa [app.run_map_state])
      cases before with
      | none => rfl
      | some control =>
          rcases control with ⟨remaining, current, execution⟩
          cases current with
          | none => rfl
          | some who =>
              change (players who (execution.recall who) (execution.observe app who)).bind
                (fun action => app.transition initial horizon scheduler
                  (some ⟨remaining, some who, execution⟩)
                  (fun observer => if observer = who then some action else none)) =
                (other who (execution.recall who) (execution.observe app who)).bind _
              rw [agree execution valid who]

theorem Policy.recover_canonical_run (players : Principal → app.Policy) (who : Principal)
    (recovery : app.Policy) (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (fuel : Nat) :
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun actor => app.encodePolicy
        (Function.update players who ((players who).recover recovery) actor))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        ExecutionProtocol.History.state) =
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun actor => app.encodePolicy (players actor))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        ExecutionProtocol.History.state) := by
  apply ((players who).recover_invariant recovery who _
    (Function.update_self ..)).canonical_run_congr players ?_ initial horizon scheduler
      (fun _ _ => .nil) fuel
  intro current consistent actor
  by_cases same : actor = who
  · subst actor
    simpa only [Function.update_self] using
      (players who).recover_eq recovery _ _ consistent
  · simp only [Function.update_of_ne same]

end Interaction.ReactiveApplication

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import Interaction.MessageApplicationPending
import Interaction.MessageReplay

/-! # Observation locality of player-only polling

Submission and rebroadcast change the sender's local view and the pending
pool. Other players learn of that traffic through later delivery or inclusion,
not through the polling invocation itself. If private application commands also
preserve another player's view, a sequence of other-player polls preserves
that player's entire policy input. The policies being polled are unrestricted.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal uProjection

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- A raw command by another principal preserves the observer's actual
history and current view, provided the application's private transition does.
No restriction is imposed on submission or replay payloads. -/
theorem playerStep_other_input (actor observer : Principal) (hne : observer ≠ actor)
    (hprivate : ∀ state command,
      app.observePlayer (app.privateStep state actor command) observer =
        app.observePlayer state observer)
    (execution next : app.PolicyExecution) (command : app.PlayerCommand)
    (hnext : next ∈ (app.playerStep actor execution command).support) :
    (next.principalHistory observer, State.observe app next.native observer) =
      (execution.principalHistory observer, State.observe app execution.native observer) := by
  have hhistory := app.playerStep_other_history actor observer hne execution command next hnext
  have hnative : next.native ∈
      ((app.playerStep actor execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [app.playerStep_native] at hnative
  have hview : State.observe app next.native observer =
      State.observe app execution.native observer := by
    cases command with
    | privateCommand command =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        simp only [State.observe, hprivate]
    | submit payload =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        simp only [State.observe, MessagePool.submit, MessagePool.observe, if_neg hne]
    | replay id =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        simp only [State.observe, MessagePool.replay_other_observe _ _ _ _ hne]
    | wait =>
        simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at hnative
        rw [hnative]
  exact Prod.ext hhistory hview

/-- Other-player polling leaves the observer's input unchanged on every
supported branch, even when all polled policies randomize. This deliberately
excludes environment turns, which can deliver or publish messages. -/
theorem runPolicies_other_input (observer : Principal)
    (hprivate : ∀ state actor command, observer ≠ actor →
      app.observePlayer (app.privateStep state actor command) observer =
        app.observePlayer state observer)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (henvironment : Invocation.environment ∉ schedule)
    (hobserver : Invocation.player observer ∉ schedule)
    (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    (next.principalHistory observer, State.observe app next.native observer) =
      (execution.principalHistory observer, State.observe app execution.native observer) := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      cases invocation with
      | environment => exact False.elim (henvironment (List.mem_cons_self ..))
      | player actor =>
          have hne : observer ≠ actor := by
            intro heq
            subst actor
            exact hobserver (List.mem_cons_self ..)
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          exact (ih (fun hmem => henvironment (List.mem_cons_of_mem _ hmem))
            (fun hmem => hobserver (List.mem_cons_of_mem _ hmem)) middle hnext).trans
              (app.playerStep_other_input actor observer hne
                (fun state command => hprivate state actor command hne)
                execution middle command hstep)

/-- Other-player commands preserve any application projection left unchanged
by their private commands, the observer's allocation counter, and every
already-pending lookup result. Submission and replay may add unrelated traffic;
no equality of complete pools is asserted. The projection is proof-facing and
need not be part of the player's observation. -/
private theorem playerStep_other_frame {Projection : Type uProjection}
    (observer actor : Principal) (hne : observer ≠ actor)
    (project : app.Application → Projection)
    (hprivate : ∀ state command,
      project (app.privateStep state actor command) = project state)
    (execution next : app.PolicyExecution) (command : app.PlayerCommand)
    (hnext : next ∈ (app.playerStep actor execution command).support) :
    project next.native.application = project execution.native.application ∧
      next.native.pool.nextSerial observer = execution.native.pool.nextSerial observer ∧
      ∀ id message, execution.native.pool.lookup id = some message →
        next.native.pool.lookup id = some message := by
  have hnative : next.native ∈
      ((app.playerStep actor execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [app.playerStep_native] at hnative
  cases command with
  | privateCommand command =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨hprivate _ _, rfl, fun _ _ hlookup => hlookup⟩
  | submit payload =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      refine ⟨rfl, by simp only [MessagePool.submit, if_neg hne], ?_⟩
      intro id message hlookup
      exact execution.native.pool.lookup_submit_of_some id message hlookup actor payload
  | replay id =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      refine ⟨rfl, ?_, ?_⟩
      · unfold MessagePool.replay
        split <;> rfl
      · intro selected message hlookup
        exact execution.native.pool.lookup_replay_of_some selected message hlookup actor id
  | wait =>
      simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨rfl, rfl, fun _ _ hlookup => hlookup⟩

/-- A player-only schedule excluding the observer preserves its private
application projection and allocation counter. Existing pending envelopes
remain selectable, including when another player rebroadcasts them. All
policies may randomize and submit arbitrary payloads. -/
theorem runPolicies_other_frame {Projection : Type uProjection}
    (observer : Principal) (project : app.Application → Projection)
    (hprivate : ∀ state actor command, observer ≠ actor →
      project (app.privateStep state actor command) = project state)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (henvironment : Invocation.environment ∉ schedule)
    (hobserver : Invocation.player observer ∉ schedule)
    (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    project next.native.application = project execution.native.application ∧
      next.native.pool.nextSerial observer = execution.native.pool.nextSerial observer ∧
      ∀ id message, execution.native.pool.lookup id = some message →
        next.native.pool.lookup id = some message := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨rfl, rfl, fun _ _ hlookup => hlookup⟩
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      cases invocation with
      | environment => exact False.elim (henvironment (List.mem_cons_self ..))
      | player actor =>
          have hne : observer ≠ actor := by
            intro heq
            subst actor
            exact hobserver (List.mem_cons_self ..)
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have first := app.playerStep_other_frame observer actor hne project
            (fun state command => hprivate state actor command hne)
            execution middle command hstep
          have last := ih (fun hmem => henvironment (List.mem_cons_of_mem _ hmem))
            (fun hmem => hobserver (List.mem_cons_of_mem _ hmem)) middle hnext
          exact ⟨last.1.trans first.1, last.2.1.trans first.2.1,
            fun id message hlookup => last.2.2 id message (first.2.2 id message hlookup)⟩

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_other_input' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_other_input

/-- info: 'Interaction.MessageApplication.runPolicies_other_frame' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_other_frame

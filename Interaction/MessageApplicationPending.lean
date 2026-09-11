/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Pending messages across adversarial player reactions -/

noncomputable section

namespace Interaction.MessagePool

universe uPrincipal uPayload

variable {Principal : Type uPrincipal} {Payload : Type uPayload} [DecidableEq Principal]

/-- Submission cannot shadow an already successful pending lookup. -/
theorem lookup_submit_of_some (pool : MessagePool Principal Payload)
    (id : MessageId Principal) (message : Message Principal Payload)
    (hlookup : pool.lookup id = some message) (sender : Principal) (payload : Payload) :
    (pool.submit sender payload).2.lookup id = some message := by
  unfold lookup at hlookup
  simp only [submit, lookup, List.find?_append, hlookup, Option.or]

/-- Replay either leaves pending messages unchanged or appends one. -/
theorem lookup_replay_of_some (pool : MessagePool Principal Payload)
    (id : MessageId Principal) (message : Message Principal Payload)
    (hlookup : pool.lookup id = some message) (broadcaster : Principal)
    (replayed : MessageId Principal) :
    (pool.replay broadcaster replayed).state.lookup id = some message := by
  unfold lookup at hlookup
  unfold replay
  split
  · unfold lookup
    rw [List.find?_append, hlookup]
    rfl
  · exact hlookup

end Interaction.MessagePool

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable {app : MessageApplication Principal}

/-- Every supported player step preserves an already pending message. -/
theorem playerStep_pending_lookup
    (who : Principal) (execution next : app.PolicyExecution)
    (command : app.PlayerCommand) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (hlookup : execution.native.pool.lookup id = some message)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.native.pool.lookup id = some message := by
  cases command with
  | privateCommand registration =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact hlookup
  | submit payload =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact execution.native.pool.lookup_submit_of_some id message hlookup who payload
  | replay replayed =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact execution.native.pool.lookup_replay_of_some id message hlookup who replayed
  | wait =>
      simp only [playerStep, PlayerCommand.toAction, advance, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact hlookup

/-- Player steps preserve every local inbox. -/
theorem playerStep_inbox
    (who observer : Principal) (execution next : app.PolicyExecution)
    (command : app.PlayerCommand)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.native.pool.inbox observer = execution.native.pool.inbox observer := by
  cases command with
  | privateCommand registration =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | submit payload =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | replay replayed =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      unfold MessagePool.replay
      split <;> rfl
  | wait =>
      simp only [playerStep, PlayerCommand.toAction, advance, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      rfl

/-- Arbitrary randomized policies preserve a pending message across every
supported player-only invocation sequence. -/
theorem runPolicies_playerOnly_pending_lookup
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (henvironment : Invocation.environment ∉ schedule)
    (execution next : app.PolicyExecution)
    (id : MessageId Principal) (message : Message Principal app.Payload)
    (hlookup : execution.native.pool.lookup id = some message)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    next.native.pool.lookup id = some message := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hlookup
  | cons invocation rest ih =>
      have hrest : Invocation.environment ∉ rest := fun hmem =>
        henvironment (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | environment => exact False.elim (henvironment List.mem_cons_self)
      | player who =>
          simp only [runPolicies, invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
          obtain ⟨middle, ⟨command, _, hstep⟩, hnext⟩ := hnext
          exact ih hrest middle (app.playerStep_pending_lookup who execution middle command
            id message hlookup hstep) hnext

/-- Arbitrary randomized policies preserve a recipient's inbox across every
supported player-only invocation sequence. -/
theorem runPolicies_playerOnly_inbox
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (henvironment : Invocation.environment ∉ schedule)
    (observer : Principal) (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    next.native.pool.inbox observer = execution.native.pool.inbox observer := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | cons invocation rest ih =>
      have hrest : Invocation.environment ∉ rest := fun hmem =>
        henvironment (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | environment => exact False.elim (henvironment List.mem_cons_self)
      | player who =>
          simp only [runPolicies, invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
          obtain ⟨middle, ⟨command, _, hstep⟩, hnext⟩ := hnext
          exact (ih hrest middle hnext).trans
            (app.playerStep_inbox who observer execution middle command hstep)

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_playerOnly_pending_lookup'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_playerOnly_pending_lookup

/-- info: 'Interaction.MessageApplication.runPolicies_playerOnly_inbox'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_playerOnly_inbox

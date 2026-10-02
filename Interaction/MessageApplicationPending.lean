/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Pending messages across adversarial player reactions

A characterization of the model rather than a step in the tower: no Vegas
capstone reaches these, and they are here to say what the host permits. -/

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
      simp only [playerStep, PlayerCommand.toAction, advance, step, PMF.pure_bind,
        PMF.mem_support_pure_iff _ _] at hnext
      subst next
      exact hlookup
  | submit payload =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, PMF.pure_bind,
        PMF.mem_support_pure_iff _ _] at hnext
      subst next
      exact execution.native.pool.lookup_submit_of_some id message hlookup who payload
  | wait =>
      simp only [playerStep, PlayerCommand.toAction, advance, PMF.pure_bind,
        PMF.mem_support_pure_iff _ _] at hnext
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
      simp only [playerStep, PlayerCommand.toAction, advance, step, PMF.pure_bind,
        PMF.mem_support_pure_iff _ _] at hnext
      subst next
      rfl
  | submit payload =>
      simp only [playerStep, PlayerCommand.toAction, advance, step, PMF.pure_bind,
        PMF.mem_support_pure_iff _ _] at hnext
      subst next
      rfl
  | wait =>
      simp only [playerStep, PlayerCommand.toAction, advance, PMF.pure_bind,
        PMF.mem_support_pure_iff _ _] at hnext
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
      simp only [runPolicies, PMF.mem_support_pure_iff _ _] at hnext
      subst next
      exact hlookup
  | cons invocation rest ih =>
      have hrest : Invocation.environment ∉ rest := fun hmem =>
        henvironment (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | environment => exact False.elim (henvironment List.mem_cons_self)
      | player who =>
          simp only [runPolicies, invoke, PMF.support_bind, Set.mem_iUnion] at hnext
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
      simp only [runPolicies, PMF.mem_support_pure_iff _ _] at hnext
      subst next
      rfl
  | cons invocation rest ih =>
      have hrest : Invocation.environment ∉ rest := fun hmem =>
        henvironment (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | environment => exact False.elim (henvironment List.mem_cons_self)
      | player who =>
          simp only [runPolicies, invoke, PMF.support_bind, Set.mem_iUnion] at hnext
          obtain ⟨middle, ⟨command, _, hstep⟩, hnext⟩ := hnext
          exact (ih hrest middle hnext).trans
            (app.playerStep_inbox who observer execution middle command hstep)

end Interaction.MessageApplication

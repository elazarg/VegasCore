/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyInvariant

/-! # Message provenance without delivery

If delivery is disabled, inboxes stay empty. A replay may nevertheless append
an envelope authored by another principal to the broadcaster's sent history.
Such a replay is possible only when that envelope was already public in the
ledger, so sent history must not be interpreted as authorship.
-/

noncomputable section

namespace Interaction.MessagePool

universe uPrincipal uPayload

variable {Principal : Type uPrincipal} {Payload : Type uPayload}

/-- The pool invariant left by executions which never perform delivery. -/
def NoDeliveryProvenance (pool : MessagePool Principal Payload) : Prop :=
  (∀ who, pool.inbox who = []) ∧
  ∀ who message, message ∈ pool.sent who → message.sender ≠ who →
    message ∈ pool.ledger

@[simp] theorem noDeliveryProvenance_empty :
    NoDeliveryProvenance (MessagePool.empty Principal Payload) := by
  simp [NoDeliveryProvenance, MessagePool.empty]

theorem NoDeliveryProvenance.submit [DecidableEq Principal]
    {pool : MessagePool Principal Payload} (h : pool.NoDeliveryProvenance)
    (sender : Principal) (payload : Payload) :
    (pool.submit sender payload).2.NoDeliveryProvenance := by
  rcases h with ⟨hinbox, hsent⟩
  constructor
  · exact hinbox
  · intro who message hmem hother
    simp only [MessagePool.submit] at hmem
    split at hmem
    · rename_i hwho
      subst who
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · exact hsent sender message hold hother
      · subst message
        exact (hother rfl).elim
    · exact hsent who message hmem hother

theorem NoDeliveryProvenance.replay [DecidableEq Principal]
    {pool : MessagePool Principal Payload} (h : pool.NoDeliveryProvenance)
    (broadcaster : Principal) (id : MessageId Principal) :
    (pool.replay broadcaster id).state.NoDeliveryProvenance := by
  rcases h with ⟨hinbox, hsent⟩
  unfold MessagePool.replay
  split
  · rename_i message hknown
    constructor
    · exact hinbox
    · intro who candidate hmem hother
      by_cases hwho : who = broadcaster
      · subst who
        simp only [if_pos, List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hold | hnew
        · exact hsent broadcaster candidate hold hother
        · subst candidate
          have hmemKnown := MessagePool.View.known?_mem
            (pool.observe broadcaster) id message hknown
          simp only [MessagePool.observe, List.mem_append] at hmemKnown
          rcases hmemKnown with (hsentMem | hinboxMem) | hledgerMem
          · exact hsent broadcaster message hsentMem hother
          · simp [hinbox broadcaster] at hinboxMem
          · exact hledgerMem
      · simp only [if_neg hwho] at hmem
        exact hsent who candidate hmem hother
  · exact ⟨hinbox, hsent⟩

theorem NoDeliveryProvenance.includePending [DecidableEq Principal]
    {pool : MessagePool Principal Payload} (h : pool.NoDeliveryProvenance)
    (id : MessageId Principal) :
    (pool.includePending id).state.NoDeliveryProvenance := by
  rcases h with ⟨hinbox, hsent⟩
  constructor
  · intro who
    rw [MessagePool.include_preserves_inbox, hinbox]
  · intro who message hmem hother
    rw [MessagePool.include_preserves_sent] at hmem
    have hledger := hsent who message hmem hother
    unfold MessagePool.includePending
    split
    · simp only [List.mem_append]
      exact Or.inl hledger
    · exact hledger

/-- With empty inboxes, every known foreign-authored envelope is necessarily
already public. This includes envelopes retained in sent history by replay. -/
theorem NoDeliveryProvenance.known_foreign_mem_ledger [DecidableEq Principal]
    {pool : MessagePool Principal Payload} (h : pool.NoDeliveryProvenance)
    (who : Principal) (id : MessageId Principal) (message : Message Principal Payload)
    (hknown : (pool.observe who).known? id = some message)
    (hforeign : message.sender ≠ who) : message ∈ pool.ledger := by
  have hmem := MessagePool.View.known?_mem (pool.observe who) id message hknown
  simp only [MessagePool.observe, List.mem_append] at hmem
  rcases hmem with (hsent | hinbox) | hledger
  · exact h.2 who message hsent hforeign
  · simp [h.1 who] at hinbox
  · exact hledger

end Interaction.MessagePool

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- An environment policy disables delivery at every execution view. -/
def EnvironmentPolicy.NoDelivery (environment : app.EnvironmentPolicy) : Prop :=
  ∀ history view observer id,
    MessageInterface.EnvironmentPolicyCommand.deliver observer id ∉
      (environment history view).support

/-- Arbitrary player policies preserve no-delivery provenance when the
environment policy has no supported delivery command. -/
theorem runPolicies_noDeliveryProvenance [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hnoDelivery : environment.NoDelivery)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hinvariant : execution.native.pool.NoDeliveryProvenance)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    next.native.pool.NoDeliveryProvenance := by
  apply app.runPolicies_execution_invariant
    (fun current => current.native.pool.NoDeliveryProvenance) players environment
    ?_ ?_ schedule execution next hinvariant hnext
  · intro current who command final hcurrent _ hfinal
    have hnative : final.native ∈
        ((app.playerStep who current command).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨final, hfinal, rfl⟩
    rw [app.playerStep_native] at hnative
    cases command with
    | privateCommand privateCommand =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rwa [hnative]
    | submit payload =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact hcurrent.submit who payload
    | replay id =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact hcurrent.replay who id
    | wait =>
        simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at hnative
        rwa [hnative]
  · intro current command final hcurrent hcommand hfinal
    have hnative : final.native ∈
        ((app.environmentPolicyStep current command).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨final, hfinal, rfl⟩
    rw [app.environmentStep_native] at hnative
    cases command with
    | deliver observer id =>
        exact (hnoDelivery current.environmentHistory
          (State.environmentView app current.native) observer id hcommand).elim
    | «include» id =>
        simp only [EnvironmentPolicyCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative, includePending_pool]
        exact hcurrent.includePending id
    | application applicationCommand =>
        simp only [EnvironmentPolicyCommand.toAction, step, FinDist.support_map,
          Set.mem_image] at hnative
        obtain ⟨applicationNext, _, hnative⟩ := hnative
        rwa [← hnative]
    | wait =>
        simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at hnative
        rwa [hnative]

end Interaction.MessageApplication

/-- info:
'Interaction.MessageApplication.runPolicies_noDeliveryProvenance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_noDeliveryProvenance

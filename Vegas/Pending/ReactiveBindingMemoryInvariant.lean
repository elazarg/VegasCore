/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingContinuation
import Vegas.Pending.ReactiveBindingShadowInvariant

/-! # Binding-memory preservation through retained execution

The repair implementation records only the focal player's own bindings. Its
legal-response fallback changes the emitted action without changing the
proposed memory. The same invariant therefore holds through every supported
joint execution, against arbitrary opponents and schedulers.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (menu : (runtime.reactiveApplication leaks).ResponseMenu)

/-- Both a repaired response and the legal-response fallback retain the
invariant that all remembered completions belong to the owner's bindings. -/
theorem retainedImplementation_response_ownBindings (owner : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (memory : BindingMemory runtime leaks) (onlyBindings : memory.shadow.OwnBindings owner)
    (input : List (runtime.reactiveApplication leaks).PlayerEntry ×
      (runtime.reactiveApplication leaks).PlayerView)
    (next : (runtime.reactiveApplication leaks).Action × BindingMemory runtime leaks)
    (reached : next ∈ ((retainedImplementation runtime leaks menu owner reference policy).respond
      memory input).support) : next.2.shadow.OwnBindings owner := by
  obtain ⟨proposed, supported, rfl⟩ := FinDist.support_map .. ▸ reached
  obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ supported
  dsimp only
  split
  · exact onlyBindings
  · exact repairResponse_ownBindings runtime leaks owner memory onlyBindings input.2 response

/-- A passive command or foreign response leaves private memory untouched;
a focal response preserves the own-binding invariant by construction. -/
theorem retainedImplementation_resume_ownBindings (owner : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (actor : Option Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memory : BindingMemory runtime leaks) (onlyBindings : memory.shadow.OwnBindings owner)
    (next : (runtime.reactiveApplication leaks).Execution × BindingMemory runtime leaks)
    (reached : next ∈ ((retainedImplementation runtime leaks menu owner reference policy).resume
      owner players actor execution memory).support) : next.2.shadow.OwnBindings owner := by
  cases actor with
  | none =>
      cases FinDist.mem_support_pure.mp reached
      exact onlyBindings
  | some who =>
      by_cases acting : who = owner
      · subst who
        simp only [ReactiveApplication.Implementation.resume, ite_true] at reached
        obtain ⟨response, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        exact retainedImplementation_response_ownBindings runtime leaks menu owner reference
          policy memory onlyBindings _ response supported
      · simp only [ReactiveApplication.Implementation.resume, acting, ite_false] at reached
        obtain ⟨_, _, rfl⟩ := FinDist.support_map .. ▸ reached
        exact onlyBindings

/-- The actual joint runner preserves own-binding memory at every supported
prefix. No assumption on opponent actions, runtime state, or audit cleanliness
is needed for this private-memory invariant. -/
theorem retainedImplementation_runJoint_ownBindings (owner : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memory : BindingMemory runtime leaks) (onlyBindings : memory.shadow.OwnBindings owner)
    (next : (runtime.reactiveApplication leaks).Execution × BindingMemory runtime leaks)
    (reached : next ∈ ((retainedImplementation runtime leaks menu owner reference policy).runJoint
      owner players scheduler count execution memory).support) :
    next.2.shadow.OwnBindings owner := by
  induction count generalizing execution memory with
  | zero =>
      cases FinDist.mem_support_pure.mp reached
      exact onlyBindings
  | succ count ih =>
      obtain ⟨middle, moved, continued⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
      obtain ⟨activated, _, responded⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ dispatched)
      exact ih middle.1 middle.2
        (retainedImplementation_resume_ownBindings runtime leaks menu owner reference policy
          players (command.actor? (runtime.reactiveApplication leaks)) activated memory
            onlyBindings middle responded) continued

end Vegas.EventGraphRuntime.BindingMemory

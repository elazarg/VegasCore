/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationCursor

/-! # Exact response counts at the native decision sites

The fixed service grants Bob one earlier response before his binding and two
before his opening. These are counts of unrestricted network responses.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def nativeResponseCount (who : Player) (plan : List (ServiceInstruction nativeGraph)) : Nat :=
  (plan.map fun instruction => if nativeInstructionPlayer instruction = some who then 1 else 0).sum

private theorem dispatch_recall_count (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution) (command : nativeApp.Command) (who : Player)
    (reached : next ∈ (nativeApp.dispatch players command execution).support) :
    (next.recall who).length = (execution.recall who).length +
      if command.actor? nativeApp = some who then 1 else 0 := by
  obtain ⟨observed, observedMem, resumed⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have same := nativeApp.environmentStep_recall execution observed command observedMem
  cases actor : command.actor? nativeApp with
  | none =>
      simp only [actor, ReactiveApplication.resume, FinDist.mem_support_pure] at resumed
      subst next
      simp only [same, reduceCtorEq, ↓reduceIte, Nat.add_zero]
  | some owner =>
      rw [actor] at resumed
      obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ resumed
      by_cases identical : who = owner
      · subst who
        have count := congrArg List.length (nativeApp.respond_actions observed owner response)
        simp only [List.length_map, List.length_append, List.length_singleton] at count
        simpa only [same, ↓reduceIte] using count
      · rw [nativeApp.respond_recall_other observed owner who identical response, same]
        simp only [Option.some.injEq, Ne.symm identical, ↓reduceIte, Nat.add_zero]

theorem native_step_recall_count (players : Player → nativeApp.Policy)
    (instruction : ServiceInstruction nativeGraph) (execution next : nativeApp.Execution)
    (who : Player)
    (reached : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      instruction execution).support) :
    (next.recall who).length = (execution.recall who).length +
      if nativeInstructionPlayer instruction = some who then 1 else 0 := by
  obtain ⟨command, commandMem, dispatched⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have count := dispatch_recall_count players execution next command who dispatched
  rw [native_instruction_actor instruction _ _ command commandMem] at count
  exact count

theorem native_plan_recall_count (players : Player → nativeApp.Policy)
    (plan : List (ServiceInstruction nativeGraph)) (execution next : nativeApp.Execution)
    (who : Player)
    (reached : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      plan execution).support) :
    (next.recall who).length = (execution.recall who).length + nativeResponseCount who plan := by
  induction plan generalizing execution with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      simp [nativeResponseCount]
  | cons instruction rest ih =>
      obtain ⟨middle, first, later⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      rw [ih middle later, native_step_recall_count players instruction execution middle who first]
      simp only [nativeResponseCount, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The count is valid at every legal history displaying the current grant. -/
theorem native_decision_recall_count (event : nativeGraph.EventId) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (who : Player)
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some event) (observer : Player) :
    (control.execution.recall observer).length =
      nativeResponseCount observer (nativeBeforeResponse event) := by
  obtain ⟨owner, position⟩ := native_decision_cursor event control trace who active granted
  obtain ⟨_, prior, priorMem, observed⟩ :=
    native_decision_predecessor event control trace (owner ▸ active) position
  rw [nativeApp.environmentStep_recall prior control.execution _ observed]
  simpa only [nativeRoot, ReactiveApplication.Execution.initial, List.length_nil,
    Nat.zero_add] using native_plan_recall_count nativeMenu.uniformResponses
      (nativeBeforeResponse event) nativeRoot prior observer priorMem

theorem native_bob_binding_recall (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding) :
    (control.execution.recall bob).length = 1 :=
  native_decision_recall_count bobBinding control trace bob active granted bob

theorem native_bob_opening_recall (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobPublication) :
    (control.execution.recall bob).length = 2 :=
  native_decision_recall_count bobPublication control trace bob active granted bob

theorem native_alice_opening_recall (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (granted : control.execution.application.serviceGrant = some alicePublication) :
    (control.execution.recall alice).length = 2 :=
  native_decision_recall_count alicePublication control trace alice active granted alice

end VegasTests.SelectiveAssociation

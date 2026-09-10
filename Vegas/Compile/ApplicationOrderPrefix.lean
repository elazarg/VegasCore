/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationPlanCoverage
import Vegas.Compile.ApplicationCompletion
import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationOrderTimeouts
import Vegas.Compile.ApplicationResolvedBindings
import Vegas.Compile.ApplicationPlanAllocation
import Interaction.MessageInvariant
import Interaction.MessageApplicationPolicies

/-! # Completed instruction prefixes under ordered admission

The completion invariant records which emitted instruction blocks have finished.
It is independent of player strategies, source environments, and service history.
The covered-node lists must be disjoint; generated plans prove this condition.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
/-- An active address is unfinished, even for images with aliased addresses. -/
theorem activeAddress?_not_done (image : ApplicationImage P L) (memory : Memory P L)
    (address : Nat) (hactive : image.activeAddress? memory = some address) :
    memory.done address = false := by
  unfold activeAddress? at hactive
  cases hfound : image.instructions.find? (fun instruction => !memory.done instruction.address)
      with
  | none => simp [hfound] at hactive
  | some instruction =>
      have haddress : instruction.address = address := by simpa [hfound] using hactive
      have hundone := List.find?_some hfound
      simpa only [haddress, Bool.not_eq_true'] using hundone

/-- An accepted ordered message finishes the formerly active address.
Neither source refinement nor unique instruction addresses are needed. -/
theorem ordered_handle_resolves (image : ApplicationImage P L)
    (before after : State P L) (message : Message P (Payload P L))
    (hafter : image.orderedApplication.handle before message = some after) :
    ∃ address, image.activeAddress? before.memory = some address ∧
      after.memory.done address = true ∧ image.activeAddress? after.memory ≠ some address := by
  change (if image.admitsMessage before.memory message then image.handle before message
    else none) = some after at hafter
  split at hafter
  · rename_i hadmitted
    obtain ⟨instruction, _, haddress, hdone⟩ :=
      image.handle_completion_effect before after message hafter
    have hactive : image.activeAddress? before.memory = some instruction.address := by
      change image.admitsMessage before.memory message = true at hadmitted
      simp only [admitsMessage, haddress] at hadmitted
      exact (admitsAddress_iff _ _ _).mp hadmitted
    have hresolved : after.memory.done instruction.address = true := by
      rw [hdone]
      simp only [instruction.address_mem_coveredNodes, decide_true, Bool.true_or]
    refine ⟨instruction.address, hactive, hresolved, ?_⟩
    intro hstillActive
    have := image.activeAddress?_not_done after.memory instruction.address hstillActive
    rw [hresolved] at this
    contradiction
  · contradiction

/-- Completed nodes are exactly the blocks of an initial instruction segment.
This is a completion invariant, not a source-state or strategy correspondence. -/
def CompletedPrefix (image : ApplicationImage P L) (memory : Memory P L) : Prop :=
  ∃ before rest, image.instructions = before ++ rest ∧
    ∀ node, memory.done node = true ↔
      node ∈ before.flatMap ApplicationInstruction.coveredNodes

theorem CompletedPrefix.initial (image : ApplicationImage P L) (graph : Graph P L) :
    image.CompletedPrefix (Memory.initial graph) := by
  refine ⟨[], image.instructions, rfl, ?_⟩
  intro node
  simp [Memory.initial]

omit [DecidableEq P] in
/-- Changes outside completion flags preserve the same instruction prefix. -/
theorem CompletedPrefix.of_done_eq {image : ApplicationImage P L}
    {memory next : Memory P L} (hcompleted : image.CompletedPrefix memory)
    (hdone : next.done = memory.done) : image.CompletedPrefix next := by
  obtain ⟨before, rest, himage, hprefix⟩ := hcompleted
  exact ⟨before, rest, himage, fun node => hdone ▸ hprefix node⟩

omit [DecidableEq P] in
/-- Exact consecutive code coverage turns the instruction prefix into a
numeric graph-node prefix, including absence of stray completion flags. -/
theorem CompletedPrefix.done_iff_lt {image : ApplicationImage P L}
    {memory : Memory P L} (hcompleted : image.CompletedPrefix memory)
    (count : Nat)
    (hcoverage : image.instructions.flatMap ApplicationInstruction.coveredNodes =
      List.range count) :
    ∃ bound ≤ count, ∀ node, memory.done node = true ↔ node < bound := by
  obtain ⟨before, rest, himage, hdone⟩ := hcompleted
  have hprefix : before.flatMap ApplicationInstruction.coveredNodes <+: List.range count := by
    refine ⟨rest.flatMap ApplicationInstruction.coveredNodes, ?_⟩
    simpa only [himage, List.flatMap_append] using hcoverage
  have hlength : (before.flatMap ApplicationInstruction.coveredNodes).length ≤ count := by
    simpa only [List.length_range] using hprefix.length_le
  have hbefore := List.prefix_iff_eq_take.mp hprefix
  rw [List.take_range, Nat.min_eq_left hlength] at hbefore
  refine ⟨_, hlength, ?_⟩
  intro node
  rw [hdone, hbefore, List.mem_range]
  simp only [List.length_range]

omit [DecidableEq P] in
/-- Completing the selected block advances the prefix by exactly one emitted
instruction. Disjoint node coverage rules out aliases between instructions. -/
theorem CompletedPrefix.resolve {image : ApplicationImage P L}
    {memory next : Memory P L} (hcompleted : image.CompletedPrefix memory)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (instruction : ApplicationInstruction P L) (hmem : instruction ∈ image.instructions)
    (hactive : image.activeAddress? memory = some instruction.address)
    (hnext : ∀ node, next.done node =
      (decide (node ∈ instruction.coveredNodes) || memory.done node)) :
    image.CompletedPrefix next := by
  obtain ⟨before, rest, himage, hprefix⟩ := hcompleted
  have hbefore : ∀ prior ∈ before, memory.done prior.address = true := by
    intro prior hprior
    exact (hprefix _).mpr
      (List.mem_flatMap.mpr ⟨prior, hprior, prior.address_mem_coveredNodes⟩)
  have hselected : (ApplicationImage.mk rest).activeAddress? memory =
      some instruction.address := by
    change (ApplicationImage.mk image.instructions).activeAddress? memory = _ at hactive
    rw [himage, activeAddress?_after_completed before ⟨rest⟩ memory hbefore] at hactive
    exact hactive
  cases rest with
  | nil => simp [activeAddress?] at hselected
  | cons head tail =>
      have hhead : memory.done head.address = false := by
        apply Bool.eq_false_iff.mpr
        intro hdone
        have hprior := (hprefix _).mp hdone
        have hdisjoint :
            (before.flatMap ApplicationInstruction.coveredNodes ++
              (head :: tail).flatMap ApplicationInstruction.coveredNodes).Nodup := by
          simpa only [himage, List.flatMap_append] using hnodup
        exact (List.nodup_append.mp hdisjoint).2.2 _ hprior _
          (List.mem_flatMap.mpr
            ⟨head, List.mem_cons_self, head.address_mem_coveredNodes⟩) rfl
      rw [activeAddress?_head head tail memory hhead] at hselected
      have haddress : head.address = instruction.address := Option.some.inj hselected
      have hheadMem : head ∈ image.instructions := by
        rw [himage]
        exact List.mem_append_right _ List.mem_cons_self
      have heq : instruction = head := by
        by_contra hne
        let : Std.Symm (fun a b : ApplicationInstruction P L =>
            List.Disjoint a.coveredNodes b.coveredNodes) :=
          ⟨fun _ _ h => h.symm⟩
        have hdisjoint := (List.nodup_flatMap.mp hnodup).2.forall hmem hheadMem hne
        apply (List.disjoint_left.mp hdisjoint) instruction.address_mem_coveredNodes
        exact haddress ▸ head.address_mem_coveredNodes
      subst instruction
      refine ⟨before ++ [head], tail, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using himage
      · intro node
        rw [hnext]
        simp only [Bool.or_eq_true, decide_eq_true_eq, hprefix,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append]
        exact or_comm

/-- Every accepted ordered message advances a completion prefix by its actual
instruction block. Expiry follows the same invariant as ordinary resolution. -/
theorem ordered_handle_completedPrefix (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (before after : State P L) (message : Message P (Payload P L))
    (hcompleted : image.CompletedPrefix before.memory)
    (hafter : image.orderedApplication.handle before message = some after) :
    image.CompletedPrefix after.memory := by
  change (if image.admitsMessage before.memory message then image.handle before message
    else none) = some after at hafter
  split at hafter
  · rename_i hadmitted
    obtain ⟨instruction, hmem, haddress, hdone⟩ :=
      image.handle_completion_effect before after message hafter
    have hactive : image.activeAddress? before.memory = some instruction.address := by
      change image.admitsMessage before.memory message = true at hadmitted
      simp only [admitsMessage, haddress] at hadmitted
      exact (admitsAddress_iff _ _ _).mp hadmitted
    exact hcompleted.resolve hnodup instruction hmem hactive hdone
  · contradiction

/-- Chance completion advances one block; clock advancement and disabled
chance requests preserve the current prefix. -/
theorem ordered_environment_completedPrefix (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (before after : State P L) (command : EnvironmentCommand)
    (hcompleted : image.CompletedPrefix before.memory)
    (hafter : after ∈ (image.orderedApplication.environmentStep before command).support) :
    image.CompletedPrefix after.memory := by
  cases command with
  | advance clock =>
      rw [ordered_advance, FinDist.mem_support_pure] at hafter
      subst after
      exact hcompleted.of_done_eq rfl
  | sample address =>
      by_cases hactive : image.activeAddress? before.memory = some address
      · rw [ordered_sample_eq image before address hactive] at hafter
        rcases image.sample_completion_effect before after address hafter with rfl | heffect
        · exact hcompleted
        · obtain ⟨code, hlookup, hmem, hdone⟩ := heffect
          have haddress : code.node = address := by
            have hfound := List.find?_some hlookup
            simpa only [ApplicationInstruction.address, beq_iff_eq] using hfound
          exact hcompleted.resolve hnodup (.sample code) hmem
            (by simpa only [ApplicationInstruction.address, haddress] using hactive) hdone
      · rw [ordered_sample_inactive image before address hactive,
          FinDist.mem_support_pure] at hafter
        subst after
        exact hcompleted

/-- Arbitrary native action lists preserve ordered completion, without
conditions on message contents, acceptance, or service progress. -/
theorem ordered_run_completedPrefix (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (before after : image.orderedApplication.State)
    (actions : List image.orderedApplication.Action)
    (hcompleted : image.CompletedPrefix before.application.memory)
    (hafter : after ∈ (image.orderedApplication.run actions before).support) :
    image.CompletedPrefix after.application.memory := by
  exact image.orderedApplication.run_application_invariant
    (fun state => image.CompletedPrefix state.memory)
    (fun state who command h => by cases command; exact h.of_done_eq rfl)
    (fun state message next h hnext =>
      image.ordered_handle_completedPrefix hnodup state next message h hnext)
    (fun state command next h hnext =>
      image.ordered_environment_completedPrefix hnodup state next command h hnext)
    before after actions hcompleted hafter

/-- The completion invariant applies to arbitrary randomized players and
environment policies, not only the compiled reference profile. -/
theorem ordered_runPolicies_completedPrefix (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (players : P → image.orderedApplication.PlayerPolicy)
    (environment : image.orderedApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (before after : image.orderedApplication.PolicyExecution)
    (hcompleted : image.CompletedPrefix before.native.application.memory)
    (hafter : after ∈
      (image.orderedApplication.runPolicies players environment schedule before).support) :
    image.CompletedPrefix after.native.application.memory := by
  exact image.orderedApplication.runPolicies_application_invariant
    (fun state => image.CompletedPrefix state.memory)
    (fun state who command h => by cases command; exact h.of_done_eq rfl)
    (fun state message next h hnext =>
      image.ordered_handle_completedPrefix hnodup state next message h hnext)
    (fun state command next h hnext =>
      image.ordered_environment_completedPrefix hnodup state next command h hnext)
    players environment schedule before after hcompleted hafter

end Vegas.ApplicationImage

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- With either or both timeout families enabled, arbitrary supported policy
runs complete an initial segment of compiler nodes and retain the disposition
of every completed binding. All static separation premises follow from the
generated plan. This is safety, not termination or source-strategy simulation. -/
theorem ordered_timeout_runPolicies_invariants (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (players : P → (plan.image deadlineOf).orderedApplication.PlayerPolicy)
    (environment : (plan.image deadlineOf).orderedApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (after : (plan.image deadlineOf).orderedApplication.PolicyExecution)
    (hafter : after ∈ ((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).orderedApplication.runPolicies
      players environment schedule (plan.initialExecution deadlineOf)).support) :
    (∃ bound ≤ (compile source.core).graph.nodeCount,
      ∀ node, after.native.application.memory.done node = true ↔ node < bound) ∧
    (((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).ResolvedBindings after.native.application := by
  let decorated := ((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts choice
  have hcoverage : decorated.instructions.flatMap ApplicationInstruction.coveredNodes =
      List.range (compile source.core).graph.nodeCount := by
    rw [ApplicationImage.coveredNodes_withChoiceTimeouts,
      ApplicationImage.coveredNodes_withBindingTimeouts]
    simpa only [image, BuildState.fromInitial, List.length_nil, List.range_zero,
      List.nil_append, compile, BuildResult.graph, Graph.nodeCount] using
        plan.coveredNodes_eq_range deadlineOf
  have hnodup : (decorated.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup := by
    rw [hcoverage]
    exact List.nodup_range
  have hcompleted := decorated.ordered_runPolicies_completedPrefix
    hnodup players environment schedule
    (plan.initialExecution deadlineOf) after
    (ApplicationImage.CompletedPrefix.initial _ _) hafter
  refine ⟨hcompleted.done_iff_lt _ hcoverage, ?_⟩
  apply decorated.ordered_runPolicies_resolvedBindings
    (initialState source.core.Γ source.core.env source.core.wctx).initialFields.length
    hnodup _ players environment schedule (plan.initialExecution deadlineOf) after
    (ApplicationImage.ResolvedBindings.initial _ _) hafter
  apply ApplicationImage.instructions_allocated_withChoiceTimeouts
  apply ApplicationImage.instructions_allocated_withBindingTimeouts
  exact plan.instructions_allocated deadlineOf

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationImage.CompletedPrefix.resolve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.CompletedPrefix.resolve

/-- info: 'Vegas.ApplicationImage.ordered_runPolicies_completedPrefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_runPolicies_completedPrefix

/-- info: 'Vegas.ApplicationPlan.ordered_timeout_runPolicies_invariants' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ordered_timeout_runPolicies_invariants

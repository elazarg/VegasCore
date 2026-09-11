/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationDeadlines
import Vegas.Compile.ApplicationOrderPrefix
import Vegas.Compile.ApplicationResolvedBindings

/-! # Static and state invariants under deadline replacement

Replacing absolute deadline metadata preserves instruction coverage, canonical
allocation, completion prefixes, and resolved binding dispositions. These
facts concern the same public memory and application state; they impose no
clock, service, or policy premise.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
theorem coveredNodes_withDeadlines (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) :
    (image.withDeadlines deadlineOf).instructions.flatMap
        ApplicationInstruction.coveredNodes =
      image.instructions.flatMap ApplicationInstruction.coveredNodes := by
  simp [withDeadlines, List.flatMap_map]

omit [DecidableEq P] in
theorem allocatedFields_withDeadlines (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) :
    (image.withDeadlines deadlineOf).instructions.flatMap
        ApplicationInstruction.allocatedFields =
      image.instructions.flatMap ApplicationInstruction.allocatedFields := by
  simp [withDeadlines, List.flatMap_map]

omit [DecidableEq P] in
theorem instructions_allocated_withDeadlines (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields) :
    ∀ instruction ∈ (image.withDeadlines deadlineOf).instructions,
      instruction.AllocatedAt initialFields := by
  intro instruction hmem
  simp only [withDeadlines, List.mem_map] at hmem
  obtain ⟨original, horiginal, rfl⟩ := hmem
  exact (ApplicationInstruction.withDeadlines_allocatedAt
    deadlineOf initialFields original).2 (hallocated original horiginal)

omit [DecidableEq P] in
private theorem completedPrefix_withDeadlines_forward
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (memory : Memory P L) (hcompleted : image.CompletedPrefix memory) :
    (image.withDeadlines deadlineOf).CompletedPrefix memory := by
  obtain ⟨before, rest, himage, hdone⟩ := hcompleted
  refine ⟨before.map (ApplicationInstruction.withDeadlines deadlineOf),
    rest.map (ApplicationInstruction.withDeadlines deadlineOf), ?_, ?_⟩
  · change image.instructions.map (ApplicationInstruction.withDeadlines deadlineOf) = _
    rw [himage, List.map_append]
  · intro node
    rw [hdone, List.flatMap_map]
    simp

omit [DecidableEq P] in
private theorem completedPrefix_withDeadlines_backward
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (memory : Memory P L)
    (hcompleted : (image.withDeadlines deadlineOf).CompletedPrefix memory) :
    image.CompletedPrefix memory := by
  obtain ⟨before, rest, himage, hdone⟩ := hcompleted
  change image.instructions.map (ApplicationInstruction.withDeadlines deadlineOf) =
    before ++ rest at himage
  obtain ⟨originalBefore, originalRest, horiginal, hbefore, _⟩ :=
    List.map_eq_append_iff.mp himage
  refine ⟨originalBefore, originalRest, horiginal, ?_⟩
  intro node
  rw [hdone, ← hbefore, List.flatMap_map]
  simp

omit [DecidableEq P] in
/-- Completion is a prefix of the same instruction blocks before and after
deadline replacement. -/
theorem completedPrefix_withDeadlines_iff (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (memory : Memory P L) :
    (image.withDeadlines deadlineOf).CompletedPrefix memory ↔
      image.CompletedPrefix memory :=
  ⟨completedPrefix_withDeadlines_backward image deadlineOf memory,
    completedPrefix_withDeadlines_forward image deadlineOf memory⟩

omit [DecidableEq P] in
private theorem resolvedBindings_withDeadlines_forward
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (state : State P L) (hresolved : image.ResolvedBindings state) :
    (image.withDeadlines deadlineOf).ResolvedBindings state := by
  intro code hcode hdone
  change (ApplicationInstruction.bind code : ApplicationInstruction P L) ∈
    image.instructions.map (ApplicationInstruction.withDeadlines deadlineOf) at hcode
  obtain ⟨instruction, hinstruction, heq⟩ := List.mem_map.mp hcode
  cases instruction with
  | sample sample => cases heq
  | publicChoice choice => cases heq
  | conditional conditional => cases heq
  | bind original =>
      simp only [ApplicationInstruction.withDeadlines] at heq
      cases heq
      simpa only using hresolved original hinstruction hdone

omit [DecidableEq P] in
private theorem resolvedBindings_withDeadlines_backward
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (state : State P L) (hresolved : (image.withDeadlines deadlineOf).ResolvedBindings state) :
    image.ResolvedBindings state := by
  intro code hcode hdone
  let retimed : BindingCode P L :=
    { code with timeout := code.timeout.map fun timeout =>
        { timeout with deadline := deadlineOf code.node } }
  have hretimed : (ApplicationInstruction.bind retimed : ApplicationInstruction P L) ∈
      (image.withDeadlines deadlineOf).instructions := by
    change .bind retimed ∈
      image.instructions.map (ApplicationInstruction.withDeadlines deadlineOf)
    apply List.mem_map.mpr
    exact ⟨.bind code, hcode, rfl⟩
  have hdoneRetimed : state.memory.done retimed.node = true := by
    exact hdone
  simpa only [retimed] using hresolved retimed hretimed hdoneRetimed

omit [DecidableEq P] in
/-- Binding resolution refers only to binding node, field, owner, and slot;
deadline metadata is irrelevant. -/
theorem resolvedBindings_withDeadlines_iff (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (state : State P L) :
    (image.withDeadlines deadlineOf).ResolvedBindings state ↔
      image.ResolvedBindings state :=
  ⟨resolvedBindings_withDeadlines_backward image deadlineOf state,
    resolvedBindings_withDeadlines_forward image deadlineOf state⟩

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.completedPrefix_withDeadlines_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.completedPrefix_withDeadlines_iff

/-- info: 'Vegas.ApplicationImage.resolvedBindings_withDeadlines_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.resolvedBindings_withDeadlines_iff

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationPlanAllocation

/-! # Absolute-deadline replacement for application images

This pass replaces deadline numbers already present in emitted timeout metadata.
It does not add timeout code and does not give deadlines activation-relative
meaning.
-/

namespace Vegas

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} {L : IExpr}

namespace ApplicationInstruction

/-- Replace each existing absolute deadline using its instruction address. -/
def withDeadlines (deadlineOf : Nat → Nat) :
    ApplicationInstruction P L → ApplicationInstruction P L
  | .sample code => .sample code
  | .bind code => .bind { code with
      timeout := code.timeout.map fun timeout =>
        { timeout with deadline := deadlineOf code.node } }
  | .publicChoice code => .publicChoice { code with
      timeout := code.timeout.map fun timeout =>
        { timeout with deadline := deadlineOf code.endpoint.publicationNode } }
  | .conditional code => .conditional
      { code with endpoint :=
          { code.endpoint with deadline := deadlineOf code.endpoint.publicationNode } }

@[simp] theorem withDeadlines_address (deadlineOf : Nat → Nat)
    (instruction : ApplicationInstruction P L) :
    (instruction.withDeadlines deadlineOf).address = instruction.address := by
  cases instruction <;> rfl

@[simp] theorem withDeadlines_coveredNodes (deadlineOf : Nat → Nat)
    (instruction : ApplicationInstruction P L) :
    (instruction.withDeadlines deadlineOf).coveredNodes = instruction.coveredNodes := by
  cases instruction <;> rfl

@[simp] theorem withDeadlines_allocatedFields (deadlineOf : Nat → Nat)
    (instruction : ApplicationInstruction P L) :
    (instruction.withDeadlines deadlineOf).allocatedFields = instruction.allocatedFields := by
  cases instruction <;> rfl

theorem withDeadlines_allocatedAt (deadlineOf : Nat → Nat)
    (initialFields : Nat) (instruction : ApplicationInstruction P L) :
    (instruction.withDeadlines deadlineOf).AllocatedAt initialFields ↔
      instruction.AllocatedAt initialFields := by
  cases instruction <;> rfl

@[simp] theorem withDeadlines_override (first second : Nat → Nat)
    (instruction : ApplicationInstruction P L) :
    (instruction.withDeadlines first).withDeadlines second =
      instruction.withDeadlines second := by
  cases instruction with
  | sample code | conditional code => rfl
  | bind code | publicChoice code =>
      cases htimeout : code.timeout <;> simp [withDeadlines, htimeout]

end ApplicationInstruction

namespace ApplicationImage

/-- Replace absolute deadlines throughout a finite application image. -/
def withDeadlines (image : ApplicationImage P L) (deadlineOf : Nat → Nat) :
    ApplicationImage P L :=
  ⟨image.instructions.map (ApplicationInstruction.withDeadlines deadlineOf)⟩

@[simp] theorem lookup_withDeadlines (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (address : Nat) :
    (image.withDeadlines deadlineOf).lookup address =
      (image.lookup address).map (ApplicationInstruction.withDeadlines deadlineOf) := by
  simp [lookup, withDeadlines, List.find?_map]

/-- Deadline replacement does not change the chance kernel. -/
theorem sample_withDeadlines (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (state : State P L) (address : Nat) :
    (image.withDeadlines deadlineOf).sample state address = image.sample state address := by
  simp only [sample, lookup_withDeadlines]
  cases image.lookup address with
  | none => rfl
  | some instruction => cases instruction <;> rfl

@[simp] theorem activeAddress?_withDeadlines (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (memory : Memory P L) :
    (image.withDeadlines deadlineOf).activeAddress? memory = image.activeAddress? memory := by
  simp [activeAddress?, withDeadlines, List.find?_map, Function.comp_def]

@[simp] theorem withDeadlines_override (image : ApplicationImage P L)
    (first second : Nat → Nat) :
    (image.withDeadlines first).withDeadlines second = image.withDeadlines second := by
  simp [withDeadlines, List.map_map, Function.comp_def]

end ApplicationImage
end Vegas

/-- info: 'Vegas.ApplicationImage.sample_withDeadlines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.sample_withDeadlines

/-- info: 'Vegas.ApplicationImage.activeAddress?_withDeadlines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.activeAddress?_withDeadlines

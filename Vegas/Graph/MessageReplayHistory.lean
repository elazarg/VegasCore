/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicies

/-! # Cache shapes retained by paired compiled histories

Hidden raw values and remembered disclosure Booleans may differ between runs.
The compiler's preparation/submission control flow depends only on which sites
have already been recorded, so replay retains these flags for every site.
-/

noncomputable section
namespace Vegas.GraphRuntime

open Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L] {Δ : VCtx Player L}
variable {runtime : GraphRuntime Player L Δ}

/-- Cache occupancy and prior submission, without any cached private value. -/
structure CacheShape (left right : List (Entry runtime)) : Prop where
  prepared : ∀ site, (preparedRaw left site).isSome = (preparedRaw right site).isSome
  remembered : ∀ site,
    (rememberedDisclosure left site).isSome = (rememberedDisclosure right site).isSome
  submitted : ∀ site, submittedAt left site = submittedAt right site

namespace CacheShape

theorem refl (history : List (Entry runtime)) : CacheShape history history :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

private theorem isSome_or {α : Type} (left right : Option α) :
    (left.or right).isSome = (left.isSome || right.isSome) := by
  cases left <;> cases right <;> rfl

/-- Paired prefixes and suffixes can be combined without identifying the first
cached value chosen in either history. -/
theorem append {left right leftTail rightTail : List (Entry runtime)}
    (before : CacheShape left right) (after : CacheShape leftTail rightTail) :
    CacheShape (left ++ leftTail) (right ++ rightTail) := by
  constructor
  · intro site
    simp only [preparedRaw, List.findSome?_append, isSome_or]
    change ((preparedRaw left site).isSome || (preparedRaw leftTail site).isSome) =
      ((preparedRaw right site).isSome || (preparedRaw rightTail site).isSome)
    rw [before.prepared, after.prepared]
  · intro site
    simp only [rememberedDisclosure, List.findSome?_append, isSome_or]
    change ((rememberedDisclosure left site).isSome ||
        (rememberedDisclosure leftTail site).isSome) =
      ((rememberedDisclosure right site).isSome ||
        (rememberedDisclosure rightTail site).isSome)
    rw [before.remembered, after.remembered]
  · intro site
    simp only [submittedAt, List.any_append]
    exact congrArg₂ (· || ·) (before.submitted site) (after.submitted site)

/-- A compiled binding can privately record different raw values without
changing the paired cache shape. -/
theorem append_prepare {left right : List (Entry runtime)} (shape : CacheShape left right)
    (leftView rightView : runtime.application.View) (site : Nat) (leftRaw rightRaw : Raw L) :
    CacheShape (left ++ [⟨leftView, .privateCommand (.prepare site leftRaw)⟩])
      (right ++ [⟨rightView, .privateCommand (.prepare site rightRaw)⟩]) := by
  apply shape.append
  constructor
  · intro queried
    by_cases same : site = queried <;> simp [preparedRaw, same]
  · intro queried; rfl
  · intro queried; rfl

/-- The private remembered intentions may differ, but are recorded at the same
public graph phase. -/
theorem append_remember {left right : List (Entry runtime)} (shape : CacheShape left right)
    (leftView rightView : runtime.application.View) (leftDisclose rightDisclose : Bool)
    (phase : leftView.application.publicState.pc = rightView.application.publicState.pc) :
    CacheShape (left ++ [⟨leftView, .privateCommand (.rememberDisclosure leftDisclose)⟩])
      (right ++ [⟨rightView, .privateCommand (.rememberDisclosure rightDisclose)⟩]) := by
  apply shape.append
  constructor
  · intro queried; rfl
  · intro queried
    by_cases same : rightView.application.publicState.pc = queried <;>
      simp [rememberedDisclosure, phase, same]
  · intro queried; rfl

/-- Equal commands at equal public phases preserve occupancy and submission
flags even when private components of the recorded views differ. -/
theorem append_same_command {left right : List (Entry runtime)} (shape : CacheShape left right)
    (leftView rightView : runtime.application.View) (command : Command runtime)
    (phase : leftView.application.publicState.pc = rightView.application.publicState.pc) :
    CacheShape (left ++ [⟨leftView, command⟩]) (right ++ [⟨rightView, command⟩]) := by
  cases command with
  | privateCommand command =>
      cases command with
      | prepare => exact shape.append_prepare leftView rightView _ _ _
      | rememberDisclosure => exact shape.append_remember leftView rightView _ _ phase
  | submit payload =>
      apply shape.append
      constructor <;> intro queried <;> cases payload <;>
        simp [preparedRaw, rememberedDisclosure, submittedAt]
  | replay | wait =>
      apply shape.append
      constructor <;> intro queried <;>
        simp [preparedRaw, rememberedDisclosure, submittedAt]

end CacheShape

end Vegas.GraphRuntime

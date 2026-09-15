/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Mathlib.Data.Fintype.Option

/-!
# Publication results

A source-level publication outcome. Failure is distinct from every successful
payload, including an optional payload whose value is `none`.
-/

namespace Vegas

universe u

/-- A source-level publication result. -/
inductive PublicationResult (α : Type u) where
  | failure
  | success (value : α)
deriving Repr, DecidableEq

namespace PublicationResult

variable {α : Type u}

def equivOption : PublicationResult α ≃ Option α where
  toFun
    | .failure => none
    | .success value => some value
  invFun
    | none => .failure
    | some value => .success value
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

instance [Fintype α] : Fintype (PublicationResult α) :=
  Fintype.ofEquiv (Option α) equivOption.symm

def isSuccess : PublicationResult α → Bool
  | .failure => false
  | .success _ => true

def isFailure : PublicationResult α → Bool
  | .failure => true
  | .success _ => false

def getD (fallback : α) : PublicationResult α → α
  | .failure => fallback
  | .success value => value

end PublicationResult

end Vegas

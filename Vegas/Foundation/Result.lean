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

`PublicationResult α` is isomorphic to `Option α`, by `equivOption`. It is a
separate type because `Option` already means something else wherever
publication results occur. A graph store reports an unwritten field as `none`,
so a stored publication is an `Option (PublicationResult α)` whose outer layer
is availability and whose inner layer is a completed failure; unifying them
would let `Option`'s combinators and simp lemmas cross the two. An expression
language has both an optional and a result type constructor, and
`IExpr.ResultTypes` pins the second to this type; unifying them would give the
two constructors one denotation and one set of eliminators.

Those are the only reasons. A development with a total store and no optional
payloads could use `Option` directly.
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

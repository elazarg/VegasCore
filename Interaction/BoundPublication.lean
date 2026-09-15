/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.GuardedPublication

/-! # Immutable bindings for guarded publication

A binding is private state fixed before publication.  Revealing an openable
binding may publish exactly its bound value; declining disclosure, or revealing
an unopenable binding, resolves the public site as failure.  An unbound site
stutters.  Guard checking and write-once public resolution are delegated to
`GuardedPublication.resolve`.
-/

namespace Interaction

universe u v

/-- Private status of one heterogeneous binding. -/
inductive Binding (A : Type v) where
  | unbound
  | unopenable
  | value (data : A)
  deriving DecidableEq

abbrev BindingStore {Slot : Type u} (Value : Slot → Type v) :=
  (slot : Slot) → Binding (Value slot)

namespace BindingStore

variable {Slot : Type u} {Value : Slot → Type v}

def empty : BindingStore Value := fun _ => .unbound

def write [DecidableEq Slot] (bindings : BindingStore Value)
    (site : Slot) (binding : Binding (Value site)) : BindingStore Value :=
  fun slot => if equal : site = slot then equal ▸ binding else bindings slot

@[simp] theorem write_self [DecidableEq Slot] (bindings : BindingStore Value)
    (site : Slot) (binding : Binding (Value site)) :
    bindings.write site binding site = binding := by
  simp [write]

@[simp] theorem write_other [DecidableEq Slot] (bindings : BindingStore Value)
    (site slot : Slot) (binding : Binding (Value site)) (different : site ≠ slot) :
    bindings.write site binding slot = bindings slot := by
  simp [write, different]

/-- Bind at most once.  Later attempts cannot replace the first binding. -/
def bind [DecidableEq Slot] (bindings : BindingStore Value)
    (site : Slot) (binding : Binding (Value site)) : BindingStore Value :=
  match bindings site with
  | .unbound => bindings.write site binding
  | .unopenable | .value _ => bindings

@[simp] theorem bind_of_bound [DecidableEq Slot] (bindings : BindingStore Value)
    (site : Slot) (binding : Binding (Value site))
    (bound : bindings site ≠ .unbound) :
    bindings.bind site binding = bindings := by
  cases current : bindings site <;> simp_all [bind]

theorem bind_idempotent [DecidableEq Slot] (bindings : BindingStore Value)
    (site : Slot) (first second : Binding (Value site))
    (first_bound : first ≠ .unbound) :
    (bindings.bind site first).bind site second = bindings.bind site first := by
  cases current : bindings site
  · cases first <;> simp_all [bind]
  · simp [bind, current]
  · simp [bind, current]

end BindingStore

/-- Private immutable bindings paired with their public guarded publications. -/
structure BoundPublicationState {Slot : Type u} (Value : Slot → Type v) where
  bindings : BindingStore Value
  publications : PublicationStore Value

namespace BoundPublicationState

variable {Slot : Type u} {Value : Slot → Type v}

def empty : BoundPublicationState Value where
  bindings := BindingStore.empty
  publications := PublicationStore.empty

/-- Establish private binding state once, without changing public state. -/
def bind [DecidableEq Slot] (state : BoundPublicationState Value)
    (site : Slot) (binding : Binding (Value site)) : BoundPublicationState Value :=
  { state with bindings := state.bindings.bind site binding }

@[simp] theorem bind_public [DecidableEq Slot] (state : BoundPublicationState Value)
    (site : Slot) (binding : Binding (Value site)) :
    (state.bind site binding).publications = state.publications := rfl

/-- A reveal has no replacement payload.  `true` publishes the immutable value
when one exists; `false` resolves a bound site as failure. -/
def reveal [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : BoundPublicationState Value) (site : Slot) (disclose : Bool) :
    BoundPublicationState Value :=
  match state.bindings site with
  | .unbound => state
  | .unopenable =>
      { state with publications := protocol.resolve state.publications site none }
  | .value data =>
      let candidate := if disclose then some data else none
      { state with publications := protocol.resolve state.publications site candidate }

@[simp] theorem reveal_unbound [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : BoundPublicationState Value) (site : Slot) (disclose : Bool)
    (unbound : state.bindings site = .unbound) :
    state.reveal protocol site disclose = state := by
  simp [reveal, unbound]

@[simp] theorem reveal_bindings [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : BoundPublicationState Value) (site : Slot) (disclose : Bool) :
    (state.reveal protocol site disclose).bindings = state.bindings := by
  cases current : state.bindings site <;> simp [reveal, current]

theorem reveal_public_extends [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : BoundPublicationState Value) (site : Slot) (disclose : Bool) :
    state.publications.Extends (state.reveal protocol site disclose).publications := by
  cases current : state.bindings site with
  | unbound => simp [reveal, current, PublicationStore.Extends.refl]
  | unopenable =>
      simpa [reveal, current] using protocol.resolve_extends state.publications site none
  | value data =>
      simpa [reveal, current] using protocol.resolve_extends state.publications site
        (if disclose then some data else none)

theorem reveal_public_consistent [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : BoundPublicationState Value) (site : Slot) (disclose : Bool)
    (consistent : protocol.Consistent state.publications) :
    protocol.Consistent (state.reveal protocol site disclose).publications := by
  cases current : state.bindings site with
  | unbound => simpa [reveal, current] using consistent
  | unopenable =>
      simpa [reveal, current] using
        protocol.resolve_consistent state.publications site none consistent
  | value data =>
      simpa [reveal, current] using
        protocol.resolve_consistent state.publications site
          (if disclose then some data else none) consistent

/-- Disclosing supplies exactly the previously bound value to the resolver. -/
theorem reveal_value_public [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : BoundPublicationState Value) (site : Slot) (data : Value site)
    (bound : state.bindings site = .value data) :
    (state.reveal protocol site true).publications =
      protocol.resolve state.publications site (some data) := by
  simp [reveal, bound]

/-- Withholding a bound value resolves failure; it cannot substitute a value. -/
theorem withhold_value_public [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : BoundPublicationState Value) (site : Slot) (data : Value site)
    (bound : state.bindings site = .value data) :
    (state.reveal protocol site false).publications =
      protocol.resolve state.publications site none := by
  simp [reveal, bound]

end BoundPublicationState

end Interaction

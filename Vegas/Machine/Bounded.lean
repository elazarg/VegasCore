/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Basic

/-!
# Bounded machine presentation states

`BoundedState` carries a semantic machine state together with a finite
presentation depth.  The counter is presentation data; it is not part of the
underlying machine semantics.
-/

namespace Vegas

namespace Machine

variable {Player : Type}

/-- Horizon-bounded state wrapper for finite presentations.  The counter is
presentation data; the underlying machine state remains the semantic state. -/
structure BoundedState (M : Machine Player) (horizon : Nat) where
  state : M.State
  depth : Nat
  depth_le : depth ≤ horizon

namespace BoundedState

variable {M : Machine Player} {horizon : Nat}

@[ext] theorem ext
    {left right : M.BoundedState horizon}
    (hstate : left.state = right.state)
    (hdepth : left.depth = right.depth) :
    left = right := by
  cases left
  cases right
  cases hstate
  cases hdepth
  rfl

/-- Initial bounded presentation state. -/
def init (M : Machine Player) (horizon : Nat) : M.BoundedState horizon where
  state := M.init
  depth := 0
  depth_le := by omega

/-- Step the bounded presentation counter. -/
def succ (pref : M.BoundedState horizon)
    (hlt : pref.depth < horizon) (next : M.State) :
    M.BoundedState horizon where
  state := next
  depth := pref.depth + 1
  depth_le := by omega

@[simp] theorem init_state (M : Machine Player) (horizon : Nat) :
    (BoundedState.init M horizon).state = M.init := rfl

@[simp] theorem init_depth (M : Machine Player) (horizon : Nat) :
    (BoundedState.init M horizon).depth = 0 := rfl

@[simp] theorem succ_state
    (pref : M.BoundedState horizon) (hlt : pref.depth < horizon)
    (next : M.State) :
    (pref.succ hlt next).state = next := rfl

@[simp] theorem succ_depth
    (pref : M.BoundedState horizon) (hlt : pref.depth < horizon)
    (next : M.State) :
    (pref.succ hlt next).depth = pref.depth + 1 := rfl

@[reducible] noncomputable instance instFintype
    [Fintype M.State] :
    Fintype (M.BoundedState horizon) := by
  classical
  let e :
      M.BoundedState horizon ≃ M.State × Fin (horizon + 1) :=
    { toFun := fun s =>
        (s.state, ⟨s.depth, Nat.lt_succ_of_le s.depth_le⟩)
      invFun := fun p =>
        { state := p.1
          depth := p.2.1
          depth_le := Nat.le_of_lt_succ p.2.2 }
      left_inv := by
        intro s
        cases s
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  exact Fintype.ofEquiv _ e.symm

end BoundedState

end Machine

end Vegas

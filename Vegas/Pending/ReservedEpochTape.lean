/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.EquivFin

/-! # Joint finite tapes for reserved processing epochs

A tape records processing masks, activation masks and owner orders together.
Its probability law is supplied separately and may correlate every field.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

/-- A finite joint service environment, periodically extended after its prefix. -/
structure Tape (Player : Type) (length : Nat) where
  order : Fin (length + 1) → Equiv.Perm Player
  activation : Fin (length + 1) → Player → Bool
  processing : Fin (length + 1) → Bool

namespace Tape

variable {Player : Type} {length : Nat}

def index (cycle : Nat) : Fin (length + 1) := Fin.ofNat (length + 1) cycle

def processes (tape : Tape Player length) (cycle : Nat) : Bool :=
  tape.processing (index cycle)

def activates (tape : Tape Player length) (cycle : Nat) (owner : Player) : Bool :=
  tape.activation (index cycle) owner

def owner [Fintype Player] (tape : Tape Player length) (cycle : Nat)
    (position : Fin (Fintype.card Player)) : Player :=
  tape.order (index cycle) ((Fintype.equivFin Player).symm position)

theorem owner_injective [Fintype Player] (tape : Tape Player length) (cycle : Nat) :
    Function.Injective (tape.owner cycle) :=
  (tape.order (index cycle)).injective.comp (Fintype.equivFin Player).symm.injective

theorem owner_surjective [Fintype Player] (tape : Tape Player length) (cycle : Nat) :
    Function.Surjective (tape.owner cycle) :=
  (tape.order (index cycle)).surjective.comp (Fintype.equivFin Player).symm.surjective

/-- Bounds are statements about the operational tape, independently of play. -/
structure BoundedGaps (tape : Tape Player length) (cycles activationGap processingGap : Nat) :
    Prop where
  activation : ∀ cycle < cycles, ∀ owner, ∃ later,
    cycle ≤ later ∧ later < cycle + activationGap ∧ tape.activates later owner = true
  processing : ∀ cycle < cycles, ∃ later,
    cycle ≤ later ∧ later < cycle + processingGap ∧ tape.processes later = true

/-- Every cycle offers service, with an arbitrary exogenous owner permutation. -/
def continuous (order : Fin (length + 1) → Equiv.Perm Player) : Tape Player length :=
  ⟨order, fun _ _ => true, fun _ => true⟩

theorem continuous_boundedGaps (order : Fin (length + 1) → Equiv.Perm Player)
    (cycles : Nat) : (continuous order).BoundedGaps cycles 1 1 where
  activation cycle _ owner := ⟨cycle, le_rfl, by omega, rfl⟩
  processing cycle _ := ⟨cycle, le_rfl, by omega, rfl⟩

end Tape
end Vegas.EventGraphRuntime.ReservedEpoch

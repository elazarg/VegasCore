/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.BoundPublication
import Mathlib.Tactic.DeriveFintype

/-! # Heterogeneous partial disclosure with deferred validation

One owner binds a two-bit secret and its Boolean parity. The parity is published
first: it is concrete public data while its relation with the secret is pending.
The secret's later publication either satisfies the relation or fails, without
retracting the parity or replacing the private commitment.
-/

namespace InteractionTests.GuardedPublication

open Interaction

inductive Site where
  | secret
  | parity
  deriving DecidableEq, Fintype

abbrev Value : Site → Type
  | .secret => Fin 4
  | .parity => Bool

def parityGuard : PublicationGuard Value where
  subject := .parity
  dependencies := Finset.univ
  subject_mem := Finset.mem_univ _
  test values :=
    values ⟨.parity, Finset.mem_univ _⟩ ==
      decide ((values ⟨.secret, Finset.mem_univ _⟩).val % 2 = 1)

def protocol : GuardedPublication Value := ⟨[parityGuard]⟩

def committed (secret : Fin 4) (parity : Bool) : BoundPublicationState Value :=
  ((BoundPublicationState.empty (Value := Value)).bind .secret (.value secret)).bind
    .parity (.value parity)

def disclosedParity (secret : Fin 4) (parity : Bool) : BoundPublicationState Value :=
  (committed secret parity).reveal protocol .parity true

def finish (secret : Fin 4) (parity : Bool) : BoundPublicationState Value :=
  (disclosedParity secret parity).reveal protocol .secret true

/-- A proper partial disclosure: both distinct secrets have this parity. -/
theorem partial_disclosure :
    (disclosedParity 1 true).publications = (disclosedParity 3 true).publications ∧
    (disclosedParity 3 true).publications .parity = .value true ∧
    (disclosedParity 3 true).publications .secret = .pending ∧
    parityGuard.check (disclosedParity 3 true).publications = .pending := by
  constructor
  · funext site
    cases site <;> decide
  · decide

theorem honest_success :
    (finish 3 true).publications .secret = .value 3 ∧
    (finish 3 true).publications .parity = .value true ∧
    parityGuard.check (finish 3 true).publications = .satisfied := by
  decide

/-- The later closer fails, while the earlier value and original secret remain. -/
theorem inconsistent_opening :
    (finish 2 true).publications .secret = .failed ∧
    (finish 2 true).publications .parity = .value true ∧
    (finish 2 true).bindings .secret = .value 2 ∧
    parityGuard.check (finish 2 true).publications = .satisfied := by
  decide

theorem withholding :
    ((disclosedParity 3 true).reveal protocol .secret false).publications .secret = .failed ∧
    ((disclosedParity 3 true).reveal protocol .secret false).publications .parity =
      .value true := by
  decide

theorem unopenable_binding :
    (((((BoundPublicationState.empty (Value := Value)).bind .secret .unopenable).bind
      .parity (.value true)).reveal protocol .parity true).reveal
        protocol .secret true).publications .secret = .failed := by
  decide

theorem cannot_replace_commitment :
    ((committed 2 true).bind .secret (.value 3)).bindings .secret = .value 2 := by
  decide

/-- A settlement can reward ordinary validated play and penalize failure,
without identifying failure with an ordinary secret value. -/
def reward (state : BoundPublicationState Value) : Int :=
  match state.publications .secret, state.publications .parity with
  | .value secret, .value _ => 1 + secret.val
  | _, _ => -1

theorem guarded_play_beats_failure :
    reward (finish 3 true) = 4 ∧ reward (finish 2 true) = -1 ∧
    reward ((disclosedParity 3 true).reveal protocol .secret false) = -1 := by
  decide

/-- Reordering inconsistent disclosures changes the failing slot. -/
theorem reveal_order_matters :
    (finish 2 true).publications .parity = .value true ∧
    (((committed 2 true).reveal protocol .secret true).reveal
      protocol .parity true).publications .parity = .failed := by
  decide

theorem same_owner_attribution :
    parityGuard.OwnedPending (fun _ => ()) (disclosedParity 2 true).publications := by
  intro _site _member _pending
  rfl

/-- A foreign hidden dependency would violate the ownership discipline. -/
theorem cross_owner_rejected :
    ¬ parityGuard.OwnedPending id (disclosedParity 2 true).publications := by
  intro owned
  have impossible := owned .secret (Finset.mem_univ _) (by decide)
  cases impossible

end InteractionTests.GuardedPublication

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Regularity
import GameTheoryExtensions.Math.Probability.Support

/-! # Inclusion proposals sampled over distinct pending identifiers

The eligibility predicate identifies the application event and author whose
proposals compete. Selection consults only the current pending packets.
Adding an eligible fresh identifier scales every retained candidate equally.

This is an inclusion rule for investigating continuation preservation. It is
not installed in the reserved service, and supplies neither service liveness
nor the correspondence between native and source subgames.
-/

noncomputable section

namespace Interaction.MessageNetwork

open GameTheory.Math.Probability

variable {Principal Payload : Type} [DecidableEq Principal]

def eligibleIds (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) : Finset (MessageId Principal) :=
  ((pending.filter eligible).map Message.id).toFinset

def chooseUniform (candidates : Finset (MessageId Principal)) :
    PMF (Option (MessageId Principal)) :=
  if nonempty : candidates.Nonempty then (PMF.uniformOfFinset candidates nonempty).map some
  else PMF.pure none

def uniformPending (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) : PMF (Option (MessageId Principal)) :=
  chooseUniform (eligibleIds eligible pending)

omit [DecidableEq Principal] in
theorem chooseUniform_supported (candidates : Finset (MessageId Principal))
    (id : MessageId Principal) (supported : some id ∈ (chooseUniform candidates).support) :
    id ∈ candidates := by
  unfold chooseUniform at supported
  split at supported
  · rename_i nonempty
    obtain ⟨selected, member, same⟩ := PMF.support_map .. ▸ supported
    cases Option.some.inj same
    exact (PMF.mem_support_uniformOfFinset_iff nonempty id).mp member
  · cases (PMF.mem_support_pure_iff _ _).mp supported

omit [DecidableEq Principal] in
theorem chooseUniform_support_finite (candidates : Finset (MessageId Principal)) :
    (chooseUniform candidates).support.Finite := by
  refine ((Set.finite_singleton none).union
    ((Finset.finite_toSet candidates).image some)).subset ?_
  intro selected supported
  cases selected with
  | none => exact Or.inl rfl
  | some id => exact Or.inr ⟨id, chooseUniform_supported candidates id supported, rfl⟩

theorem uniformPending_supported (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) (id : MessageId Principal)
    (supported : some id ∈ (uniformPending eligible pending).support) :
    ∃ message ∈ pending, eligible message = true ∧ message.id = id := by
  have member := chooseUniform_supported (eligibleIds eligible pending) id supported
  obtain ⟨message, selected, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact ⟨message, (List.mem_filter.mp selected).1, (List.mem_filter.mp selected).2, same⟩

omit [DecidableEq Principal] in
theorem chooseUniform_singleton (id : MessageId Principal) :
    chooseUniform {id} = PMF.pure (some id) := by
  classical
  have singletonLaw : PMF.uniformOfFinset {id} (Finset.singleton_nonempty id) =
      PMF.pure id := by
    ext value
    by_cases same : value = id <;> simp [PMF.uniformOfFinset_apply, PMF.pure_apply, same]
  rw [chooseUniform, dite_eq_left (Finset.singleton_nonempty id), singletonLaw,
    PMF.pure_map]

theorem chooseUniform_insert (candidates : Finset (MessageId Principal))
    (nonempty : candidates.Nonempty) (fresh : MessageId Principal) (absent : fresh ∉ candidates) :
    chooseUniform (insert fresh candidates) =
      mix (((candidates.card : ℝ) + 1)⁻¹)
        (inv_nonneg.mpr (by positivity))
        (by rw [inv_le_one₀ (by positivity)]
            have := Nat.cast_nonneg (α := ℝ) candidates.card
            linarith)
        (PMF.pure (some fresh)) (chooseUniform candidates) := by
  rw [chooseUniform, dite_eq_left (Finset.insert_nonempty _ _),
    uniformOfFinset_insert candidates nonempty fresh absent, mix_map, PMF.pure_map]
  rw [chooseUniform, dite_eq_left nonempty]

theorem uniformPending_empty (eligible : Message Principal Payload → Bool) :
    uniformPending eligible [] = PMF.pure none := by
  simp [uniformPending, eligibleIds, chooseUniform]

theorem uniformPending_singleton (eligible : Message Principal Payload → Bool)
    (packet : Message Principal Payload) (accepted : eligible packet = true) :
    uniformPending eligible [packet] = PMF.pure (some packet.id) := by
  simpa only [uniformPending, eligibleIds, List.filter_cons_of_pos accepted,
    List.filter_nil, List.map_cons, List.map_nil, List.toFinset_cons,
    List.toFinset_nil, Finset.insert_empty] using chooseUniform_singleton packet.id

theorem eligibleIds_append (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) (packet : Message Principal Payload) :
    eligibleIds eligible (pending ++ [packet]) =
      if eligible packet then insert packet.id (eligibleIds eligible pending)
      else eligibleIds eligible pending := by
  by_cases accepted : eligible packet = true
  · simp [eligibleIds, List.filter_append, accepted, Finset.union_comm]
  · simp [eligibleIds, List.filter_append, accepted]

theorem uniformPending_learn (eligible : Message Principal Payload → Bool)
    (network : MessageNetwork Principal Payload) (who : Principal)
    (selected : Finset (MessageId Principal)) :
    uniformPending eligible (network.learn who selected).pending =
      uniformPending eligible network.pending := rfl

/-- Uniform selection implements an action-independent mixture: one part
fresh proposal, the rest the original law over distinct retained identifiers. -/
theorem uniformPending_append_fresh (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) (packet : Message Principal Payload)
    (accepted : eligible packet = true)
    (nonempty : (eligibleIds eligible pending).Nonempty)
    (fresh : packet.id ∉ eligibleIds eligible pending) :
    uniformPending eligible (pending ++ [packet]) =
      mix (((eligibleIds eligible pending).card : ℝ) + 1)⁻¹
        (inv_nonneg.mpr (by positivity))
        (by rw [inv_le_one₀ (by positivity)]
            have := Nat.cast_nonneg (α := ℝ) (eligibleIds eligible pending).card
            linarith)
        (PMF.pure (some packet.id)) (uniformPending eligible pending) := by
  simp only [uniformPending, eligibleIds_append, accepted, ↓reduceIte]
  rw [chooseUniform, dite_eq_left (Finset.insert_nonempty _ _),
    uniformOfFinset_insert _ nonempty _ fresh, mix_map, PMF.pure_map]
  rw [chooseUniform, dite_eq_left nonempty]

/-- Uniform insertion is regular even when the retained menu is empty. -/
theorem chooseUniform_regular_insert (candidates : Finset (MessageId Principal))
    (fresh : MessageId Principal) (absent : fresh ∉ candidates) :
    (chooseUniform candidates).RegularAt (chooseUniform (insert fresh candidates))
      (some fresh) := by
  by_cases nonempty : candidates.Nonempty
  · rw [chooseUniform_insert candidates nonempty fresh absent]
    apply PMF.regularAt_mix
  · have empty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    rw [empty, Finset.insert_empty, chooseUniform_singleton]
    intro value different
    rw [PMF.pure_apply_of_ne _ _ different, ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg

/-- Uniform selection also satisfies the regularity contract. -/
theorem uniformPending_append_regular
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (packet : Message Principal Payload) (accepted : eligible packet = true)
    (nonempty : (eligibleIds eligible pending).Nonempty)
    (fresh : packet.id ∉ eligibleIds eligible pending) :
    (uniformPending eligible pending).RegularAt
      (uniformPending eligible (pending ++ [packet])) (some packet.id) := by
  rw [uniformPending_append_fresh eligible pending packet accepted nonempty fresh]
  apply PMF.regularAt_mix

end Interaction.MessageNetwork

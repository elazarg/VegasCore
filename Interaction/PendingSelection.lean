/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork
import GameTheoryExtensions.Math.Probability.FinDist
import GameTheoryExtensions.Math.Probability.Regularity

/-! # Inclusion proposals sampled over distinct pending identifiers

The eligibility predicate identifies the application event and author whose
proposals compete. Selection consults only the current pending packets.
Rebroadcasting an already pending envelope does not change its probability;
adding an eligible fresh identifier scales every retained candidate equally.

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
    FinDist (Option (MessageId Principal)) :=
  if nonempty : candidates.Nonempty then (FinDist.uniformSet candidates nonempty).map some
  else FinDist.pure none

def uniformPending (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) : FinDist (Option (MessageId Principal)) :=
  chooseUniform (eligibleIds eligible pending)

omit [DecidableEq Principal] in
theorem chooseUniform_supported (candidates : Finset (MessageId Principal))
    (id : MessageId Principal) (supported : some id ∈ (chooseUniform candidates).support) :
    id ∈ candidates := by
  unfold chooseUniform at supported
  split at supported
  · rename_i nonempty
    obtain ⟨selected, member, same⟩ := FinDist.support_map .. ▸ supported
    cases Option.some.inj same
    exact (FinDist.mem_support_uniformSet_iff candidates nonempty id).mp member
  · cases FinDist.mem_support_pure.mp supported

theorem uniformPending_supported (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) (id : MessageId Principal)
    (supported : some id ∈ (uniformPending eligible pending).support) :
    ∃ message ∈ pending, eligible message = true ∧ message.id = id := by
  have member := chooseUniform_supported (eligibleIds eligible pending) id supported
  obtain ⟨message, selected, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact ⟨message, (List.mem_filter.mp selected).1, (List.mem_filter.mp selected).2, same⟩

omit [DecidableEq Principal] in
theorem chooseUniform_singleton (id : MessageId Principal) :
    chooseUniform {id} = FinDist.pure (some id) := by
  classical
  have singletonLaw : FinDist.uniformSet {id} (Finset.singleton_nonempty id) =
      FinDist.pure id := by
    apply FinDist.ext_of_prob
    intro value
    simp only [FinDist.prob_uniformSet, Finset.mem_singleton, Finset.card_singleton,
      Nat.cast_one, inv_one, FinDist.prob_pure_eq_ite]
  rw [chooseUniform, dite_eq_left (Finset.singleton_nonempty id), singletonLaw,
    FinDist.map_pure]

theorem chooseUniform_insert (candidates : Finset (MessageId Principal))
    (nonempty : candidates.Nonempty) (fresh : MessageId Principal) (absent : fresh ∉ candidates) :
    chooseUniform (insert fresh candidates) =
      FinDist.mix (((candidates.card : ℝ) + 1)⁻¹)
        (inv_nonneg.mpr (by positivity))
        (by rw [inv_le_one₀ (by positivity)]
            have := Nat.cast_nonneg (α := ℝ) candidates.card
            linarith)
        (FinDist.pure (some fresh)) (chooseUniform candidates) := by
  rw [chooseUniform, dite_eq_left (Finset.insert_nonempty _ _),
    FinDist.uniformSet_insert candidates nonempty fresh absent, FinDist.map_mix, FinDist.map_pure]
  rw [chooseUniform, dite_eq_left nonempty]

theorem uniformPending_empty (eligible : Message Principal Payload → Bool) :
    uniformPending eligible [] = FinDist.pure none := by
  simp [uniformPending, eligibleIds, chooseUniform]

theorem uniformPending_singleton (eligible : Message Principal Payload → Bool)
    (packet : Message Principal Payload) (accepted : eligible packet = true) :
    uniformPending eligible [packet] = FinDist.pure (some packet.id) := by
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

theorem eligibleIds_append_existing (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) (packet : Message Principal Payload)
    (member : packet ∈ pending) :
    eligibleIds eligible (pending ++ [packet]) = eligibleIds eligible pending := by
  rw [eligibleIds_append]
  split
  · rename_i accepted
    apply Finset.insert_eq_of_mem
    simp only [eligibleIds, List.mem_toFinset, List.mem_map]
    exact ⟨packet, List.mem_filter.mpr ⟨member, accepted⟩, rfl⟩
  · rfl

/-- Every eligible envelope a player can rebroadcast already has a pending
candidate. A service must establish this at the point of comparison. -/
def RetainsEligible (network : MessageNetwork Principal Payload)
    (eligible : Message Principal Payload → Bool) : Prop :=
  ∀ who packet, packet ∈ network.known who → eligible packet = true →
    packet.id ∈ eligibleIds eligible network.pending

theorem RetainsEligible.empty (eligible : Message Principal Payload → Bool) :
    (MessageNetwork.empty : MessageNetwork Principal Payload).RetainsEligible eligible := by
  intro who packet member
  simp [known, MessageNetwork.empty] at member

/-- With candidate retention, every raw replay preserves the eligible menu,
including failed lookups and ineligible broadcasts. -/
theorem RetainsEligible.replay_ids
    (network : MessageNetwork Principal Payload) (eligible : Message Principal Payload → Bool)
    (retained : network.RetainsEligible eligible) (who : Principal) (id : MessageId Principal) :
    eligibleIds eligible (network.replay who id).2.pending =
      eligibleIds eligible network.pending := by
  unfold replay
  split
  · rfl
  · rename_i packet found
    change eligibleIds eligible (network.pending ++ [packet]) = _
    rw [eligibleIds_append]
    split
    · rename_i accepted
      exact Finset.insert_eq_of_mem
        (retained who packet (List.mem_of_find?_eq_some found) accepted)
    · rfl

/-- Duplicate transport copies remain legal, but do not buy extra weight. -/
theorem uniformPending_append_existing (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) (packet : Message Principal Payload)
    (member : packet ∈ pending) :
    uniformPending eligible (pending ++ [packet]) = uniformPending eligible pending := by
  unfold uniformPending
  rw [eligibleIds_append_existing eligible pending packet member]

/-- This applies to the actual network replay operation whenever the replayed
envelope is already pending. Reintroducing an absent envelope is different. -/
theorem uniformPending_replay (eligible : Message Principal Payload → Bool)
    (network next : MessageNetwork Principal Payload) (who : Principal)
    (id : MessageId Principal) (packet : Message Principal Payload)
    (replayed : network.replay who id = (some packet, next))
    (pending : packet ∈ network.pending) :
    uniformPending eligible next.pending = uniformPending eligible network.pending := by
  unfold replay at replayed
  split at replayed
  · cases replayed
  · cases replayed
    exact uniformPending_append_existing eligible network.pending packet pending

theorem uniformPending_replay_of_retained (eligible : Message Principal Payload → Bool)
    (network : MessageNetwork Principal Payload) (retained : network.RetainsEligible eligible)
    (who : Principal) (id : MessageId Principal) :
    uniformPending eligible (network.replay who id).2.pending =
      uniformPending eligible network.pending := by
  unfold uniformPending
  rw [retained.replay_ids]

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
      FinDist.mix (((eligibleIds eligible pending).card : ℝ) + 1)⁻¹
        (inv_nonneg.mpr (by positivity))
        (by rw [inv_le_one₀ (by positivity)]
            have := Nat.cast_nonneg (α := ℝ) (eligibleIds eligible pending).card
            linarith)
        (FinDist.pure (some packet.id)) (uniformPending eligible pending) := by
  simp only [uniformPending, eligibleIds_append, accepted, ↓reduceIte]
  rw [chooseUniform, dite_eq_left (Finset.insert_nonempty _ _),
    FinDist.uniformSet_insert _ nonempty _ fresh, FinDist.map_mix, FinDist.map_pure]
  rw [chooseUniform, dite_eq_left nonempty]

/-- Uniform insertion is regular even when the retained menu is empty. -/
theorem chooseUniform_regular_insert (candidates : Finset (MessageId Principal))
    (fresh : MessageId Principal) (absent : fresh ∉ candidates) :
    (chooseUniform candidates).RegularAt (chooseUniform (insert fresh candidates))
      (some fresh) := by
  by_cases nonempty : candidates.Nonempty
  · rw [chooseUniform_insert candidates nonempty fresh absent]
    apply FinDist.regularAt_mix
  · have empty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    rw [empty, Finset.insert_empty, chooseUniform_singleton]
    intro value different
    rw [FinDist.prob_pure_of_ne different]
    exact FinDist.prob_nonneg _ _

/-- Uniform selection also satisfies the regularity contract. -/
theorem uniformPending_append_regular
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (packet : Message Principal Payload) (accepted : eligible packet = true)
    (nonempty : (eligibleIds eligible pending).Nonempty)
    (fresh : packet.id ∉ eligibleIds eligible pending) :
    (uniformPending eligible pending).RegularAt
      (uniformPending eligible (pending ++ [packet])) (some packet.id) := by
  rw [uniformPending_append_fresh eligible pending packet accepted nonempty fresh]
  apply FinDist.regularAt_mix

end Interaction.MessageNetwork

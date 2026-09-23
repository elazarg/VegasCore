/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.PendingSelection
import GameTheoryExtensions.Math.Probability.WeightedSet

/-! # Weighted inclusion on distinct pending identifiers

Weights are fixed across the compared submissions. A service may supply them
from public fee or delivery attributes; this module does not model fee choice,
miner optimization, or changes to the weights of already pending messages.
-/

noncomputable section

namespace Interaction.MessageNetwork

open GameTheory.Math.Probability

variable {Principal Payload : Type} [DecidableEq Principal]

def chooseWeighted (weight : MessageId Principal → ℝ) (positive : ∀ id, 0 < weight id)
    (candidates : Finset (MessageId Principal)) : FinDist (Option (MessageId Principal)) :=
  if nonempty : candidates.Nonempty then
    (FinDist.weightedSet candidates nonempty weight positive).map some
  else FinDist.pure none

def weightedPending (weight : MessageId Principal → ℝ) (positive : ∀ id, 0 < weight id)
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload)) :
    FinDist (Option (MessageId Principal)) :=
  chooseWeighted weight positive (eligibleIds eligible pending)

theorem weightedPending_one (eligible : Message Principal Payload → Bool)
    (pending : List (Message Principal Payload)) :
    weightedPending (fun _ => 1) (fun _ => by norm_num) eligible pending =
      uniformPending eligible pending := by
  unfold weightedPending uniformPending chooseWeighted chooseUniform
  split
  · rw [FinDist.weightedSet_one]
  · rfl

theorem weightedPending_append_fresh
    (weight : MessageId Principal → ℝ) (positive : ∀ id, 0 < weight id)
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (packet : Message Principal Payload) (accepted : eligible packet = true)
    (nonempty : (eligibleIds eligible pending).Nonempty)
    (fresh : packet.id ∉ eligibleIds eligible pending) :
    weightedPending weight positive eligible (pending ++ [packet]) =
      let total := FinDist.totalWeight (eligibleIds eligible pending) weight
      let totalPositive := FinDist.totalWeight_pos _ nonempty weight positive
      FinDist.mix (weight packet.id / (weight packet.id + total))
        (div_nonneg (positive packet.id).le (add_pos (positive packet.id) totalPositive).le)
        ((div_le_one (add_pos (positive packet.id) totalPositive)).mpr
          (le_add_of_nonneg_right totalPositive.le))
        (FinDist.pure (some packet.id)) (weightedPending weight positive eligible pending) := by
  unfold weightedPending
  rw [eligibleIds_append, ite_eq_left accepted]
  simp only [chooseWeighted, dite_eq_left nonempty,
    dite_eq_left (Finset.insert_nonempty packet.id _)]
  rw [FinDist.weightedSet_insert _ nonempty weight positive packet.id fresh,
    FinDist.map_mix, FinDist.map_pure]

theorem weightedPending_append_regular
    (weight : MessageId Principal → ℝ) (positive : ∀ id, 0 < weight id)
    (eligible : Message Principal Payload → Bool) (pending : List (Message Principal Payload))
    (packet : Message Principal Payload) (accepted : eligible packet = true)
    (nonempty : (eligibleIds eligible pending).Nonempty)
    (fresh : packet.id ∉ eligibleIds eligible pending) :
    (weightedPending weight positive eligible pending).RegularAt
      (weightedPending weight positive eligible (pending ++ [packet])) (some packet.id) := by
  rw [weightedPending_append_fresh weight positive eligible pending packet accepted nonempty fresh]
  apply FinDist.regularAt_mix

theorem weightedPending_replay
    (weight : MessageId Principal → ℝ) (positive : ∀ id, 0 < weight id)
    (eligible : Message Principal Payload → Bool)
    (network next : MessageNetwork Principal Payload) (who : Principal)
    (id : MessageId Principal) (packet : Message Principal Payload)
    (replayed : network.replay who id = (some packet, next))
    (pending : packet ∈ network.pending) :
    weightedPending weight positive eligible next.pending =
      weightedPending weight positive eligible network.pending := by
  unfold replay at replayed
  split at replayed
  · cases replayed
  · cases replayed
    unfold weightedPending
    rw [eligibleIds_append_existing eligible network.pending packet pending]

theorem weightedPending_learn
    (weight : MessageId Principal → ℝ) (positive : ∀ id, 0 < weight id)
    (eligible : Message Principal Payload → Bool) (network : MessageNetwork Principal Payload)
    (who : Principal) (selected : Finset (MessageId Principal)) :
    weightedPending weight positive eligible (network.learn who selected).pending =
      weightedPending weight positive eligible network.pending := rfl

theorem weightedPending_replay_of_retained
    (weight : MessageId Principal → ℝ) (positive : ∀ id, 0 < weight id)
    (eligible : Message Principal Payload → Bool) (network : MessageNetwork Principal Payload)
    (retained : network.RetainsEligible eligible) (who : Principal) (id : MessageId Principal) :
    weightedPending weight positive eligible (network.replay who id).2.pending =
      weightedPending weight positive eligible network.pending := by
  unfold weightedPending
  rw [retained.replay_ids]

end Interaction.MessageNetwork

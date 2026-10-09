/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeService

/-! # Exact probabilities of pending disclosure

Every subset of the foreign pending identifiers has mass two to the negative
pool size, and every other subset has mass zero. In particular, a singleton
foreign pool discloses its identifier or discloses nothing with equal chance.
These are facts about a single observation sample; learned packets remain in
recall through the existing network semantics.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeObservation

open Interaction EventGraphRuntime GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

/-- Packet payloads do not affect which pending identifiers are disclosed. -/
theorem leaks_eq_of_identifiers (who : Player)
    (first second : List (Message Player (WitnessedPacket nativeGraph)))
    (same : first.map Message.id = second.map Message.id) :
    leaks who first = leaks who second := by
  have pool : foreignPending who first = foreignPending who second := by
    exact congrArg (fun ids : Finset (MessageId Player) => ids.filter (fun id => id.1 ≠ who))
      (MessageNetwork.pendingIds_eq_of_map_id_eq first second same)
  exact congrArg (fun ids : Finset (MessageId Player) =>
    PMF.uniformOfFinset ids.powerset (Finset.powerset_nonempty ids)) pool

/-- Exact atom probabilities of the uniform-subset observation rule. -/
theorem leaks_subset_probability (who : Player)
    (pending : List (Message Player (WitnessedPacket nativeGraph)))
    (selected : Finset (MessageId Player)) :
    ((leaks who pending) selected).toReal =
      if selected ⊆ foreignPending who pending then
        ((2 : ℝ) ^ (foreignPending who pending).card)⁻¹ else 0 := by
  rw [leaks, PMF.uniformOfFinset_apply]
  by_cases subset : selected ⊆ foreignPending who pending
  · simp [subset, ENNReal.toReal_pow]
  · simp only [Finset.mem_powerset, subset, ↓reduceIte, ENNReal.toReal_zero]

/-- A singleton foreign pending pool has precisely the fair disclosure law. -/
theorem leaks_singleton (who : Player)
    (pending : List (Message Player (WitnessedPacket nativeGraph))) (id : MessageId Player)
    (single : foreignPending who pending = {id}) :
    leaks who pending = mix (1 / 2 : ℝ) (by norm_num) (by norm_num)
      (PMF.pure {id}) (PMF.pure ∅) := by
  ext selected
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    leaks_subset_probability, single, mix_apply_toReal]
  by_cases equal : selected = {id}
  · subst selected
    norm_num
  · by_cases empty : selected = ∅
    · subst selected
      norm_num [Ne.symm equal]
    · have outside : ¬ selected ⊆ ({id} : Finset (MessageId Player)) := by
        intro subset
        rcases Finset.subset_singleton_iff.mp subset with isEmpty | isSingleton
        · exact empty isEmpty
        · exact equal isSingleton
      simp [outside, equal, empty]

end Vegas.Examples.LateOpeningRuntimeObservation

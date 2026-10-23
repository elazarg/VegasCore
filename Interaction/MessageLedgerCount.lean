/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetwork

/-! # Processed identifiers per author

The modeled network never includes an identifier twice, but a deployed chain
may deliver duplicate transactions, and inclusion here does not itself check
whether an identifier was already included. A contract processes each
identifier once, so the number of an author's calls it has processed is the
number of distinct identifiers of that author on the ledger, whether each call
was accepted or rejected. An implementation keeps this number as the author's
nonce. When the author's identifiers on the ledger are exactly its serials
below a count, the number is that count, however many copies are included
(`Interaction.Message.distinctAuthoredCount_eq_of_serials`).
-/

namespace Interaction.Message

variable {Principal Payload : Type} [DecidableEq Principal]

/-- The number of distinct identifiers authored by `who` on `ledger`. -/
def distinctAuthoredCount (ledger : List (Message Principal Payload)) (who : Principal) : Nat :=
  ((ledger.map Message.id).toFinset.filter fun id => id.1 = who).card

@[simp] theorem distinctAuthoredCount_nil (who : Principal) :
    distinctAuthoredCount ([] : List (Message Principal Payload)) who = 0 := rfl

/-- When `who`'s identifiers on the ledger are exactly its serials below
`count`, the distinct count is `count`, however many copies are included. -/
theorem distinctAuthoredCount_eq_of_serials (ledger : List (Message Principal Payload))
    (who : Principal) (count : Nat)
    (below : ∀ message ∈ ledger, message.sender = who → message.id.2 < count)
    (present : ∀ serial < count, (who, serial) ∈ ledger.map Message.id) :
    distinctAuthoredCount ledger who = count := by
  unfold distinctAuthoredCount
  have same : ((ledger.map Message.id).toFinset.filter fun id => id.1 = who) =
      (Finset.range count).image (fun serial => (who, serial)) := by
    ext ⟨author, serial⟩
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_image, Finset.mem_range,
      Prod.mk.injEq]
    constructor
    · rintro ⟨member, rfl⟩
      obtain ⟨message, inside, identified⟩ := List.mem_map.mp member
      have bound := below message inside (congrArg Prod.fst identified)
      rw [identified] at bound
      exact ⟨serial, bound, rfl, rfl⟩
    · rintro ⟨index, lower, rfl, rfl⟩
      exact ⟨present index lower, rfl⟩
  rw [same, Finset.card_image_of_injective _ (fun first second equal => congrArg Prod.snd equal),
    Finset.card_range]

end Interaction.Message

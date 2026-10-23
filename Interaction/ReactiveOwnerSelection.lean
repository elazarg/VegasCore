/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveProvenance
import Interaction.ReactivePublication

/-! # Owner selection from recalled output

Authenticated unpublished envelopes of an owner are pending exactly when they
appear in that owner's output recall. When there is at most one eligible
envelope, the owner's recall determines which envelope the service selects.
-/

namespace Interaction.ReactiveApplication

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem respond_pending_mono (execution : app.Execution) (who : Principal) (action : app.Action) :
    execution.network.pending ⊆ (execution.respond app who action).network.pending := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact List.Subset.refl _
  | some material => exact List.subset_append_left _ _

theorem pending_iff_recalled (execution : app.Execution) (who : Principal)
    (message : Message Principal app.Payload) (authored : message.sender = who)
    (unpublished : message.id ∉ execution.network.ledger.map Message.id)
    (origins : execution.Provenance app) (recalled : execution.InputRecall app)
    (retained : execution.network.PendingOrPublished) :
    message ∈ execution.network.pending ↔ message ∈ app.outputs (execution.recall who) := by
  constructor
  · intro pending
    obtain ⟨entry, member, _, _, emitted, _⟩ := origins.pending message pending
    rw [authored] at member
    exact List.mem_filterMap.mpr ⟨entry, member, emitted⟩
  · intro output
    have known : message ∈ execution.network.known who := by
      rw [app.known_from_recall execution who recalled]
      exact List.mem_append_left _ (List.mem_append_left _ output)
    rcases retained.known who message known with pending | published
    · exact pending
    · exact (unpublished (List.mem_map.mpr ⟨message, published, rfl⟩)).elim

end Interaction.ReactiveApplication

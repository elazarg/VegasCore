/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

/-- A unique eligible authored envelope can be selected using own recall. -/
theorem find_pending_from_recall (execution : app.Execution) (who : Principal)
    (eligible : Message Principal app.Payload → Bool)
    (authored : ∀ message, eligible message = true → message.sender = who)
    (unpublished : ∀ message, eligible message = true →
      message.id ∉ execution.network.ledger.map Message.id)
    (origins : execution.Provenance app) (recalled : execution.InputRecall app)
    (retained : execution.network.PendingOrPublished)
    (unique : ∀ first ∈ app.outputs (execution.recall who),
      ∀ second ∈ app.outputs (execution.recall who),
        eligible first = true → eligible second = true → first = second) :
    execution.network.pending.reverse.find? eligible =
      (app.outputs (execution.recall who)).find? eligible := by
  have iffMember (message : Message Principal app.Payload) (good : eligible message = true) :
      message ∈ execution.network.pending.reverse ↔
        message ∈ app.outputs (execution.recall who) := by
    rw [List.mem_reverse]
    exact app.pending_iff_recalled execution who message (authored message good)
      (unpublished message good) origins recalled retained
  cases left : execution.network.pending.reverse.find? eligible with
  | none =>
      cases right : (app.outputs (execution.recall who)).find? eligible with
      | none => rfl
      | some message =>
          have good := List.find?_some right
          have pending := (iffMember message good).mpr (List.mem_of_find?_eq_some right)
          exact (List.find?_eq_none.mp left message pending good).elim
  | some first =>
      have firstGood := List.find?_some left
      have firstMem := (iffMember first firstGood).mp (List.mem_of_find?_eq_some left)
      cases right : (app.outputs (execution.recall who)).find? eligible with
      | none =>
          exact (List.find?_eq_none.mp right first firstMem firstGood).elim
      | some second =>
          exact congrArg some (unique first firstMem second
            (List.mem_of_find?_eq_some right) firstGood (List.find?_some right))

end Interaction.ReactiveApplication

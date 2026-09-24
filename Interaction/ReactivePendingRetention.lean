/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePublication

/-! # An inclusion can remove only its selected envelope

This carrier fact holds even with replay copies and duplicate identifiers.
Acceptance belongs to the application; the selection fact identifies the
precise envelope for which that obligation must be proved.
-/

namespace Interaction.ReactiveApplication

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem includePending_retained_or_selected (execution : app.Execution)
    (id : MessageId Principal) (message : Message Principal app.Payload)
    (pending : message ∈ execution.network.pending) :
    message ∈ (execution.includePending app id).network.pending ∨
      execution.network.lookup id = some message := by
  rw [app.includePending_network]
  cases found : execution.network.lookup id with
  | none => exact Or.inl (by simpa only [MessageNetwork.includePending, found] using pending)
  | some selected =>
      rcases MessagePool.mem_removeFirst_or_found id execution.network.pending message pending with
        retained | selected
      · exact Or.inl (by simpa only [MessageNetwork.includePending, found] using retained)
      · exact Or.inr (found.symm.trans selected)

end Interaction.ReactiveApplication

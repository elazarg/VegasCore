/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountVerdict

/-! # Uniqueness of permitted packets for a physical event address -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount.Permits

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {traffic : List (Message Player (CommitAttemptPacket graph))}
  {first second : Message Player (CommitAttemptPacket graph)}

/-- Permanent author serials and FIRST give a unique complete signed envelope
for each owner and physical attempt event, even after reset. -/
theorem eq_of_same_event (firstAllowed : Permits traffic first)
    (secondAllowed : Permits traffic second)
    (firstInput : first ∈ traffic) (secondInput : second ∈ traffic)
    (identified : ∀ left ∈ traffic, ∀ right ∈ traffic, left.id = right.id → left = right)
    (sender : first.sender = second.sender)
    (event : event? first.payload = event? second.payload) : first = second := by
  rcases lt_trichotomy first.id.2 second.id.2 with earlier | same | later
  · exact (secondAllowed.2.2.1 first ⟨firstInput, sender, earlier⟩ event).elim
  · exact identified first firstInput second secondInput (Prod.ext sender same)
  · exact (firstAllowed.2.2.1 second ⟨secondInput, sender.symm, later⟩ event.symm).elim

end Vegas.EventGraphRuntime.PhaseCount.Permits

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountVerdict

/-! # Uniqueness of count-permitted signed packets

The count verdict forbids an earlier own packet for the same event and forbids
reusing a commitment handle. Distinct authenticated identifiers turn these
serial comparisons into equality of the complete signed envelopes.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.CountPermits

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {traffic : List (Message Player (WitnessedPacket graph))}
  {first second : Message Player (WitnessedPacket graph)}

theorem eq_of_same_event (firstAllowed : CountPermits traffic first)
    (secondAllowed : CountPermits traffic second)
    (firstInput : first ∈ traffic) (secondInput : second ∈ traffic)
    (identified : ∀ left ∈ traffic, ∀ right ∈ traffic, left.id = right.id → left = right)
    (sender : first.sender = second.sender)
    (event : first.payload.call.event? graph = second.payload.call.event? graph) :
    first = second := by
  rcases lt_trichotomy first.id.2 second.id.2 with earlier | same | later
  · exact (secondAllowed.2.2 first ⟨firstInput, sender, earlier⟩ event).elim
  · exact identified first firstInput second secondInput (Prod.ext sender same)
  · exact (firstAllowed.2.2 second ⟨secondInput, sender.symm, later⟩ event.symm).elim

theorem commitment_eq_of_handle (firstAllowed : CountPermits traffic first)
    (secondAllowed : CountPermits traffic second)
    (firstInput : first ∈ traffic) (secondInput : second ∈ traffic)
    (identified : ∀ left ∈ traffic, ∀ right ∈ traffic, left.id = right.id → left = right)
    {firstEvent secondEvent : graph.EventId} {candidate : Handle graph}
    (firstCall : first.payload.call = .commitment firstEvent candidate)
    (secondCall : second.payload.call = .commitment secondEvent candidate) :
    first = second := by
  have firstCorrect := firstAllowed.2.1
  have secondCorrect := secondAllowed.2.1
  rw [CountCallCorrect, firstCall] at firstCorrect
  rw [CountCallCorrect, secondCall] at secondCorrect
  obtain ⟨_, _, firstOwner, _, firstUnused⟩ := firstCorrect
  obtain ⟨_, _, secondOwner, _, secondUnused⟩ := secondCorrect
  have sender : first.sender = second.sender := firstOwner.symm.trans secondOwner
  rcases lt_trichotomy first.id.2 second.id.2 with earlier | same | later
  · exact (secondUnused first ⟨firstInput, sender, earlier⟩ firstEvent firstCall).elim
  · exact identified first firstInput second secondInput (Prod.ext sender same)
  · exact (firstUnused second ⟨secondInput, sender.symm, later⟩ secondEvent secondCall).elim

end Vegas.EventGraphRuntime.CountPermits

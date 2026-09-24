/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEvidenceOrigin
import Vegas.Pending.ReactivePacketEvidence

/-! # Certificate acquisition in the native commitment runtime

The actual certificate issuer satisfies the owner-or-forwarding contract.
Without passive observation, every certificate possessed by a foreign player
must occur in the ledger, regardless of the application accepting its call.
This is an all-history consequence of changing only the observation rule.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem openingEvidence_ownerIssued (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.packetEvidence leaks).OwnerIssued (fun fact => fact.handle.1) := by
  intro state who known material fact carried
  change fact ∈ (material.emit state who known).evidence.toList at carried
  have certified : (material.emit state who known).evidence = some fact := by
    simpa using carried
  rcases material.emit_origin state who known fact certified with own | received
  · exact Or.inl own.1
  · obtain ⟨message, member, certificate⟩ := received
    exact Or.inr ⟨message, member, by simp [packetEvidence, certificate]⟩

/-- Every legal native prefix obeys the acquisition restriction, including
arbitrary deviations, forwarding, replays, rejected calls and scheduler choices.
The publication may be rejected by the game; it still carries public evidence. -/
theorem foreign_certificate_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (emptyObservation : ∀ who pending, leaks who pending = FinDist.pure ∅)
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (who : Player) (message : Message Player (WitnessedPacket graph))
    (known : message ∈ control.execution.network.known who) (fact : OpeningFact graph)
    (carried : message.payload.evidence = some fact) (foreign : fact.handle.1 ≠ who) :
    ∃ publication ∈ control.execution.network.ledger,
      publication.payload.evidence = some fact := by
  obtain ⟨publication, member, certified⟩ :=
    (runtime.packetEvidence leaks).foreign_known_published (fun fact => fact.handle.1)
      (runtime.openingEvidence_ownerIssued leaks) emptyObservation initial horizon scheduler
      control trace who message known fact (by
        simp [packetEvidence, carried]) foreign
  exact ⟨publication, member, by
    change fact ∈ publication.payload.evidence.toList at certified
    simpa using certified⟩

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePolicy

/-! # Canonical certified opening packets

The public format admits only an opening with its exactly matching certificate.
Accepted packets in this format identify the current binding's fixed value.
Owned and forwarded requests for that certificate have the same semantic normal
form, without assuming an empty known-packet list or a particular value type.

This is a packet-format theorem. Readiness, deadlines and source conformance
remain separate obligations. In particular, a truthful opening can still yield
guard-rejected publication failure; identifying it with a source opening requires
guard-free code or a proof that the publication checks succeed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The packet admits neither missing/mismatching evidence nor another call kind.
It does not inspect a private expected value, event phase, or source strategy. -/
def certifiedOpening (packet : WitnessedPacket graph) : Bool :=
  match packet.call, packet.evidence with
  | .opening _ candidate raw, some fact => decide (fact = ⟨candidate, raw⟩)
  | _, _ => false

theorem certifiedOpening_iff (packet : WitnessedPacket graph) :
    certifiedOpening packet = true ↔
      ∃ event candidate raw token, packet =
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩, token⟩ := by
  constructor
  · intro conforming
    rcases packet with ⟨call, evidence, token⟩
    cases call <;> cases evidence <;>
      simp only [certifiedOpening, Bool.false_eq_true, decide_eq_true_eq] at conforming
    rename_i event candidate raw fact
    subst fact
    exact ⟨event, candidate, raw, token, rfl⟩
  · rintro ⟨event, candidate, raw, token, rfl⟩
    simp only [certifiedOpening, decide_true]

end Vegas.EventGraphRuntime

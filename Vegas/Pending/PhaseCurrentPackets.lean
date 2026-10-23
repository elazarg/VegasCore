/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseInputNamespace
import Vegas.Pending.PhaseCountMenu

/-! # Latest signed bindings in the current physical namespace

Actual namespace order and the first-packet rule together force a signed
current-attempt binding to be the latest own binding for that source field.
This uses physical input serials, not an assumed accepting receipt.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A current-attempt first binding cannot have a later permitted own binding
to the same source field, whether that other packet was included or not. -/
theorem current_binding_latest (execution : (app).Execution)
    (namespaces : InputNamespaces runtime leaks execution)
    (clean : CountClean runtime leaks execution)
    (message : Message Player (CommitAttemptPacket graph))
    (present : message ∈ execution.network.inputs)
    (current : message.payload.attempt = execution.application.attempt)
    (event : graph.EventId) (candidate : Handle graph)
    (sent : message.payload.packet.call = .commitment event candidate) :
    ∀ other ∈ execution.network.inputs, other.sender = message.sender → ∀ handle,
      other.payload.packet.call = .commitment event handle → other.id.2 ≤ message.id.2 := by
  intro other otherMem same handle otherSent
  by_contra notLower
  have lower : message.id.2 < other.id.2 := Nat.lt_of_not_ge notLower
  have next := namespaces.monotone message present other otherMem same.symm lower
  have bounded := namespaces.bounded other otherMem
  have generation : message.payload.attempt.generation = other.payload.attempt.generation := by
    exact Nat.le_antisymm next.1 (by simpa only [current] using bounded.1)
  have phase : message.payload.attempt.phase = other.payload.attempt.phase := by
    exact Nat.le_antisymm next.2 (by simpa only [current] using bounded.2)
  have sameAttempt : message.payload.attempt = other.payload.attempt := by
    cases left : message.payload.attempt with
    | mk leftPhase leftGeneration =>
        cases right : other.payload.attempt with
        | mk rightPhase rightGeneration =>
            simp only [left, right] at generation phase
            cases generation
            cases phase
            rfl
  have sameEvent : event? message.payload = event? other.payload := by
    simp only [event?, sent, otherSent, Payload.event?, Option.map_some, sameAttempt]
  have permitted := (permits_eq_true_iff execution.network.inputs other).mp (clean.2 other otherMem)
  exact permitted.2.2.1 message ⟨present, same.symm, lower⟩ sameEvent

end Vegas.EventGraphRuntime.PhaseCount

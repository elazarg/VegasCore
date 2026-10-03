/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingUsableStep
import Vegas.Pending.ReactiveBindingInertClosure

/-! # Commitment provenance through later fresh usable registrations

Each actual owner-authored commitment has either completed its addressed event
or names a fixed candidate with the same meaning on both coupled executions.
Old completed commitments remain inert; new matching candidates can complete
with their actual value or expire. This is an operational relation on real
traffic, not a runtime observation, retained risk-menu claim or utility bound.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- Every emitted valid owner commitment is inert by completion, or has an
actual fixed candidate whose meaning agrees across the two executions. -/
def OwnerCommitmentsSettledOrMatching (owner : Player)
    (original repaired : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ message ∈ original.network.inputs, message.sender = owner → ∀ event candidate,
    message.payload.call = .commitment event candidate → message.payload.tokenValid = true →
      event ∈ original.application.config.cut.completed ∨
        (original.application.candidates.lookup candidate ≠ .fresh ∧
          original.application.candidates.lookup candidate =
            repaired.application.candidates.lookup candidate)

namespace OwnerCommitmentsSettledOrMatching

variable {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Any real response on either side retains an old completed event or an old
fixed matching candidate. No equality of response actions is needed. -/
private theorem respond_old
    (held : OwnerCommitmentsSettledOrMatching owner original repaired)
    (actor : Player) (left right : (runtime.reactiveApplication leaks).Action)
    (message : Message Player (WitnessedPacket graph)) (member : message ∈ original.network.inputs)
    (authored : message.sender = owner) (event : graph.EventId) (candidate : Handle graph)
    (committed : message.payload.call = .commitment event candidate)
    (valid : message.payload.tokenValid = true) :
    let nextLeft := original.respond (runtime.reactiveApplication leaks) actor left
    let nextRight := repaired.respond (runtime.reactiveApplication leaks) actor right
    event ∈ nextLeft.application.config.cut.completed ∨
      (nextLeft.application.candidates.lookup candidate ≠ .fresh ∧
        nextLeft.application.candidates.lookup candidate =
          nextRight.application.candidates.lookup candidate) := by
  intro nextLeft nextRight
  rcases held message member authored event candidate committed valid with completed | matching
  · left
    rw [(runtime.reactive_respond_application leaks original actor left).1]
    exact completed
  · right
    have leftEq := runtime.reactive_respond_candidate_fixed leaks original actor left candidate
      matching.1
    have rightEq := runtime.reactive_respond_candidate_fixed leaks repaired actor right candidate
      (matching.2 ▸ matching.1)
    rw [leftEq, rightEq]
    exact matching

/-- Arbitrary foreign responses and owner noncommitment responses preserve
provenance. An owner may still send openings, explicit FALSE, silence or malformed data. -/
theorem respond_noncommitment
    (held : OwnerCommitmentsSettledOrMatching owner original repaired)
    (actor : Player) (left right : (runtime.reactiveApplication leaks).Action)
    (noncommitment : actor = owner → ∀ material, left.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate) :
    OwnerCommitmentsSettledOrMatching owner
      (original.respond (runtime.reactiveApplication leaks) actor left)
      (repaired.respond (runtime.reactiveApplication leaks) actor right) := by
  intro message member authored event candidate committed valid
  rcases left with ⟨transmission⟩
  cases transmission with
  | none =>
      exact respond_old held actor ⟨none⟩ right message member authored event candidate committed
        valid
  | some material =>
      change message ∈ original.network.inputs ++ [_] at member
      rcases List.mem_append.mp member with old | added
      · exact respond_old held actor ⟨some material⟩ right message old authored event candidate
          committed valid
      · cases List.mem_singleton.mp added
        change actor = owner at authored
        have called : material.call.packet = .commitment event candidate := by
          exact (material.emit_call _ _ _).symm.trans committed
        exact (noncommitment authored material rfl event candidate called).elim

/-- A fresh shared binding registration establishes a matching fixed meaning
for its new actual envelope, while all prior commitment resources persist. -/
theorem respond_fresh_binding
    (held : OwnerCommitmentsSettledOrMatching owner original repaired)
    (event : graph.EventId) (serial : Nat) (raw : Raw L)
    (leftFresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (rightFresh : repaired.application.candidates.lookup (owner, .prepared serial) = .fresh) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), some raw⟩, .none⟩⟩
    OwnerCommitmentsSettledOrMatching owner (original.respond app owner response)
      (repaired.respond app owner response) := by
  intro app response message member authored named candidate committed valid
  change message ∈ original.network.inputs ++ [_] at member
  rcases List.mem_append.mp member with old | added
  · exact respond_old held owner response response message old authored named candidate committed
      valid
  · cases List.mem_singleton.mp added
    let material : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, .prepared serial), some raw⟩, .none⟩
    change (material.emit (app.submit original.application owner material) owner
      (original.network.known owner)).call = .commitment named candidate at committed
    have called : Payload.commitment event (owner, .prepared serial) =
        .commitment named candidate :=
      (material.emit_call (app.submit original.application owner material) owner
        (original.network.known owner)).symm.trans committed
    cases called
    have leftEq := runtime.bareBinding_submitted_openable leaks original owner event serial raw
      leftFresh
    have rightEq := runtime.bareBinding_submitted_openable leaks repaired owner event serial raw
      rightFresh
    right
    rw [leftEq, rightEq]
    exact ⟨by simp, rfl⟩

/-- Paired actual scheduler transitions preserve the traffic relation under
all commands, including inclusion, rejected calls, chance draws and overdue expiry. -/
theorem environment
    (held : OwnerCommitmentsSettledOrMatching owner original repaired)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (leftMoved : left ∈ (original.environmentStep (runtime.reactiveApplication leaks)
      command).support)
    (rightMoved : right ∈ (repaired.environmentStep (runtime.reactiveApplication leaks)
      command).support) : OwnerCommitmentsSettledOrMatching owner left right := by
  intro message member authored event candidate committed valid
  rw [(runtime.reactiveApplication leaks).environmentStep_inputs original left command leftMoved]
    at member
  rcases held message member authored event candidate committed valid with completed | matching
  · left
    have retained := (runtime.reactiveCompletedInvariant leaks
      original.application.config.cut.completed).environmentStep original left command
        (Finset.Subset.refl _) leftMoved
    exact retained completed
  · right
    have leftEq := runtime.reactive_environment_candidate_fixed leaks original left command
      candidate matching.1 leftMoved
    have rightEq := runtime.reactive_environment_candidate_fixed leaks repaired right command
      candidate (matching.2 ▸ matching.1) rightMoved
    rw [leftEq, rightEq]
    exact matching

end OwnerCommitmentsSettledOrMatching

end Vegas.EventGraphRuntime

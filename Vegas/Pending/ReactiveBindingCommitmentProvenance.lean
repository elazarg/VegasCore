/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingUsedCommitment
import Vegas.Pending.ReactiveBindingInertClosure
import Vegas.Pending.ReactiveBindingCopiedSubmission

/-! # Commitment provenance through fresh and reused owned handles

Each actual owner-authored commitment has completed its addressed event,
uses an already associated handle, or names a fixed candidate with the same
meaning on both coupled executions. Associated handles reject every later
commitment; new matching candidates can complete with their actual value or expire.
This is an operational relation on real traffic, not a runtime observation,
retained risk-menu claim or utility bound.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- Every emitted valid owner commitment is inert by completion or a
publicly accepted association, or has an actual fixed matching meaning. -/
def OwnerCommitmentsInertOrMatching (owner : Player)
    (original repaired : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ message ∈ original.network.inputs, message.sender = owner → ∀ event candidate,
    message.payload.call = .commitment event candidate → message.payload.tokenValid = true →
      event ∈ original.application.config.cut.completed ∨
        (∃ field, original.application.accepted field = some candidate) ∨
        (original.application.candidates.lookup candidate ≠ .fresh ∧
          original.application.candidates.lookup candidate =
            repaired.application.candidates.lookup candidate)

namespace OwnerCommitmentsInertOrMatching

variable {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Any real response on either side retains an old completed event, used
association or fixed matching candidate. No equality of response actions is needed. -/
private theorem respond_old
    (held : OwnerCommitmentsInertOrMatching owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (actor : Player) (left right : (runtime.reactiveApplication leaks).Action)
    (message : Message Player (WitnessedPacket graph)) (member : message ∈ original.network.inputs)
    (authored : message.sender = owner) (event : graph.EventId) (candidate : Handle graph)
    (committed : message.payload.call = .commitment event candidate)
    (valid : message.payload.tokenValid = true) :
    let nextLeft := original.respond (runtime.reactiveApplication leaks) actor left
    let nextRight := repaired.respond (runtime.reactiveApplication leaks) actor right
    event ∈ nextLeft.application.config.cut.completed ∨
      (∃ field, nextLeft.application.accepted field = some candidate) ∨
      (nextLeft.application.candidates.lookup candidate ≠ .fresh ∧
        nextLeft.application.candidates.lookup candidate =
          nextRight.application.candidates.lookup candidate) := by
  intro nextLeft nextRight
  rcases held message member authored event candidate committed valid with
    completed | used | matching
  · left
    rw [(runtime.reactive_respond_application leaks original actor left).1]
    exact completed
  · right; left
    obtain ⟨field, associated⟩ := used
    exact ⟨field, ((runtime.reactiveAssociationInvariant leaks field candidate).respond
      original actor left ⟨leftBinding, associated⟩).2⟩
  · right; right
    have leftEq := runtime.reactive_respond_candidate_fixed leaks original actor left candidate
      matching.1
    have rightEq := runtime.reactive_respond_candidate_fixed leaks repaired actor right candidate
      (matching.2 ▸ matching.1)
    rw [leftEq, rightEq]
    exact matching

/-- Arbitrary foreign responses and owner noncommitment responses preserve
provenance. An owner may still send openings, explicit FALSE, silence or malformed data. -/
theorem respond_noncommitment
    (held : OwnerCommitmentsInertOrMatching owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (actor : Player) (left right : (runtime.reactiveApplication leaks).Action)
    (noncommitment : actor = owner → ∀ material, left.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate) :
    OwnerCommitmentsInertOrMatching owner
      (original.respond (runtime.reactiveApplication leaks) actor left)
      (repaired.respond (runtime.reactiveApplication leaks) actor right) := by
  intro message member authored event candidate committed valid
  rcases left with ⟨transmission⟩
  cases transmission with
  | none =>
      exact respond_old held leftBinding actor ⟨none⟩ right message member authored event
        candidate committed valid
  | some material =>
      change message ∈ original.network.inputs ++ [_] at member
      rcases List.mem_append.mp member with old | added
      · exact respond_old held leftBinding actor ⟨some material⟩ right message old authored
          event candidate committed valid
      · cases List.mem_singleton.mp added
        change actor = owner at authored
        have called : material.call.packet = .commitment event candidate := by
          exact (material.emit_call _ _ _).symm.trans committed
        exact (noncommitment authored material rfl event candidate called).elim

/-- A fresh shared binding registration establishes a matching fixed meaning
for its new actual envelope, while all prior commitment resources persist. -/
theorem respond_fresh_binding
    (held : OwnerCommitmentsInertOrMatching owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    {memory : BindingMemory runtime leaks}
    (frame : BindingMemory.Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    OwnerCommitmentsInertOrMatching owner (original.respond app owner response)
      (repaired.respond app owner response) := by
  intro app response message member authored named candidate committed valid
  change message ∈ original.network.inputs ++ [_] at member
  rcases List.mem_append.mp member with old | added
  · exact respond_old held leftBinding owner response response message old authored named
      candidate committed valid
  · cases List.mem_singleton.mp added
    let material : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩
    change (material.emit (app.submit original.application owner material) owner
      (original.network.known owner)).call = .commitment named candidate at committed
    have called : Payload.commitment event (owner, .prepared serial) =
        .commitment named candidate :=
      (material.emit_call (app.submit original.application owner material) owner
        (original.network.known owner)).symm.trans committed
    cases called
    right; right
    have meaning := frame.copied_binding_fresh_meaning event serial opening fresh
    exact ⟨meaning.1, meaning.2.1⟩

/-- A reused fixed owned handle emits a commitment with the same actual
meaning on both executions. Neither new registration nor typed private data
is needed; all old completed-or-matching commitment resources persist. -/
theorem respond_matching_binding
    (held : OwnerCommitmentsInertOrMatching owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (event : graph.EventId) (slot : CandidateSlot graph) (opening : Option (Raw L))
    (fixed : original.application.candidates.lookup (owner, slot) ≠ .fresh)
    (same : original.application.candidates.lookup (owner, slot) =
      repaired.application.candidates.lookup (owner, slot)) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action := ⟨some ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩⟩
    OwnerCommitmentsInertOrMatching owner (original.respond app owner response)
      (repaired.respond app owner response) := by
  intro app response message member authored named candidate committed valid
  change message ∈ original.network.inputs ++ [_] at member
  rcases List.mem_append.mp member with old | added
  · exact respond_old held leftBinding owner response response message old authored named
      candidate committed valid
  · cases List.mem_singleton.mp added
    let material : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩
    change (material.emit (app.submit original.application owner material) owner
      (original.network.known owner)).call = .commitment named candidate at committed
    have called : Payload.commitment event (owner, slot) = .commitment named candidate :=
      (material.emit_call (app.submit original.application owner material) owner
        (original.network.known owner)).symm.trans committed
    cases called
    right; right
    rw [runtime.reactive_respond_candidate_fixed leaks original owner response (owner, slot) fixed,
      runtime.reactive_respond_candidate_fixed leaks repaired owner response (owner, slot)
        (same ▸ fixed)]
    exact ⟨fixed, same⟩

/-- A copied commitment to a publicly associated handle needs no equality
of private meanings: the association persists and forbids later binding acceptance. -/
theorem respond_associated_binding
    (held : OwnerCommitmentsInertOrMatching owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (event : graph.EventId) (slot : CandidateSlot graph) (opening : Option (Raw L))
    (field : graph.Field) (associated : original.application.accepted field = some (owner, slot)) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action := ⟨some ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩⟩
    OwnerCommitmentsInertOrMatching owner (original.respond app owner response)
      (repaired.respond app owner response) := by
  intro app response message member authored named candidate committed valid
  change message ∈ original.network.inputs ++ [_] at member
  rcases List.mem_append.mp member with old | added
  · exact respond_old held leftBinding owner response response message old authored named candidate
      committed valid
  · cases List.mem_singleton.mp added
    let material : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩
    change (material.emit (app.submit original.application owner material) owner
      (original.network.known owner)).call = .commitment named candidate at committed
    have called : Payload.commitment event (owner, slot) = .commitment named candidate :=
      (material.emit_call (app.submit original.application owner material) owner
        (original.network.known owner)).symm.trans committed
    cases called
    right; left
    exact ⟨field, ((runtime.reactiveAssociationInvariant leaks field (owner, slot)).respond
      original owner response ⟨leftBinding, associated⟩).2⟩

/-- Paired actual scheduler transitions preserve the traffic relation under
all commands, including inclusion, rejected calls, chance draws and overdue expiry. -/
theorem environment
    (held : OwnerCommitmentsInertOrMatching owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (leftMoved : left ∈ (original.environmentStep (runtime.reactiveApplication leaks)
      command).support)
    (rightMoved : right ∈ (repaired.environmentStep (runtime.reactiveApplication leaks)
      command).support) : OwnerCommitmentsInertOrMatching owner left right := by
  intro message member authored event candidate committed valid
  rw [(runtime.reactiveApplication leaks).environmentStep_inputs original left command leftMoved]
    at member
  rcases held message member authored event candidate committed valid with
    completed | used | matching
  · left
    have retained := (runtime.reactiveCompletedInvariant leaks
      original.application.config.cut.completed).environmentStep original left command
        (Finset.Subset.refl _) leftMoved
    exact retained completed
  · right; left
    obtain ⟨field, associated⟩ := used
    exact ⟨field, ((runtime.reactiveAssociationInvariant leaks field candidate).environmentStep
      original left command ⟨leftBinding, associated⟩ leftMoved).2⟩
  · right; right
    have leftEq := runtime.reactive_environment_candidate_fixed leaks original left command
      candidate matching.1 leftMoved
    have rightEq := runtime.reactive_environment_candidate_fixed leaks repaired right command
      candidate (matching.2 ▸ matching.1) rightMoved
    rw [leftEq, rightEq]
    exact matching

end OwnerCommitmentsInertOrMatching

end Vegas.EventGraphRuntime

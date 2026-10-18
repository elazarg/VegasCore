/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperOriginalFrameLaw
import Vegas.Examples.CommitSeedBroadcastInitialPublicLaw
import Vegas.Examples.CommitSeedBroadcastInitialPacketOrigins

/-! # A single public initial packet determines the original helper frame -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem response_inputs_owned (execution : app.Execution) (owner hidden : Player)
    (response : app.Action) :
    (∀ message ∈ (execution.respond app owner response).network.inputs,
      message.sender = hidden) ↔
    (∀ message ∈ execution.network.inputs, message.sender = hidden) ∧
      (owner ≠ hidden → response.transmission = none) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp only [ReactiveApplication.Execution.respond, implies_true, and_true]
  | some material =>
      change (∀ message ∈ execution.network.inputs ++
        [(⟨(owner, execution.network.nextSerial owner),
          app.packet (app.submit execution.application owner material) owner
            (execution.network.known owner) material⟩ : Message Player app.Payload)],
        message.sender = hidden) ↔ _
      simp only [List.mem_append, List.mem_singleton, Message.sender,
        Option.some_ne_none, imp_false, not_not]
      constructor
      · intro all
        exact ⟨fun message member => all message (Or.inl member), all _ (Or.inr rfl)⟩
      · rintro ⟨old, own⟩ message (member | equal)
        · exact old message member
        · subst message
          exact own

open Classical in
/-- The retained original public packet set is the actual initial traffic;
the two clock transitions neither replace it nor discard private preparation. -/
theorem initialClockTwo_public_packets (first second third : app.Action) :
    initialPublicPackets (initialClockTwo first second third) =
      (afterInitialResponses first second third).network.inputs.toFinset := by
  rfl

private theorem action_silent (response : app.Action) :
    response.transmission = none ↔ response = ⟨none⟩ := by
  cases response with
  | mk transmission => cases transmission <;> simp

private theorem initial_inputs_owned (first second third : app.Action) (hidden : Player) :
    (∀ message ∈ (afterInitialResponses first second third).network.inputs,
      message.sender = hidden) ↔
      (alice ≠ hidden → first = ⟨none⟩) ∧
        (bob ≠ hidden → second = ⟨none⟩) ∧ (carol ≠ hidden → third = ⟨none⟩) := by
  rw [afterInitialResponses, response_inputs_owned]
  change ((∀ message ∈ ((initialBobCallback first).respond app bob second).network.inputs,
    message.sender = hidden) ∧ _) ↔ _
  rw [response_inputs_owned]
  change (((∀ message ∈ (initialAliceCallback.respond app alice first).network.inputs,
    message.sender = hidden) ∧ _) ∧ _) ↔ _
  rw [response_inputs_owned]
  have empty : initialAliceCallback.network.inputs = [] := rfl
  simp only [empty, List.not_mem_nil, false_implies, implies_true, true_and,
    action_silent, and_assoc]

/-- At an actual initialized frame, a nonempty public initial word owned by
one helper forces every other initial response to be literal WAIT. This is an
observation argument on the entire raw frame, with no cleanliness premise. -/
theorem initial_single_helper_frame (seed : Seeds) (players : Player → app.Policy)
    (frame : app.Execution)
    (reached : frame ∈ (app.runRounds (family seed) players 5 initialExecution).support)
    (hidden : Player) (present : (initialPublicPackets frame).Nonempty)
    (owned : ∀ message ∈ initialPublicPackets frame, message.sender = hidden) :
    ∃ material : WitnessedSubmission graph, frame = initialHelperFrame hidden material := by
  classical
  rw [first_five_rounds] at reached
  obtain ⟨first, _first, secondReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨second, _second, thirdReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ secondReached)
  obtain ⟨third, _third, equal⟩ := PMF.support_map .. ▸ thirdReached
  subst frame
  rw [initialClockTwo_public_packets] at owned present
  have foreign : (alice ≠ hidden → first = ⟨none⟩) ∧
      (bob ≠ hidden → second = ⟨none⟩) ∧ (carol ≠ hidden → third = ⟨none⟩) :=
    (initial_inputs_owned first second third hidden).mp (by
      intro message member
      exact owned message (List.mem_toFinset.mpr member))
  have nonempty : (afterInitialResponses first second third).network.inputs ≠ [] := by
    intro empty
    rw [empty, List.toFinset_nil] at present
    exact Finset.not_nonempty_empty present
  fin_cases hidden
  · have secondEq := foreign.2.1 (by decide : bob ≠ alice)
    have thirdEq := foreign.2.2 (by decide : carol ≠ alice)
    subst second third
    rcases first with ⟨transmission⟩
    cases transmission with
    | none => exact False.elim (nonempty (afterInitialResponses_inputs_empty _ _ _ |>.mpr
        ⟨rfl, rfl, rfl⟩))
    | some material => exact ⟨material, rfl⟩
  · have firstEq := foreign.1 (by decide : alice ≠ bob)
    have thirdEq := foreign.2.2 (by decide : carol ≠ bob)
    subst first third
    rcases second with ⟨transmission⟩
    cases transmission with
    | none => exact False.elim (nonempty (afterInitialResponses_inputs_empty _ _ _ |>.mpr
        ⟨rfl, rfl, rfl⟩))
    | some material => exact ⟨material, rfl⟩
  · have firstEq := foreign.1 (by decide : alice ≠ carol)
    have secondEq := foreign.2.1 (by decide : bob ≠ carol)
    subst first second
    rcases third with ⟨transmission⟩
    cases transmission with
    | none => exact False.elim (nonempty (afterInitialResponses_inputs_empty _ _ _ |>.mpr
        ⟨rfl, rfl, rfl⟩))
    | some material => exact ⟨material, rfl⟩

end Vegas.Examples.CommitSeedBroadcast

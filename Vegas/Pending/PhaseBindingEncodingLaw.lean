/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSlotPolicy

/-! # Exact physical atoms of independently sampled binding slots -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- The physical encoding retains both the typed result and its chosen slot. -/
theorem phaseBindingResponse_eq_iff (who : Player) (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial other : Nat) :
    phaseBindingResponse runtime leaks who event payload first serial =
        phaseBindingResponse runtime leaks who event payload second other ↔
      serial = other ∧ first = second := by
  constructor
  · intro same
    have slots := congrArg (PhaseCandidates.responseCandidateSlot runtime leaks) same
    change some serial = some other at slots
    refine ⟨Option.some.inj slots, ?_⟩
    have prepared := congrArg (fun response : (phaseApplication runtime leaks).Action =>
      response.transmission.bind fun material => material.call.opening) same
    cases first with
    | failure =>
        cases second with
        | failure => rfl
        | success value => cases prepared
    | success firstValue =>
        cases second with
        | failure => cases prepared
        | success secondValue =>
            have typed := congrArg (fun raw : Option (Raw L) =>
              raw.bind (fun value => value.as? payload)) prepared
            simp only [phaseBindingResponse, Option.bind_some, Raw.as?_mk] at typed
            exact congrArg PublicationResult.success (Option.some.inj typed)
  · rintro ⟨rfl, rfl⟩
    rfl

namespace PhaseCount

variable [Fintype Player] (bounds : MessageBounds graph)

/-- An eligible raw sending atom is exactly its typed-result mass divided by
eligible-slot cardinality. Distinct slots and failed results are not merged. -/
theorem phaseBindingSlotPolicy_atom (who : Player) (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (serial : Nat) (eligible : serial ∈ phaseBindingSlots runtime leaks bounds who event payload
      past view) (result : PublicationResult (L.Val payload)) :
    phaseBindingSlotPolicy runtime leaks bounds who event payload results past view
        (phaseBindingResponse runtime leaks who event payload result serial) =
      ((phaseBindingSlots runtime leaks bounds who event payload past view).card : ENNReal)⁻¹ *
        results past view result := by
  classical
  have nonempty : (phaseBindingSlots runtime leaks bounds who event payload past view).Nonempty :=
    ⟨serial, eligible⟩
  rw [phaseBindingSlotPolicy, dite_eq_left nonempty, PMF.bind_apply]
  have inner (other : Nat) :
      ((results past view).map (phaseBindingResponse runtime leaks who event payload · other))
        (phaseBindingResponse runtime leaks who event payload result serial) =
      if serial = other then results past view result else 0 := by
    rw [PMF.map_apply]
    simp only [phaseBindingResponse_eq_iff]
    by_cases same : serial = other
    · simp only [same, true_and, ite_true]
      simpa only [eq_comm] using
        (tsum_ite_eq result (fun value : PublicationResult (L.Val payload) =>
          results past view value))
    · simp only [same, false_and, ite_false, tsum_zero]
  simp_rw [inner]
  have sumEq : (∑' other, PMF.uniformOfFinset
      (phaseBindingSlots runtime leaks bounds who event payload past view) nonempty other *
        (if serial = other then results past view result else 0)) =
      PMF.uniformOfFinset _ nonempty serial * results past view result := by
    simpa only [mul_ite, mul_zero, eq_comm] using
      (tsum_ite_eq serial (fun other => PMF.uniformOfFinset
        (phaseBindingSlots runtime leaks bounds who event payload past view) nonempty other *
          results past view result))
  rw [sumEq, PMF.uniformOfFinset_apply_of_mem nonempty eligible]

end PhaseCount
end Vegas.EventGraphRuntime

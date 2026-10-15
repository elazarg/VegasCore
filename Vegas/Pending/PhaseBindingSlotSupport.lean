/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseBindingSlotHistory

/-! # The fresh-slot law covers the handles of all permitted raw bindings -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

/-- A fixed wire-capacity denominator controls every eligible slot, even when
the number of surviving fresh slots varies across complete information fibers. -/
theorem phaseBindingSlotPolicy_bounded_mass
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (serial : Nat)
    (eligible : serial ∈ phaseBindingSlots runtime leaks bounds who event payload past view)
    (result : PublicationResult (L.Val payload)) :
    (bounds.candidateCount : ENNReal)⁻¹ * results past view result ≤
      phaseBindingSlotPolicy runtime leaks bounds who event payload results past view
        (phaseBindingResponse runtime leaks who event payload result serial) := by
  classical
  have cards : (phaseBindingSlots runtime leaks bounds who event payload past view).card ≤
      bounds.candidateCount := by
    unfold phaseBindingSlots
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have inverse : (bounds.candidateCount : ENNReal)⁻¹ ≤
      ((phaseBindingSlots runtime leaks bounds who event payload past view).card : ENNReal)⁻¹ :=
    ENNReal.inv_le_inv.mpr (by exact_mod_cast cards)
  exact (mul_le_mul' inverse le_rfl).trans
    (phaseBindingSlotPolicy_mass runtime leaks bounds who event payload results past view serial
      eligible result)

/-- Every admitted raw binding names an eligible slot of the source-preserving
law. Earlier retired attempts, ill-typed preparation and arbitrary evidence
requests are permitted by the statement; genuine legality derives freshness. -/
theorem binding_slot_mem_of_onePacket
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (preparation : Option (Raw L)) (evidence : EvidenceRequest graph)
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ onePacketActions runtime leaks bounds who
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)) :
    serial < bounds.candidateCount ∧
      control.execution.application.current.native.candidates.lookup
        (who, .prepared serial) = .fresh ∧
      serial ∈ phaseBindingSlots runtime leaks bounds who event payload
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who) := by
  have fresh := onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler trace
    who event serial preparation evidence member
  have available := ((mem_onePacketActions runtime leaks bounds who _ _ _).mp member).1
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at available
  have bounded : serial < bounds.candidateCount :=
    ((bounds.submissions_mem _ _).mp available).1.1
  exact ⟨bounded, fresh, mem_phaseBindingSlots_of_history runtime leaks bounds
    (onePacketMenu runtime leaks bounds) plan inputs horizon scheduler control trace who event
      payload outputEq request unsent values serial bounded fresh⟩

end Vegas.EventGraphRuntime.PhaseCount

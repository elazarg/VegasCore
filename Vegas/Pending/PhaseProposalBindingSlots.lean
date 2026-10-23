/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseBindingSlotPolicy

/-! # Every actually counted binding slot is available to the canonical encoder -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- The slot sampler includes the exact fresh serial of every allowed raw
binding response, regardless of its private preparation or evidence syntax.
Membership follows from the actual count history and available typed values. -/
theorem binding_slot_of_counted_response
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (execution.recall owner)
        (execution.observe app owner))
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
      (execution.recall owner) (execution.observe app owner) := by
  classical
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
  obtain ⟨actual, preparation, certificate, same, bounded, fresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler
      remaining owner execution trace event payload binding request material member
  have serialEq : actual = serial := by
    have call := congrArg (fun material : WitnessedSubmission graph => material.call.packet) same
    exact (Slot.prepared.inj (congrArg Prod.snd (Payload.commitment.inj call).2)).symm
  subst actual
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner execution trace ⟨execution.application.attempt, event⟩ request
      material member
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have recalled := PhaseCount.countRecall_history runtime leaks raw
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks _ horizon scheduler raw
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr bounded, fresh, ?_⟩
  intro result
  apply (PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mpr
  refine ⟨phaseBindingResponse_available runtime leaks bounds owner _ _ event payload values result
    serial bounded, Or.inr ?_⟩
  exact PhaseCount.phaseBindingResponse_permitted runtime leaks execution recalled fixed owner event
    payload binding request unsent result serial fresh

end Vegas.EventGraphRuntime.PhaseProposal

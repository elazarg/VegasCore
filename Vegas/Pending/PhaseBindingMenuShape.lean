/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseBindingFreshness

/-! # Actual permitted response shape at a current binding callback -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- A nonsilent counted response at a genuine binding request is a binding at
that exact event and a globally fresh prepared slot. Preparation and evidence
are retained verbatim, including unusable and wrongly typed preparations. -/
theorem onePacket_binding_shape (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (phaseApplication runtime leaks).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (member : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe (phaseApplication runtime leaks) owner)) :
    ∃ serial preparation evidence,
      material = ⟨⟨.commitment event (owner, .prepared serial), preparation⟩, evidence⟩ ∧
      serial < bounds.candidateCount ∧
      execution.application.current.native.candidates.lookup (owner, .prepared serial) =
        .fresh := by
  let app := phaseApplication runtime leaks
  have named := onePacket_event_of_request runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner execution trace ⟨execution.application.attempt, event⟩ request
      material member
  have permitted : permits ((app).outputs (execution.recall owner))
      (localEnvelope runtime leaks owner (execution.recall owner) (execution.observe app owner)
        material) = true := by
    rcases ((mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2 with
      impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((permits_eq_true_iff _ _).mp permitted).2.1
  have callEq : (nativeMessage (localEnvelope runtime leaks owner (execution.recall owner)
      (execution.observe app owner) material)).payload.call = material.call.packet :=
    maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [callEq] at correct
  rcases material with ⟨⟨packet, preparation⟩, evidence⟩
  cases packet with
  | malformed raw => cases correct
  | commitment other candidate =>
      have same : other = event := Option.some.inj named
      subst other
      obtain ⟨_bindingOwned, _uncertified, candidateOwner, ⟨serial, slot⟩, _unused⟩ := correct
      change candidate.1 = owner at candidateOwner
      have candidateEq : candidate = (owner, .prepared serial) := Prod.ext candidateOwner slot
      subst candidate
      have available := ((mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).1
      rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at available
      have bounded : serial < bounds.candidateCount :=
        ((bounds.submissions_mem _ _).mp available).1.1
      exact ⟨serial, preparation, evidence, rfl, bounded,
        onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler trace owner
          event serial preparation evidence member⟩
  | opening other candidate raw =>
      have same : other = event := Option.some.inj named
      subst other
      cases node : nodeView graph event with
      | bind actor ty kind code => simp only [node, and_false] at correct
      | resolve actor ty binding checks kind code => cases kind.symm.trans outputEq
      | sample ty law kind code => cases kind.symm.trans outputEq

end Vegas.EventGraphRuntime.PhaseCount

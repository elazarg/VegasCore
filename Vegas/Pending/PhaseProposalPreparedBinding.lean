/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalPreparedResponse
import Vegas.Pending.PhaseProposalPreparationResult

/-! # Actual binding responses extend persistent typed packet provenance -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Repairing one actual fresh preparation extends the physical packet
invariant. Older packets remain covered even at the same logical event in a
retired generation; only their own fixed candidate meanings are used. The
original raw private evidence alias remains in its owner's actual recall. -/
theorem PreparedBindings.binding_response {owner : Player}
    {original repaired : (app).Execution}
    (prepared : PreparedBindings runtime leaks owner original repaired)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (leftFresh : original.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (rightFresh : repaired.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh) :
    let replacement := match opening.bind (fun raw => raw.as? payload) with
      | none => some (⟨payload, L.someValue payload⟩ : Raw L)
      | some _ => opening
    let source : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩
    let target : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacement⟩, .none⟩⟩
    PreparedBindings runtime leaks owner (original.respond app owner source)
      (repaired.respond app owner target) := by
  intro replacement source target message member sender other candidate call domain otherOutput
    _otherCode _otherNode
  simp only [source, ReactiveApplication.Execution.respond, MessageNetwork.submit,
    List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact (prepared message prior sender other candidate call domain otherOutput
      _otherCode _otherNode).rebase
        ((phaseApplication_preservesFixedCandidates runtime leaks).respond original owner source)
        ((phaseApplication_preservesFixedCandidates runtime leaks).respond repaired owner target)
  · have actual := phase_emit_call
      (original.application.submit owner
        ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩)
      owner (original.network.known owner)
        ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
    have named := actual.symm.trans call
    change Payload.commitment event (owner, .prepared serial) =
      .commitment other candidate at named
    obtain ⟨rfl, rfl⟩ := Payload.commitment.inj named
    have sameDomain : payload = domain :=
      (EventField.binding.inj (outputEq.symm.trans otherOutput)).2
    subst domain
    exact prepared_binding_result runtime original.application.current.native
      repaired.application.current.native owner event payload serial opening leftFresh rightFresh

end Vegas.EventGraphRuntime.BindingShadow

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalOrigin

/-! # Submitted counted proposals came from actual successful binding values

The original callback and its typed stored binding are derived from the counted
history. The packet need not be pending, accepted or in the current attempt at
the endpoint where this theorem is used.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A counted proposal's plaintext is the actual typed binding value at its
genuine original requesting callback, even if delivery later fails. -/
theorem submitted_proposal_binding_meaning (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw)) :
    ∃ (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
      (owner : Player) (payload : L.Ty)
      (binding : FieldRef graph.layout (.binding owner payload))
      (checks : List (GuardCheck graph.layout payload))
      (outputEq : graph.outputLayout coordinate.event = .publication payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes coordinate.event) =
        .resolve owner payload binding checks) (value : L.Val payload),
      TracePrefix prior trace ∧ message.sender = owner ∧ before.actor = some owner ∧
      before.execution.application.SeedRequest owner coordinate ∧
      nodeView graph coordinate.event = .resolve owner payload binding checks outputEq codeEq ∧
      raw = ⟨payload, value⟩ ∧
      binding.get? before.execution.application.current.native.config.store =
        some (.success value) := by
  obtain ⟨before, prior, material, candidate, retained, acting, request, opening,
    offered, _stamp⟩ :=
    submitted_proposal_callback runtime leaks bounds plan ordered inputs horizon scheduler current
      trace message submitted coordinate raw proposed
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    _ horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message submitted)).2.1
  obtain ⟨_attempt, actualCandidate, call⟩ :=
    opening_of_packetProposal message.payload coordinate raw proposed
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [call] at correct
  have resolves := correct.2
  cases node : nodeView graph coordinate.event with
  | bind owner payload outputEq codeEq =>
      rw [node] at resolves
      exact resolves.elim
  | sample payload law outputEq codeEq =>
      rw [node] at resolves
      exact resolves.elim
  | resolve owner payload binding checks outputEq codeEq =>
      rw [node] at resolves
      have ownerEq : message.sender = owner := resolves.1
      rw [ownerEq] at request offered acting
      rcases before with ⟨remaining, actor, physical⟩
      cases acting
      have originalRequest : physical.application.SeedRequest owner
          ⟨physical.application.attempt, coordinate.event⟩ := by
        have same : (⟨coordinate.attempt, coordinate.event⟩ : CommitAttemptEvent graph) =
            coordinate := rfl
        rw [request.1] at same
        exact same.symm ▸ request
      obtain ⟨selected, value, emitted, stored, _accepted, _catalog⟩ :=
        PhaseCount.onePacket_opening_shape runtime leaks bounds plan ordered inputs horizon
          scheduler remaining owner physical prior coordinate.event payload binding checks
          outputEq codeEq node originalRequest material offered
      have typed : raw = (⟨payload, value⟩ : Raw L) :=
        (Payload.opening.inj (opening.symm.trans emitted)).2.2
      exact ⟨⟨remaining, some owner, physical⟩, prior, owner, payload, binding, checks,
        outputEq, codeEq, value, retained, ownerEq, rfl, request, rfl, typed, stored⟩

end Vegas.EventGraphRuntime.PhaseProposal

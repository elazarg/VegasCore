/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceConformance

/-! # An acceptable fresh call is accepted at any later inclusion in its window

The audit's public conformance rule `freshServiceEnvelope` checks a packet
against the public view its author saw. Its acceptance part
(`freshServiceAcceptable`) drops the canonical-serial requirement on
commitments, which the handler does not check. While no event has completed, the
public observation and accepted handles are unchanged, so the handler's public
conditions still hold at a later inclusion, provided it is before the event's
deadline. The handler's private conditions for an opening, the candidate's
opening and its stored binding value, follow from the packet's own certified
evidence and the binding provenance invariant at the inclusion state.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)

/-- The part of the audit's conformance rule that the handler's acceptance
needs. A commitment must only be includable: its candidate need not be the
author's canonical serial. Other packets must conform. -/
def freshServiceAcceptable (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  match message.payload.call with
  | .commitment event _ => view.BindingIncludable runtime ⟨message.id, message.payload.call⟩ ∧
      message.payload.token = some ⟨event⟩
  | _ => runtime.freshServiceEnvelope view message

/-- A conforming packet is acceptable. -/
theorem freshServiceEnvelope.acceptable {view : PublicView graph}
    {message : Message Player (WitnessedPacket graph)}
    (conforming : runtime.freshServiceEnvelope view message) :
    runtime.freshServiceAcceptable view message := by
  rcases message with ⟨id, ⟨packet, evidence, token⟩⟩
  cases packet with
  | commitment event candidate => exact ⟨conforming.1, conforming.2.2.2⟩
  | opening event candidate raw => exact conforming
  | malformed raw => exact conforming

/-- An acceptable fresh call carries the readiness token of its event. -/
theorem freshServiceAcceptable.tokenValid {view : PublicView graph}
    {message : Message Player (WitnessedPacket graph)}
    (conforming : runtime.freshServiceAcceptable view message) :
    message.payload.tokenValid = true := by
  rcases message with ⟨id, ⟨packet, evidence, token⟩⟩
  cases packet with
  | commitment event candidate =>
      obtain ⟨_, tokened⟩ := conforming
      change token = some ⟨event⟩ at tokened
      subst tokened
      exact WitnessedPacket.tokenValid_commitment _ _ _
  | opening event candidate raw =>
      cases node : nodeView graph event with
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨_, _, _, _, _, _, _, _, tokened⟩ :=
            (runtime.freshServiceEnvelope_opening_iff view id event owner payload binding checks
              outputEq codeEq node candidate raw evidence token).mp conforming
          subst tokened
          exact WitnessedPacket.tokenValid_opening _ _ _ _
      | bind _ _ _ _ =>
          simp only [freshServiceAcceptable, freshServiceEnvelope, node] at conforming
          exact conforming.2.2.2.2.elim
      | sample _ _ _ _ =>
          simp only [freshServiceAcceptable, freshServiceEnvelope, node] at conforming
          exact conforming.2.2.2.2.elim
  | malformed raw => exact conforming.elim

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceOpening
import Vegas.Pending.EventBindingInvariant

/-! # A conforming fresh call is accepted at any later inclusion in its window

The audit's public conformance rule `freshServiceEnvelope` checks a packet
against the public view its author saw. While no event has completed, the
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

/-- A packet that conformed to the public view its author saw is accepted at a
state with the same public observation and accepted handles, before the
event's deadline, when its certified evidence holds and binding provenance is
intact. -/
theorem freshServiceEnvelope_accepted (state : State graph) (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph))
    (conforming : runtime.freshServiceEnvelope view message)
    (observationEq : view.observation = state.publicView.observation)
    (acceptedEq : view.accepted = state.accepted)
    (event : graph.EventId) (named : message.payload.call.event? graph = some event)
    (timely : state.WithinDeadline runtime event)
    (certified : ∀ fact ∈ message.payload.evidence.toList, fact.Holds state)
    (invariant : state.BindingInvariant) :
    ∃ next, handle runtime state ⟨message.id, message.payload.call⟩ = some next := by
  rcases message with ⟨id, ⟨packet, evidence⟩⟩
  have readyOf (ready : view.EventReady event) : state.config.cut.Ready event := by
    have same : state.publicView.EventReady event := by
      unfold PublicView.EventReady at ready ⊢
      rw [← observationEq]
      exact ready
    exact (state.publicView_eventReady event).mp same
  cases packet with
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      obtain ⟨includable, _, _⟩ := conforming
      change view.EventReady event ∧ _ ∧ _ at includable
      obtain ⟨ready, _, owned⟩ := includable
      cases node : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          rw [node] at owned
          obtain ⟨sender, handleOwner, vacant, unused⟩ := owned
          rw [acceptedEq] at vacant unused
          exact ⟨_, runtime.handle_commitment_eq state id event candidate owner payload outputEq
            codeEq node (readyOf ready) timely sender handleOwner vacant unused⟩
      | resolve _ _ _ _ _ _ => rw [node] at owned; exact owned.elim
      | sample _ _ _ _ => rw [node] at owned; exact owned.elim
  | opening actual candidate raw =>
      change some actual = some event at named
      cases Option.some.inj named
      cases node : nodeView graph event with
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨ready, _, certifiedPacket, guards, sender, owned, associated, _⟩ :=
            (runtime.freshServiceEnvelope_opening_iff view id event owner payload binding checks
              outputEq codeEq node candidate raw evidence).mp conforming
          obtain ⟨value, rawEq, publicChecks⟩ :=
            (view.openingGuardsAccepted_iff owner event payload binding checks outputEq codeEq
              node candidate raw evidence).mp guards
          subst raw
          have evidenceEq : evidence = some ⟨candidate, ⟨payload, value⟩⟩ := by
            cases evidence with
            | none => simp only [certifiedOpening, Bool.false_eq_true] at certifiedPacket
            | some fact =>
                simp only [certifiedOpening, decide_eq_true_eq] at certifiedPacket
                exact congrArg some certifiedPacket
          have verified : state.candidates.lookup candidate = .openable ⟨payload, value⟩ :=
            certified ⟨candidate, ⟨payload, value⟩⟩ (by simp [evidenceEq])
          rw [acceptedEq] at associated
          have stored := invariant.opening_stored binding candidate value associated verified
          have acceptedChecks : GuardCheck.allAccepted? checks state.config.store
              (.success value) = some true := by
            rw [observationEq] at publicChecks
            change GuardCheck.allAccepted? checks (graph.publicStore state.config.store)
              (.success value) = some true at publicChecks
            rwa [GuardCheck.allAccepted?_publicStore] at publicChecks
          have resolved : EventCode.resolveOutput? binding checks true state.config.store =
              some (.success value) := by
            simp only [EventCode.resolveOutput?, stored, Option.bind_eq_bind, Option.bind_some,
              ↓reduceIte, acceptedChecks, Option.pure_def]
          exact ⟨_, runtime.handle_opening_eq state id event candidate owner payload binding
            checks outputEq codeEq node (readyOf ready) timely sender owned associated value
            verified stored (.success value) resolved⟩
      | bind _ _ _ _ =>
          simp only [freshServiceEnvelope, node] at conforming
          exact conforming.2.2.2.2.elim
      | sample _ _ _ _ =>
          simp only [freshServiceEnvelope, node] at conforming
          exact conforming.2.2.2.2.elim
  | withhold actual => exact conforming.elim
  | malformed raw => exact conforming.elim

end Vegas.EventGraphRuntime

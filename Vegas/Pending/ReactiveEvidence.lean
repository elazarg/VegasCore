/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEvidence
import Vegas.EventGraph.CommitmentEvidence
import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventStore

/-! # Native receipt decoding to semantic commitment evidence

Successful opening calls certify the referenced binding, including when the
game publication fails its guard. The decoded fact contains no handle, serial,
receipt or event address. Malformed and unsuccessful calls supply no certificate.
This decoder does not authenticate pending packets before inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Interpretation of an opening whose application receipt succeeds. -/
def Payload.bindingEvidence : Payload graph → List (EventGraph.CommitmentEvidence graph)
  | .opening event _ raw => match nodeView graph event with
    | .resolve owner payload binding _ _ _ =>
        match raw.as? payload with
        | some value => [⟨owner, payload, binding, value⟩]
        | none => []
    | .bind .. | .sample .. => []
  | .commitment .. | .withhold .. | .malformed .. => []

theorem reactiveEvidenceInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (fact : EventGraph.CommitmentEvidence graph) :
    (runtime.reactiveApplication leaks).Invariant (fun state => fact.Holds state.config.store) where
  submit state who material valid := by
    change fact.Holds (submitStep (material.register state who) who material.packet).config.store
    rw [submitStep_config, (material.register_facts who state).1]
    exact valid
  handle state message next valid accepted :=
    fact.holds_preserved _ _ (handle_store_of_some runtime state next message accepted) valid
  environment state command next valid reached :=
    fact.holds_preserved _ _
      (environmentStep_store_of_some runtime state next command reached) valid

theorem handle_bindingEvidence (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next)
    (fact : EventGraph.CommitmentEvidence graph)
    (decoded : fact ∈ message.payload.bindingEvidence) :
    fact.Holds next.config.store := by
  classical
  apply fact.holds_preserved state.config.store next.config.store
    (handle_store_of_some runtime state next message accepted)
  rcases message with ⟨id, packet⟩
  cases packet with
  | commitment | withhold | malformed => simp [Payload.bindingEvidence] at decoded
  | opening event candidate raw =>
      cases node : nodeView graph event with
      | sample | bind => simp [Payload.bindingEvidence, node] at decoded
      | resolve owner payload binding checks outputEq codeEq =>
          cases typed : raw.as? payload with
          | none => simp [Payload.bindingEvidence, node, typed] at decoded
          | some value =>
              simp only [Payload.bindingEvidence, node, typed, List.mem_singleton] at decoded
              subst fact
              change binding.get? state.config.store = some (.success value)
              by_contra absent
              simp only [handle, node] at accepted
              split at accepted <;> try cases accepted
              split at accepted <;> try cases accepted
              split at accepted <;> try cases accepted
              split at accepted <;> try cases accepted
              split at accepted <;> try cases accepted
              split at accepted <;> try cases accepted
              split at accepted
              · rename_i impossible
                rw [typed] at impossible
                cases impossible
              · rename_i decoded same
                have valueEq := Option.some.inj (same.symm.trans typed)
                subst decoded
                simp only [dite_eq_right absent] at accepted
                cases accepted

def receiptEvidence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) :
    (runtime.reactiveApplication leaks).ReceiptEvidence where
  Fact := EventGraph.CommitmentEvidence graph
  valid state fact := fact.Holds state.config.store
  decode := Payload.bindingEvidence
  persists := runtime.reactiveEvidenceInvariant leaks
  checked state message next := handle_bindingEvidence runtime state next message

end Vegas.EventGraphRuntime

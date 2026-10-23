/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveService
import Interaction.ReactiveProvenance
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveAllocation

/-! # Canonical revelation blocks in the existing reactive service

A source revelation chooses a certified opening or silence. Reserved inclusion
then consumes the sole opening packet; silence leaves expiry to resolve the
event. The equations concern actual executions and retain network and recall
effects. They do not restrict the raw response menu or assume player optimality.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The two source choices, using matching owned evidence on the opening branch.
Withholding emits no packet and is completed by the existing expiry command. -/
def canonicalRevealResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) (disclose : Bool) :
    (runtime.reactiveApplication leaks).Action :=
  ⟨if disclose then some (disclosureSubmission (.opening event candidate raw))
    else none⟩

theorem canonicalRevealResponse_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) (disclose : Bool) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.canonicalRevealResponse leaks event candidate raw disclose)).application =
        execution.application := by
  cases disclose <;> rfl

/-- Reserved inclusion never reprocesses an already published identifier. -/
theorem reactiveLatest_wait_of_pending_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (published : ∀ message ∈ view.network.pending,
      message.id ∈ view.network.ledger.map Message.id) :
    runtime.reactiveLatest leaks event owner view = .wait := by
  have absent : view.network.pending.reverse.find? (fun message =>
      message.sender = owner ∧ message.payload.call.event? graph = some event ∧
        view.Unpublished (runtime.reactiveApplication leaks) message.id) = none := by
    apply List.find?_eq_none.mpr
    intro message member
    have spent := published message (List.mem_reverse.mp member)
    simp only [ReactiveApplication.EnvironmentView.Unpublished, spent, not_true_eq_false,
      and_false, decide_false, Bool.false_eq_true, not_false_eq_true]
  simp only [reactiveLatest, absent]

end Vegas.EventGraphRuntime

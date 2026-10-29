/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveInvariant
import Vegas.Pending.EventBindingInvariant
import Vegas.Pending.ReactiveRuntime

/-! # Immutable binding provenance in raw ledger histories

Successful bindings and accepted handles retain their exact candidate meanings
through arbitrary player responses, inclusion, expiry and automatic completion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}


/-- Arbitrary responses, admissions and environment commands preserve binding
provenance in the single reactive application, including automatic completion. -/
theorem reactiveBindingInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).Invariant State.BindingInvariant where
  submit state who material valid := by
    apply submitStep_bindingInvariant _ _ who material.call.packet
    rw [material.call.register_eq]
    cases material.call.registrationCommand who with
    | none => exact valid
    | some command => exact privateStep_bindingInvariant state valid who command
  handle state message next valid accepted := by
    obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
    rw [← nextEq]
    exact (handle_bindingInvariant runtime state native ⟨message.id, message.payload.call⟩
      valid handled).drain
  environment state command next valid reached := by
    change next ∈ ((environmentStep runtime state command).map State.drain).support at reached
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    exact (environmentStep_bindingInvariant runtime state native command valid moved).drain

/-- Exact binding provenance holds at every initialized raw history, including
deviations and scheduler choices outside a reserved service. -/
theorem reactiveBindingInvariant_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant State.BindingInvariant state :=
  (runtime.reactiveBindingInvariant leaks).history (inputs.map State.initial) horizon scheduler
    (fun state member => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ member
      exact State.initial_bindingInvariant input) trace

end Vegas.EventGraphRuntime

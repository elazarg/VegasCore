/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.EventBindingInvariant

/-! # Previously observed openings authenticate later accepted bindings

A player may observe a candidate certificate before that candidate is used
by the game. Once its accepted association becomes public, the same evidence
certifies the typed graph binding. No new opening call, certificate delivery,
or successful opening receipt is required. The conclusion holds throughout
the observer's information set, including histories off the equilibrium path.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveBindingInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).Invariant State.BindingInvariant where
  submit state who material valid := by
    apply submitStep_bindingInvariant _ _ who material.call.packet
    rw [material.call.register_eq]
    cases material.call.registrationCommand who with
    | none => exact valid
    | some command => exact privateStep_bindingInvariant state valid who command
  handle state message next valid accepted :=
    handle_bindingInvariant runtime state next ⟨message.id, message.payload.call⟩ valid
      (reactiveHandle_call accepted)
  environment state command next valid reached :=
    environmentStep_bindingInvariant runtime state next command valid reached

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

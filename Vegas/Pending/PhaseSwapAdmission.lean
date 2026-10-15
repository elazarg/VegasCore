/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseReactiveValueSwap

/-! # Replay guards apply only to physically admitted phase calls -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Future phases, retired tokens and excluded actors are rejected before any
hidden binding value can be read. Only admitted calls need the native guards. -/
theorem handle_swap_of_admitted (runtime : EventGraphRuntime graph) (swap : HiddenSwap graph)
    (state : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (compatible : (message.payload.tokenValid state.attempt &&
        state.allows message.payload.packet.call &&
        !state.current.excludedCall message.payload.packet.call) = true →
      ∀ next event candidate, EventGraphRuntime.handle runtime state.current.native
        ⟨message.id, message.payload.packet.call⟩ = some next →
        message.payload.packet.call = .commitment event candidate →
        BindCompatible swap event candidate)
    (fixed : (message.payload.tokenValid state.attempt &&
        state.allows message.payload.packet.call &&
        !state.current.excludedCall message.payload.packet.call) = true →
      ∀ event, (∃ candidate raw, message.payload.packet.call = .opening event candidate raw) →
        state.current.native.config.cut.Ready event → RevealFixed swap state.current.native event) :
    (state.swap swap).handle runtime message =
      (state.handle runtime message).map (PhaseRuntimeState.swap swap) := by
  by_cases admitted : (message.payload.tokenValid state.attempt &&
      state.allows message.payload.packet.call &&
      !state.current.excludedCall message.payload.packet.call) = true
  · exact handle_swap runtime swap state message expiry
      (fun _ => compatible admitted) (fun _ => fixed admitted)
  · unfold handle
    change (if message.payload.tokenValid state.attempt &&
        state.allows message.payload.packet.call &&
        !state.current.excludedCall message.payload.packet.call then _ else none) = _
    split
    · rename_i accepted
      exact (admitted accepted).elim
    · rfl

/-- An admitted call in a commitment phase cannot open a future revelation,
even if the underlying graph alone already marks that revelation ready. -/
theorem handle_swap_commitment (runtime : EventGraphRuntime graph) (swap : HiddenSwap graph)
    (state : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (remaining : List (RuntimePhase graph)) (installed : state.phases = phase :: remaining)
    (kind : phase.kind = .commitment) (message : Message Player (CommitAttemptPacket graph))
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (compatible : (message.payload.tokenValid state.attempt &&
        state.allows message.payload.packet.call &&
        !state.current.excludedCall message.payload.packet.call) = true →
      ∀ next event candidate, EventGraphRuntime.handle runtime state.current.native
        ⟨message.id, message.payload.packet.call⟩ = some next →
        message.payload.packet.call = .commitment event candidate →
        BindCompatible swap event candidate) :
    (state.swap swap).handle runtime message =
      (state.handle runtime message).map (PhaseRuntimeState.swap swap) := by
  apply handle_swap_of_admitted runtime swap state message expiry compatible
  intro admitted event named _
  obtain ⟨candidate, raw, sent⟩ := named
  have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2
  have inside : event ∈ phase.events := by
    apply of_decide_eq_true
    simpa only [allows, installed, List.head?_cons, sent, Payload.event?] using allowed
  obtain ⟨lower, upper⟩ := phase.mem_events event |>.mp inside
  have binding := phase.fields event lower upper
  rw [kind] at binding
  obtain ⟨owner, payload, outputEq⟩ := binding
  unfold RevealFixed
  cases node : nodeView graph event with
  | bind | sample => trivial
  | resolve _ _ _ _ otherEq _ => cases otherEq.symm.trans outputEq

end PhaseRuntimeState

namespace HiddenSwap

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- Exact packet inclusion replay asks no native guard for a call rejected by
the phase gate. Every receipt and the permanent physical network are retained. -/
theorem includePending_phaseExecution_of_admitted (swap : HiddenSwap graph)
    (current : (phaseApplication runtime leaks).Execution) (id : MessageId Player)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (fixed : ∀ envelope, current.network.lookup id = some envelope →
      (envelope.payload.tokenValid current.application.attempt &&
        current.application.allows envelope.payload.packet.call &&
        !current.application.current.excludedCall envelope.payload.packet.call) = true →
      InclusionFixed runtime swap current.application.current.native
        ⟨envelope.id, envelope.payload.packet.call⟩) :
    (swap.phaseExecution current).includePending (phaseApplication runtime leaks) id =
      swap.phaseExecution (current.includePending (phaseApplication runtime leaks) id) := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  simp only [phaseExecution_network]
  cases found : current.network.lookup id with
  | none => rfl
  | some envelope =>
      have handled : (phaseApplication runtime leaks).handle
          (current.application.swap swap) envelope =
          ((phaseApplication runtime leaks).handle current.application envelope).map
            (PhaseRuntimeState.swap swap) :=
        PhaseRuntimeState.handle_swap_of_admitted runtime swap current.application envelope expiry
          (fun admitted => (fixed envelope found admitted).1)
          (fun admitted => (fixed envelope found admitted).2)
      simp only [phaseExecution_application]
      rw [handled]
      cases (phaseApplication runtime leaks).handle current.application envelope <;> rfl

end HiddenSwap
end Vegas.EventGraphRuntime

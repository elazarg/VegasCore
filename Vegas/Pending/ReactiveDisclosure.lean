/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.EventBindingInvariant

/-! # Compiled disclosures retain opening evidence

Packet selection reads the binding, not its publication verdict. The local
realization law applies to every publication result, including guard failure.
Its premises describe an inclusion opportunity; it does not assert that a
scheduler supplies that opportunity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Transmitting opening evidence does not itself execute the game action. -/
theorem submitStep_opening (state : State graph) (who : Player) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) :
    submitStep state who (.opening event candidate raw) = state := rfl

theorem reactiveResolutionPacket_opening {owner : Player}
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : ReactivePlayerView graph)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (value : L.Val payload) (stored : binding.get? view.observation.store = some (.success value))
    (candidate : Handle graph)
    (associated : view.publicView.accepted binding.field = some candidate)
    (owned : candidate.1 = who) :
    reactiveResolutionPacket who event payload binding outputEq action view =
      .opening event candidate ⟨payload, value⟩ := by
  simp only [reactiveResolutionPacket, discloses, ↓reduceIte, stored, associated, owned]

theorem reactiveResolutionPacket_withhold {owner : Player}
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : ReactivePlayerView graph)
    (withholds : cast (congrArg EventField.Action outputEq) action = false) :
    reactiveResolutionPacket who event payload binding outputEq action view = .withhold event := by
  simp only [reactiveResolutionPacket, withholds, Bool.false_eq_true, ↓reduceIte]

/-- Any successful binding in a valid runtime state supplies the opening
selected by its owner's compiler, independently of the deferred checks. -/
theorem reactiveResolutionPacket_provenance (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (valid : state.BindingInvariant)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (value : L.Val payload) (stored : binding.get? state.config.store = some (.success value)) :
    ∃ candidate, state.accepted binding.field = some candidate ∧ candidate.1 = owner ∧
      state.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      reactiveResolutionPacket owner event payload binding outputEq action
        ((runtime.reactiveApplication leaks).observePlayer state owner) =
          .opening event candidate ⟨payload, value⟩ := by
  obtain ⟨candidate, associated, owned, verified⟩ := valid.success_provenance binding value stored
  refine ⟨candidate, associated, owned, verified, ?_⟩
  apply reactiveResolutionPacket_opening owner event payload binding outputEq action _ discloses
    value _ candidate associated owned
  change binding.get? (graph.playerStore owner state.config.store) = _
  rw [binding.get?_playerStore owner state.config.store rfl, stored]

/-- The emitted packet executes disclosure with the actual guarded result.
In particular, a failed result does not substitute withholding for disclosure. -/
theorem reactiveDecision_opening_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (valid : state.BindingInvariant)
    (id : MessageId Player) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : state.config.cut.Ready event) (timely : state.WithinDeadline runtime event)
    (sender : id.1 = owner) (action : graph.Action event)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (value : L.Val payload) (stored : binding.get? state.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true state.config.store = some result) :
    ∃ candidate, (runtime.reactiveDecision leaks owner event action
        ((runtime.reactiveApplication leaks).observePlayer state owner)).transmission =
        some (.submit (disclosureSubmission (.opening event candidate ⟨payload, value⟩))) ∧
      handle runtime state ⟨id, .opening event candidate ⟨payload, value⟩⟩ =
        some (state.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) result)) := by
  obtain ⟨candidate, associated, owned, verified, packet⟩ :=
    reactiveResolutionPacket_provenance runtime leaks state valid owner event payload
      binding outputEq action discloses value stored
  refine ⟨candidate, ?_, ?_⟩
  · simp only [reactiveDecision, node, packet]
  · exact handle_opening_eq runtime state id event candidate owner payload binding checks
      outputEq codeEq node ready timely sender owned associated value verified stored
      result resolved

end Vegas.EventGraphRuntime

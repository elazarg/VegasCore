/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.EventBindingInvariant

/-! # Authentic compiled disclosures

An active owner can transmit the authentic value of its accepted binding.
The handler evaluates public guards, so authentic disclosure can still fail.
These facts require no prediction that the resulting publication succeeds.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveResolutionPacket_opening {owner : Player}
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph)
    (active : who ∉ view.publicView.observation.defaulted)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (value : L.Val payload)
    (stored : binding.get? view.observation.store = some (.success value))
    (candidate : Handle graph)
    (associated : view.publicView.accepted binding.field = some candidate)
    (owned : candidate.1 = who) :
    reactiveResolutionPacket who event payload binding checks outputEq action view =
      some (.opening event candidate ⟨payload, value⟩) := by
  simp only [reactiveResolutionPacket, ite_eq_right active, discloses, ↓reduceIte,
    stored, associated, owned]

/-- Every stored successful binding has authentic opening material in a valid state,
independently of the guarded publication's eventual result. -/
theorem reactiveResolutionPacket_provenance (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (valid : state.BindingInvariant)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event)
    (active : owner ∉ state.config.defaulted)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (value : L.Val payload)
    (stored : binding.get? state.config.store = some (.success value)) :
    ∃ candidate, state.accepted binding.field = some candidate ∧ candidate.1 = owner ∧
      state.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      reactiveResolutionPacket owner event payload binding checks outputEq action
        ((runtime.reactiveApplication leaks).observePlayer state owner) =
          some (.opening event candidate ⟨payload, value⟩) := by
  obtain ⟨candidate, associated, owned, verified⟩ := valid.success_provenance binding value stored
  refine ⟨candidate, associated, owned, verified, ?_⟩
  apply reactiveResolutionPacket_opening owner event payload binding checks outputEq action
    ((runtime.reactiveApplication leaks).observePlayer state owner)
    active discloses value _ candidate associated owned
  change binding.get? (graph.playerStore owner state.config.store) = _
  rw [binding.get?_playerStore owner state.config.store rfl, stored]

end Vegas.EventGraphRuntime

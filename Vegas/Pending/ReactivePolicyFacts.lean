/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePolicy

/-! # Prescribed submissions, recovery choices, and initialized law equality -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A resolution sends an opening of its event or nothing. -/
theorem reactiveResolutionPacket_shape {owner : Player} (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph) :
    (∃ candidate raw, reactiveResolutionPacket who event payload binding checks outputEq action
        view = some (.opening event candidate raw)) ∨
      reactiveResolutionPacket who event payload binding checks outputEq action view = none := by
  unfold reactiveResolutionPacket
  dsimp only
  repeat' split
  all_goals first
    | exact Or.inr rfl
    | exact Or.inl ⟨_, _, rfl⟩

theorem reactiveResolutionPacket_event {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph) (packet : Payload graph)
    (sent : reactiveResolutionPacket who event payload binding checks outputEq action view =
      some packet) :
    packet.event? graph = some event := by
  dsimp only [reactiveResolutionPacket] at sent
  repeat' split at sent
  all_goals first
    | cases sent; rfl
    | cases sent

/-- The prescribed translator makes no transmission for an already defaulted owner. -/
theorem reactiveDecision_defaulted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (action : graph.Action event) (view : PlayerView graph)
    (inactive : who ∈ view.publicView.observation.defaulted) :
    (runtime.reactiveDecision leaks who event action view).transmission = none := by
  simp only [reactiveDecision, ite_eq_left inactive]

/-- A selected binding omission stays silent, independently of available candidate slots. -/
theorem reactiveDecision_binding_none (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (view : PlayerView graph) :
    (runtime.reactiveDecision leaks who event
      (cast (congrArg EventField.Action outputEq.symm)
        (none : Option (PublicationResult (L.Val payload)))) view).transmission = none := by
  simp only [reactiveDecision, node, cast_cast, cast_eq, Option.bind_none, ite_self]

/-- Admitted binding failure sends an opaque handle just as an admitted value does. -/
theorem reactiveDecision_binding_some (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (view : PlayerView graph) (active : who ∉ view.publicView.observation.defaulted)
    (serial : Nat) (selected : reactiveFreshSlot view = some serial)
    (result : PublicationResult (L.Val payload)) :
    runtime.reactiveDecision leaks who event
        (cast (congrArg EventField.Action outputEq.symm) (some result)) view =
      runtime.reactiveBinding leaks who event payload result serial := by
  simp only [reactiveDecision, ite_eq_right active, node, cast_cast, cast_eq,
    Option.bind_some, selected, Option.map_some]
  rfl

/-- Authentic opening material is transmitted without a successful-guard premise. -/
theorem reactiveResolutionPacket_openable {owner : Player} (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload) (view : PlayerView graph)
    (active : who ∉ view.publicView.observation.defaulted) (value : L.Val payload)
    (stored : binding.get? view.observation.store = some (.success value))
    (candidate : Handle graph) (accepted : view.publicView.accepted binding.field = some candidate)
    (owned : candidate.1 = who) :
    reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventField.Action outputEq.symm) true) view =
      some (.opening event candidate ⟨payload, value⟩) := by
  simp only [reactiveResolutionPacket, cast_cast, cast_eq, ite_eq_right active,
    ↓reduceIte, stored, accepted, owned]

/-- A transmitted opening contains an active owner's authentic binding value.
Public guards are evaluated by the receiving handler. -/
theorem reactiveResolutionPacket_opening_spec {owner : Player} (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph)
    (named : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (opened : reactiveResolutionPacket who event payload binding checks outputEq action view =
      some (.opening named candidate raw)) :
    who ∉ view.publicView.observation.defaulted ∧
      (cast (congrArg EventField.Action outputEq) action : Bool) = true ∧
      named = event ∧
      ∃ value, binding.get? view.observation.store = some (.success value) ∧
        view.publicView.accepted binding.field = some candidate ∧ candidate.1 = who ∧
        raw = ⟨payload, value⟩ := by
  unfold reactiveResolutionPacket at opened
  dsimp only at opened
  split at opened
  · cases opened
  · rename_i active
    split at opened
    · rename_i disclose
      split at opened
      · rename_i value stored
        split at opened
        · rename_i handle associated
          split at opened
          · rename_i owned
            cases opened
            exact ⟨active, disclose, rfl, value, stored, associated, owned, rfl⟩
          · cases opened
        · cases opened
      · cases opened
      · cases opened
    · cases opened

end Vegas.EventGraphRuntime

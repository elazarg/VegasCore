/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.EventBindingInvariant

/-! # Locally validated compiled disclosures

The prescribed source compiler opens only successful publications. Its owner can
compute the exact guarded result from the locally visible store. Raw players
retain the ability to publish rejected openings; the handler and evidence rules
are unchanged. These local laws assume an inclusion opportunity.
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
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks true view.observation.store =
      some (.success value))
    (candidate : Handle graph)
    (associated : view.publicView.accepted binding.field = some candidate)
    (owned : candidate.1 = who) :
    reactiveResolutionPacket who event payload binding checks outputEq action view =
      some (.opening event candidate ⟨payload, value⟩) := by
  simp only [reactiveResolutionPacket, discloses, ↓reduceIte, resolved, associated, owned]

/-- A successfully validated publication has authentic opening material in a
valid runtime state, and owner-local validation selects that opening. -/
theorem reactiveResolutionPacket_provenance (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (valid : state.BindingInvariant)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks true state.config.store =
      some (.success value)) :
    ∃ candidate, state.accepted binding.field = some candidate ∧ candidate.1 = owner ∧
      state.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      reactiveResolutionPacket owner event payload binding checks outputEq action
        ((runtime.reactiveApplication leaks).observePlayer state owner) =
          some (.opening event candidate ⟨payload, value⟩) := by
  have stored : binding.get? state.config.store = some (.success value) := by
    unfold EventCode.resolveOutput? at resolved
    cases bound : binding.get? state.config.store with
    | none => simp [bound] at resolved
    | some result =>
        cases accepted : GuardCheck.allAccepted? checks state.config.store result with
        | none => simp [bound, accepted] at resolved
        | some allowed =>
            cases allowed <;> simp_all
  obtain ⟨candidate, associated, owned, verified⟩ := valid.success_provenance binding value stored
  refine ⟨candidate, associated, owned, verified, ?_⟩
  apply reactiveResolutionPacket_opening owner event payload binding checks outputEq action _
    discloses value _ candidate associated owned
  change EventCode.resolveOutput? binding checks true
    (graph.playerStore owner state.config.store) = _
  rw [EventCode.resolveOutput?_playerStore, resolved]

end Vegas.EventGraphRuntime

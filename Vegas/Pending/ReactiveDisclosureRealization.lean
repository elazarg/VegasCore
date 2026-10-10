/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.EventPublicState
import Vegas.EventGraph.Commutation

/-! # Semantic realization of silent sampled disclosures

In a valid ready state, a prescribed silent resolution has exactly the failure
output of its original sampled graph action. Expiry uses FALSE physically;
original private disclosure recall must still be reconstructed separately.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Silence at a valid ready resolution means semantic failure, including a
TRUE intention rejected by the owner-local guard. Success always has an
accepted binding handle and an authentic prescribed opening. -/
theorem reactiveDecision_silent_resolution_failure (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (valid : state.BindingInvariant)
    (owner : Player) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (disclose : Bool)
    (silent : (runtime.reactiveDecision leaks owner event
      (cast (congrArg EventField.Action outputEq.symm) disclose)
      ((runtime.reactiveApplication leaks).observePlayer state owner)).transmission = none) :
    EventCode.resolveOutput? binding checks disclose state.config.store = some .failure := by
  have readsEq : (graph.nodes event).readFields =
      insert binding.field (GuardCheck.listReadFields checks) := by
    rw [← EventCode.readFields_cast outputEq, codeEq]
    rfl
  have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (state.config.store field).isSome = true := by
    intro field read
    exact state.config.read_available ready (readsEq.symm ▸ read)
  cases disclose with
  | false => exact EventCode.resolveOutput?_false_eq_failure binding checks _ available
  | true =>
      have present := EventCode.resolveOutput?_isSome binding checks true _ available
      cases resolved : EventCode.resolveOutput? binding checks true state.config.store with
      | none => simp [resolved] at present
      | some result =>
          cases result with
          | failure => rfl
          | success value =>
              obtain ⟨candidate, _, _, _, packet⟩ :=
                reactiveResolutionPacket_provenance runtime leaks state valid owner event payload
                  binding checks outputEq
                  (cast (congrArg EventField.Action outputEq.symm) true)
                  (by simp only [cast_cast, cast_eq]) value resolved
              simp only [reactiveDecision, node] at silent
              rw [reactiveResolutionSubmission_normal runtime leaks state valid, packet] at silent
              cases silent

/-- The original sampled action's graph transition has a deterministic failure
output, while retaining the original Boolean in its completion history. -/
theorem reactiveDecision_silent_resolution_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (valid : state.BindingInvariant)
    (owner : Player) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (disclose : Bool)
    (silent : (runtime.reactiveDecision leaks owner event
      (cast (congrArg EventField.Action outputEq.symm) disclose)
      ((runtime.reactiveApplication leaks).observePlayer state owner)).transmission = none) :
    state.config.step event ready (cast (congrArg EventField.Action outputEq.symm) disclose) =
      PMF.pure (state.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))) := by
  have failed := runtime.reactiveDecision_silent_resolution_failure leaks state valid owner event
    ready payload binding checks outputEq codeEq node disclose silent
  rw [state.config.step_eq_map_of_code event ready outputEq
    (.resolve owner payload binding checks) codeEq disclose (PMF.pure .failure)
      (by simp only [EventCode.resolve_eval?, failed, Option.map_some])]
  exact PMF.pure_map _ _

/-- Actual due expiry realizes the typed store law of a silent sampled
resolution. This comparison retains the original action on the graph side;
the runtime's FALSE recall is not declared equal to that intention. -/
theorem reactiveDecision_silent_resolution_expiry_store (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (valid : state.BindingInvariant)
    (owner : Player) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (disclose : Bool)
    (silent : (runtime.reactiveDecision leaks owner event
      (cast (congrArg EventField.Action outputEq.symm) disclose)
      ((runtime.reactiveApplication leaks).observePlayer state owner)).transmission = none) :
    (environmentStep runtime state (.expire event)).map (fun next => next.config.store) =
      (state.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)).map Config.store := by
  rw [environmentStep_expire_resolve_eq runtime state event ready entered activated due owner
      payload binding checks outputEq codeEq node,
    runtime.reactiveDecision_silent_resolution_step leaks state valid owner event ready payload
      binding checks outputEq codeEq node disclose silent]
  simp only [PMF.pure_map]
  apply congrArg PMF.pure
  change (state.config.complete event ready _ _).store = _
  rw [store_complete, store_complete]

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosureStability

/-! # Public realization of every compiled disclosure

When the binding itself failed, both source disclosure choices emit withholding.
Their source completion histories differ, but their stored results and public
observations coincide. The compiler may retain the sampled choice in its private
implementation state; this theorem does not recover that choice from the packet.
When a binding succeeded, disclosure emits its opening even if a guard rejects it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveResolutionPacket_failed_binding {owner : Player}
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : ReactivePlayerView graph)
    (failed : binding.get? view.observation.store = some .failure) :
    reactiveResolutionPacket who event payload binding outputEq action view = .withhold event := by
  simp only [reactiveResolutionPacket, failed, ite_self]

/-- The emitted response cannot identify which aliased source choice was sampled. -/
theorem reactiveDecision_failed_binding_action_irrel (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (first second : graph.Action event) (view : ReactivePlayerView graph)
    (failed : binding.get? view.observation.store = some .failure) :
    runtime.reactiveDecision leaks who event first view =
      runtime.reactiveDecision leaks who event second view := by
  simp only [reactiveDecision, node,
    reactiveResolutionPacket_failed_binding who event payload binding outputEq first view failed,
    reactiveResolutionPacket_failed_binding who event payload binding outputEq second view failed]

omit [DecidableEq Player] in
private theorem completion_public_action_irrel (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (first second : graph.Action event) (value : (graph.outputLayout event).Value) :
    (state.complete event ready first value).publicView =
      (state.complete event ready second value).publicView := by
  unfold State.publicView
  congr 1
  apply PublicObservation.ext graph
  · simp [State.complete, Vegas.EventGraph.publicObserve]
  · rfl

/-- At a ready, timely inclusion the actual response produces the source store
and public observation. Equality of the private source action history is neither
needed here nor asserted. The application-side opening cache is empty. -/
theorem reactiveDecision_disclosure_public_law (runtime : EventGraphRuntime graph)
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
    (sender : id.1 = owner) (unremembered : state.remembered event = none)
    (action : graph.Action event) :
    ∃ (result : PublicationResult (L.Val payload)) (packet : Payload graph) (next : State graph),
      EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) action) state.config.store = some result ∧
      (runtime.reactiveDecision leaks owner event action
        ((runtime.reactiveApplication leaks).observePlayer state owner)).transmission =
          some (.submit (disclosureSubmission packet)) ∧
      handle runtime state ⟨id, packet⟩ = some next ∧
      next.config.store = (state.complete event ready action
        (cast (congrArg EventField.Value outputEq.symm) result)).config.store ∧
      next.publicView = (state.complete event ready action
        (cast (congrArg EventField.Value outputEq.symm) result)).publicView := by
  have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (state.config.store field).isSome = true := by
    intro field member
    apply state.config.read_available ready
    rw [resolution_readFields event owner payload binding checks outputEq codeEq]
    exact member
  have falseResult := EventCode.resolveOutput?_false_eq_failure binding checks
    state.config.store available
  have withheld := runtime.handle_withhold_unremembered_eq state id event owner payload
    binding checks outputEq codeEq node ready timely sender unremembered
  cases discloses : cast (congrArg EventField.Action outputEq) action with
  | false =>
      have packet := reactiveResolutionPacket_withhold owner event payload binding outputEq
        action ((runtime.reactiveApplication leaks).observePlayer state owner) discloses
      refine ⟨.failure, .withhold event, _, falseResult, ?_, withheld, rfl, ?_⟩
      · simp only [reactiveDecision, node, packet]
      · exact completion_public_action_irrel state event ready _ action _
  | true =>
      have present : (binding.get? state.config.store).isSome = true :=
        binding.get?_isSome state.config.store
          (available binding.field (Finset.mem_insert_self ..))
      cases stored : binding.get? state.config.store with
      | none => simp only [stored, Option.isSome_none, Bool.false_eq_true] at present
      | some bound =>
          cases bound with
          | failure =>
              have resolved : EventCode.resolveOutput? binding checks true state.config.store =
                  some (.failure : PublicationResult (L.Val payload)) := by
                simpa [EventCode.resolveOutput?, stored] using falseResult
              have localFailed : binding.get?
                  ((runtime.reactiveApplication leaks).observePlayer state
                    owner).observation.store =
                    some .failure := by
                change binding.get? (graph.playerStore owner state.config.store) = _
                rw [binding.get?_playerStore owner state.config.store rfl, stored]
              have packet := reactiveResolutionPacket_failed_binding owner event payload binding
                outputEq action _ localFailed
              refine ⟨.failure, .withhold event, _, resolved, ?_, withheld, rfl, ?_⟩
              · simp only [reactiveDecision, node, packet]
              · exact completion_public_action_irrel state event ready _ action _
          | success value =>
              have defined := EventCode.resolveOutput?_isSome binding checks true
                state.config.store available
              cases resolved : EventCode.resolveOutput? binding checks true state.config.store with
              | none => simp only [resolved, Option.isSome_none, Bool.false_eq_true] at defined
              | some result =>
                  obtain ⟨candidate, transmission, handled⟩ :=
                    runtime.reactiveDecision_opening_law leaks state valid id owner event payload
                      binding checks outputEq codeEq node ready timely sender action discloses
                      value stored result resolved
                  refine ⟨result, .opening event candidate ⟨payload, value⟩, _, rfl,
                    transmission, handled, rfl, ?_⟩
                  exact completion_public_action_irrel state event ready _ action _

end Vegas.EventGraphRuntime

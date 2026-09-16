/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingInvariant

/-! # Effective actions of native event completions

An accepted packet may have passed through arbitrary private preparation and
transport state.  The semantic action it realizes is nevertheless recorded by
the event graph itself.  This module reads that action at the unique history
position appended by the native completion.  In particular, resolution
actions are read from the history rather than reconstructed from their public
result: a rejected disclosure may store failure while retaining the original
`true` action.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The completion immediately following the semantic history of `before`, if
`after` has one at that position.  Transport state and private caches do not
enter this readout. -/
def effectiveCompletion? (before after : State graph) : Option graph.Completion :=
  after.config.history[before.config.history.length]?

omit [DecidableEq Player] in
/-- A supported graph step records exactly its supplied dependent action at the
first new history position. -/
theorem effectiveCompletion?_eq_of_mem_step
    (before after : State graph) (event : graph.EventId)
    (ready : before.config.cut.Ready event) (action : graph.Action event)
    (member : after.config ∈ (before.config.step event ready action).support) :
    effectiveCompletion? before after = some ⟨event, action⟩ := by
  rw [effectiveCompletion?,
    before.config.step_history event ready action after.config member]
  simp

/-- Every accepted packet has a stable addressed event and one effective graph
action, and the history readout returns that very dependent action. -/
theorem handle_effectiveCompletion
    (runtime : EventGraphRuntime graph) (before after : State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime before message = some after) :
    ∃ event, Payload.event? graph message.payload = some event ∧
      ∃ (ready : before.config.cut.Ready event) (action : graph.Action event),
        after.config ∈ (before.config.step event ready action).support ∧
          effectiveCompletion? before after = some ⟨event, action⟩ := by
  obtain ⟨event, addressed, ready, action, member⟩ :=
    handle_config_mem_step runtime before after message accepted
  exact ⟨event, addressed, ready, action, member,
    effectiveCompletion?_eq_of_mem_step before after event ready action member⟩

omit [DecidableEq Player] in
/-- The effective action at a fixed event is unique.  This remains true when
two actions produce the same public value, because the graph history retains
the original action. -/
theorem effective_action_unique
    (before after : State graph) (event : graph.EventId)
    (leftReady rightReady : before.config.cut.Ready event)
    (left right : graph.Action event)
    (leftMember : after.config ∈
      (before.config.step event leftReady left).support)
    (rightMember : after.config ∈
      (before.config.step event rightReady right).support) :
    left = right := by
  have same : (some ⟨event, left⟩ : Option graph.Completion) =
      some ⟨event, right⟩ := by
    rw [← effectiveCompletion?_eq_of_mem_step before after event leftReady left leftMember,
      effectiveCompletion?_eq_of_mem_step before after event rightReady right rightMember]
  have completionEq : (⟨event, left⟩ : graph.Completion) = ⟨event, right⟩ :=
    Option.some.inj same
  cases completionEq
  rfl

/-- A successful binding inclusion reads out the immutable typed meaning of
the accepted candidate, including canonical binding failure. -/
theorem handle_commitment_effectiveCompletion
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (view : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : state.config.cut.Ready event)
    (timely : state.WithinDeadline runtime event)
    (sender : id.1 = owner) (handleOwner : candidate.1 = owner)
    (vacant : state.accepted (.inr event) = none)
    (unused : state.HandleUnused candidate) :
    let next := { (state.complete event ready
      (cast (congrArg EventField.Action outputEq.symm)
        (state.bindingResult candidate payload))
      (cast (congrArg EventField.Value outputEq.symm)
        (state.bindingResult candidate payload))) with
      accepted := Function.update state.accepted (.inr event) (some candidate)
      candidates := state.candidates.accept candidate }
    handle runtime state ⟨id, .commitment event candidate⟩ = some next ∧
      effectiveCompletion? state next = some ⟨event,
        cast (congrArg EventField.Action outputEq.symm)
          (state.bindingResult candidate payload)⟩ := by
  dsimp only
  constructor
  · exact handle_commitment_eq runtime state id event candidate owner payload outputEq codeEq
      view ready timely sender handleOwner vacant unused
  · simp [effectiveCompletion?, State.complete, EventGraph.Config.complete_history]

/-- A verified opening records disclosure `true`; validation may still make
its public publication result a failure. -/
theorem handle_opening_effectiveCompletion
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (view : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : state.config.cut.Ready event)
    (timely : state.WithinDeadline runtime event)
    (sender : id.1 = owner) (handleOwner : candidate.1 = owner)
    (associated : state.accepted binding.field = some candidate)
    (value : L.Val payload)
    (verified : state.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (stored : binding.get? state.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true state.config.store = some result) :
    let next := state.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) true)
      (cast (congrArg EventField.Value outputEq.symm) result)
    handle runtime state ⟨id, .opening event candidate ⟨payload, value⟩⟩ = some next ∧
      effectiveCompletion? state next = some ⟨event,
        cast (congrArg EventField.Action outputEq.symm) true⟩ := by
  dsimp only
  constructor
  · exact handle_opening_eq runtime state id event candidate owner payload binding checks
      outputEq codeEq view ready timely sender handleOwner associated value verified stored
      result resolved
  · simp [effectiveCompletion?, State.complete, EventGraph.Config.complete_history]

/-- Canonical withholding reads out the owner's retained disclosure decision.
This is deliberately not inferred from the failure-valued public result. -/
theorem handle_withhold_effectiveCompletion
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (view : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : state.config.cut.Ready event)
    (timely : state.WithinDeadline runtime event)
    (sender : id.1 = owner) (disclose : Bool)
    (remembered : state.remembered event = some
      (cast (congrArg EventField.Action outputEq.symm) disclose))
    (resolved : EventCode.resolveOutput? binding checks disclose state.config.store =
      some .failure) :
    let next := state.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))
    handle runtime state ⟨id, .withhold event⟩ = some next ∧
      effectiveCompletion? state next = some ⟨event,
        cast (congrArg EventField.Action outputEq.symm) disclose⟩ := by
  dsimp only
  constructor
  · exact handle_withhold_eq runtime state id event owner payload binding checks outputEq
      codeEq view ready timely sender disclose remembered resolved
  · simp [effectiveCompletion?, State.complete, EventGraph.Config.complete_history]

end Vegas.EventGraphRuntime

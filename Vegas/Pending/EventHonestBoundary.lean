/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingService
import Vegas.Pending.EventPolicyBlock

/-! # Clean boundaries for the honest event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The finite state carried between honest event blocks. Conditions that are
consumed by an event are required only while that event remains unfinished. -/
structure HonestBoundary (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (execution : runtime.application.PolicyExecution) : Prop where
  invariant : execution.native.application.Invariant inputs
  bindingInvariant : execution.native.application.BindingInvariant
  pending_empty : execution.native.pool.pending = []
  remembered_unfinished : ∀ event, event ∉ execution.native.application.config.cut.completed →
    execution.native.application.remembered event = none
  history_unfinished : ∀ who event,
    event ∉ execution.native.application.config.cut.completed →
      stagingCount (execution.principalHistory who) event = 0 ∧
        submittedAt (execution.principalHistory who) event = false
  accepted_unfinished : ∀ event,
    event ∉ execution.native.application.config.cut.completed →
      execution.native.application.accepted (.inr event) = none
  canonical_fresh_unfinished : ∀ event owner,
    event ∉ execution.native.application.config.cut.completed →
      graph.actor? event = some owner →
      execution.native.application.candidates.lookup (owner, eventSlot event) = .fresh
  canonical_unused_unfinished : ∀ event owner,
    event ∉ execution.native.application.config.cut.completed →
      graph.actor? event = some owner →
      execution.native.application.HandleUnused (owner, eventSlot event)

/-- The native initial execution is a clean honest boundary. -/
theorem initial_honestBoundary (runtime : EventGraphRuntime graph) (inputs : graph.Inputs) :
    HonestBoundary runtime inputs
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs))) := by
  refine ⟨State.initial_invariant inputs, State.initial_bindingInvariant inputs, rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro event unfinished
    rfl
  · intro who event unfinished
    exact ⟨rfl, rfl⟩
  · intro event unfinished
    rfl
  · intro event owner unfinished actor
    rfl
  · intro event owner unfinished actor field accepted
    obtain ⟨input, inputOwner, payload, fieldEq, kindEq, handleEq⟩ :=
      State.initial_accepted_eq_some inputs field (owner, eventSlot event) accepted
    have slotEq : Slot.initial input = Slot.prepared event := by
      simpa [eventSlot] using congrArg Prod.snd handleEq
    cases slotEq

theorem HonestBoundary.lookup_eq_none {runtime : EventGraphRuntime graph}
    {inputs : graph.Inputs} {execution : runtime.application.PolicyExecution}
    (boundary : HonestBoundary runtime inputs execution)
    (id : MessageId Player) : execution.native.pool.lookup id = none := by
  unfold MessagePool.lookup
  rw [boundary.pending_empty]
  rfl

/-- Restore a clean boundary after completing one event.  The transition
supplies only pointwise frames for other events, allowing policy histories for
the completed event itself to remain recorded. -/
theorem HonestBoundary.after_completed_event
    {runtime : EventGraphRuntime graph} {inputs : graph.Inputs}
    {before after : runtime.application.PolicyExecution}
    (boundary : HonestBoundary runtime inputs before) (event : graph.EventId)
    (invariant : after.native.application.Invariant inputs)
    (bindingInvariant : after.native.application.BindingInvariant)
    (pendingEmpty : after.native.pool.pending = [])
    (completed : event ∈ after.native.application.config.cut.completed)
    (completedSubset : before.native.application.config.cut.completed ⊆
      after.native.application.config.cut.completed)
    (rememberedFrame : ∀ query, query ≠ event →
      after.native.application.remembered query =
        before.native.application.remembered query)
    (historyFrame : ∀ who query, query ≠ event →
      stagingCount (after.principalHistory who) query =
          stagingCount (before.principalHistory who) query ∧
        submittedAt (after.principalHistory who) query =
          submittedAt (before.principalHistory who) query)
    (acceptedFrame : ∀ query, query ≠ event →
      after.native.application.accepted (.inr query) =
        before.native.application.accepted (.inr query))
    (candidateFrame : ∀ query owner, query ≠ event →
      after.native.application.candidates.lookup (owner, eventSlot query) =
        before.native.application.candidates.lookup (owner, eventSlot query))
    (unusedFrame : ∀ query owner, query ≠ event →
      before.native.application.HandleUnused (owner, eventSlot query) →
        after.native.application.HandleUnused (owner, eventSlot query)) :
    HonestBoundary runtime inputs after := by
  refine ⟨invariant, bindingInvariant, pendingEmpty, ?_, ?_, ?_, ?_, ?_⟩
  · intro query unfinished
    have different : query ≠ event := by
      intro same
      subst query
      exact unfinished completed
    rw [rememberedFrame query different]
    apply boundary.remembered_unfinished query
    intro prior
    exact unfinished (completedSubset prior)
  · intro who query unfinished
    have different : query ≠ event := by
      intro same
      subst query
      exact unfinished completed
    rw [(historyFrame who query different).1, (historyFrame who query different).2]
    apply boundary.history_unfinished who query
    intro prior
    exact unfinished (completedSubset prior)
  · intro query unfinished
    have different : query ≠ event := by
      intro same
      subst query
      exact unfinished completed
    rw [acceptedFrame query different]
    apply boundary.accepted_unfinished query
    intro prior
    exact unfinished (completedSubset prior)
  · intro query owner unfinished actor
    have different : query ≠ event := by
      intro same
      subst query
      exact unfinished completed
    rw [candidateFrame query owner different]
    apply boundary.canonical_fresh_unfinished query owner
    · intro prior
      exact unfinished (completedSubset prior)
    · exact actor
  · intro query owner unfinished actor
    have different : query ≠ event := by
      intro same
      subst query
      exact unfinished completed
    apply unusedFrame query owner different
    apply boundary.canonical_unused_unfinished query owner
    · intro prior
      exact unfinished (completedSubset prior)
    · exact actor

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant

/-! # Binding-handle provenance for the event pending runtime

This invariant connects successful typed binding values in the ideal event
store to immutable candidate meanings.  Binding failure deliberately creates
no provenance obligation: deadline expiry may complete a binding with failure
without accepting any handle.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace State

/-- Accepted handles are well typed and unique, and every successful binding
value is backed by the immutable opening of its accepted handle. -/
structure BindingInvariant (state : State graph) : Prop where
  accepted_typed : ∀ field handle, state.accepted field = some handle →
    ∃ payload, graph.layout field = .binding handle.1 payload
  accepted_injective : ∀ left right handle,
    state.accepted left = some handle → state.accepted right = some handle →
      left = right
  success_provenance : ∀ {owner payload}
      (ref : FieldRef graph.layout (.binding owner payload)) (value : L.Val payload),
    ref.get? state.config.store = some (.success value) →
      ∃ handle, state.accepted ref.field = some handle ∧ handle.1 = owner ∧
        state.candidates.lookup handle = .openable ⟨payload, value⟩

omit [DecidableEq Player] in
/-- Runtime fields unrelated to the graph store and commitment tables do not
affect binding provenance. -/
theorem BindingInvariant.copy {before after : State graph}
    (invariant : before.BindingInvariant)
    (configEq : after.config = before.config)
    (acceptedEq : after.accepted = before.accepted)
    (candidatesEq : after.candidates = before.candidates) :
    after.BindingInvariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro field handle accepted
    rw [acceptedEq] at accepted
    exact invariant.accepted_typed field handle accepted
  · intro left right handle leftAccepted rightAccepted
    rw [acceptedEq] at leftAccepted rightAccepted
    exact invariant.accepted_injective left right handle leftAccepted rightAccepted
  · intro owner payload ref value stored
    rw [configEq] at stored
    obtain ⟨handle, accepted, ownerEq, candidate⟩ :=
      invariant.success_provenance ref value stored
    refine ⟨handle, ?_, ownerEq, ?_⟩
    · simpa only [acceptedEq] using accepted
    · simpa only [candidatesEq] using candidate

omit [DecidableEq Player] in
/-- Preserve provenance when the commitment tables are unchanged and every
successful binding in the new store was already the same success before. -/
theorem BindingInvariant.of_successes_before {before after : State graph}
    (invariant : before.BindingInvariant)
    (acceptedEq : after.accepted = before.accepted)
    (candidatesEq : after.candidates = before.candidates)
    (successBefore : ∀ {owner payload}
      (ref : FieldRef graph.layout (.binding owner payload)) (value : L.Val payload),
      ref.get? after.config.store = some (.success value) →
        ref.get? before.config.store = some (.success value)) :
    after.BindingInvariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro field handle accepted
    rw [acceptedEq] at accepted
    exact invariant.accepted_typed field handle accepted
  · intro left right handle leftAccepted rightAccepted
    rw [acceptedEq] at leftAccepted rightAccepted
    exact invariant.accepted_injective left right handle leftAccepted rightAccepted
  · intro owner payload ref value stored
    obtain ⟨handle, accepted, ownerEq, candidate⟩ :=
      invariant.success_provenance ref value (successBefore ref value stored)
    refine ⟨handle, ?_, ownerEq, ?_⟩
    · simpa only [acceptedEq] using accepted
    · simpa only [candidatesEq] using candidate

omit [DecidableEq Player] in
/-- Completing one field preserves all earlier binding successes when the new
output itself cannot be a binding success. -/
theorem complete_success_before (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (output : (graph.outputLayout event).Value)
    (noSuccess : ∀ (owner : Player) (payload : L.Ty)
      (outputEq : graph.outputLayout event = .binding owner payload)
      (value : L.Val payload),
      cast (congrArg EventField.Value outputEq) output ≠ .success value)
    {owner payload} (ref : FieldRef graph.layout (.binding owner payload))
    (value : L.Val payload)
    (stored : ref.get? (state.complete event ready action output).config.store =
      some (.success value)) :
    ref.get? state.config.store = some (.success value) := by
  by_cases same : ref.field = .inr event
  · rcases ref with ⟨field, layoutEq⟩
    change field = .inr event at same
    subst field
    change graph.outputLayout event = .binding owner payload at layoutEq
    have outputEq : graph.outputLayout event = .binding owner payload := layoutEq
    have outputStored :
        (state.complete event ready action output).config.store (.inr event) =
          some output := by
      exact EventGraph.Config.complete_output_same state.config event ready action output
    have typedStored : cast
        (congrArg (fun kind : EventField Player L => kind.Value) outputEq) output =
        (PublicationResult.success value : PublicationResult (L.Val payload)) := by
      unfold FieldRef.get? at stored
      rw [outputStored] at stored
      have valueEq : (graph.outputLayout event).Value =
          (EventField.binding owner payload).Value :=
        congrArg (fun kind : EventField Player L => kind.Value) outputEq
      change cast (congrArg Option valueEq) (some output) =
        some (.success value) at stored
      have castSome {alpha beta : Type} (typeEq : alpha = beta) (item : alpha) :
          cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
        subst beta
        rfl
      rw [castSome valueEq output] at stored
      have typedOutput : cast valueEq output = .success value := Option.some.inj stored
      exact typedOutput
    exact (noSuccess owner payload outputEq value typedStored).elim
  · have fieldEq :
        (state.complete event ready action output).config.store ref.field =
          state.config.store ref.field := by
      cases field : ref.field with
      | inl input => rfl
      | inr query =>
          have different : query ≠ event := by
            intro queryEq
            apply same
            rw [field, queryEq]
          change (state.complete event ready action output).config.outputs query =
            state.config.outputs query
          exact EventGraph.Config.complete_output_of_ne state.config event query ready
            action output different
    exact (ref.get?_congr _ _ fieldEq).symm.trans stored

omit [DecidableEq Player] in
/-- State completion preserves binding provenance whenever its new output is
not a successful binding. -/
theorem BindingInvariant.complete_of_no_success {state : State graph}
    (invariant : state.BindingInvariant) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (output : (graph.outputLayout event).Value)
    (noSuccess : ∀ (owner : Player) (payload : L.Ty)
      (outputEq : graph.outputLayout event = .binding owner payload)
      (value : L.Val payload),
      cast (congrArg EventField.Value outputEq) output ≠ .success value) :
    (state.complete event ready action output).BindingInvariant := by
  apply BindingInvariant.of_successes_before
    (before := state) (after := state.complete event ready action output)
    invariant rfl rfl
  intro owner payload ref value stored
  exact complete_success_before state event ready action output noSuccess ref value stored

omit [DecidableEq Player] in
/-- Completing a non-binding output cannot introduce a successful binding. -/
theorem BindingInvariant.complete_nonbinding {state : State graph}
    (invariant : state.BindingInvariant) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (output : (graph.outputLayout event).Value)
    (notBinding : ∀ (owner : Player) (payload : L.Ty),
      graph.outputLayout event ≠ .binding owner payload) :
    (state.complete event ready action output).BindingInvariant := by
  apply invariant.complete_of_no_success event ready action output
  intro owner payload outputEq
  exact (notBinding owner payload outputEq).elim

/-- Initial opaque handles provide exact immutable provenance for every
successful binding input. Event outputs are unavailable initially. -/
theorem initial_bindingInvariant (inputs : graph.Inputs) :
    (State.initial inputs).BindingInvariant := by
  refine ⟨?_, State.initial_accepted_injective inputs, ?_⟩
  · intro field handle accepted
    obtain ⟨input, owner, payload, rfl, kindEq, handleEq⟩ :=
      State.initial_accepted_eq_some inputs field handle accepted
    subst handle
    refine ⟨payload, ?_⟩
    change graph.inputLayout input = .binding owner payload
    exact kindEq
  · intro owner payload ref value stored
    rcases ref with ⟨field, layoutEq⟩
    cases field with
    | inr event =>
        change graph.outputLayout event = .binding owner payload at layoutEq
        have valueEq : (graph.outputLayout event).Value =
            (EventField.binding owner payload).Value :=
          congrArg (fun kind : EventField Player L => kind.Value) layoutEq
        unfold FieldRef.get? EventGraph.Config.store State.initial
          EventGraph.Config.initial at stored
        change cast (congrArg Option valueEq) none = some (.success value) at stored
        have castNone {alpha beta : Type} (typeEq : alpha = beta) :
            cast (congrArg Option typeEq) (none : Option alpha) =
              (none : Option beta) := by
          subst beta
          rfl
        rw [castNone valueEq] at stored
        contradiction
    | inl input =>
        change graph.inputLayout input = .binding owner payload at layoutEq
        have valueEq : (graph.inputLayout input).Value =
            (EventField.binding owner payload).Value :=
          congrArg (fun kind : EventField Player L => kind.Value) layoutEq
        have typedInput : cast valueEq (inputs input) = .success value := by
          unfold FieldRef.get? EventGraph.Config.store State.initial at stored
          change cast (congrArg Option valueEq) (some (inputs input)) =
            some (.success value) at stored
          have castSome {alpha beta : Type} (typeEq : alpha = beta) (item : alpha) :
              cast (congrArg Option typeEq) (some item) =
                some (cast typeEq item) := by
            subst beta
            rfl
          rw [castSome valueEq (inputs input)] at stored
          exact Option.some.inj stored
        refine ⟨(owner, .initial input), ?_, rfl, ?_⟩
        · exact State.initial_accepted_binding inputs input owner payload layoutEq
        · exact State.initial_candidate_binding_success inputs input owner payload
            layoutEq value typedInput

end State

/-- Private remembering preserves binding provenance. Preparation also
preserves it because every handle already backing a success is permanently
openable and candidate meanings are write-once. -/
theorem privateStep_bindingInvariant (state : State graph)
    (invariant : state.BindingInvariant) (who : Player)
    (command : PrivateCommand graph) :
    (privateStep state who command).BindingInvariant := by
  cases command with
  | prepare serial raw =>
      refine ⟨invariant.accepted_typed, invariant.accepted_injective, ?_⟩
      intro owner payload ref value stored
      obtain ⟨handle, accepted, ownerEq, candidate⟩ :=
        invariant.success_provenance ref value stored
      refine ⟨handle, accepted, ownerEq, ?_⟩
      change (state.candidates.prepare who (.prepared serial) raw).lookup handle =
        .openable ⟨payload, value⟩
      rw [state.candidates.lookup_prepare_eq_of_not_fresh handle who (.prepared serial) raw]
      · exact candidate
      · rw [candidate]
        simp
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · cases remembered : state.remembered event
        <;> apply invariant.copy <;> simp [privateStep, owned, remembered]
      · apply invariant.copy <;> simp [privateStep, owned]

end Vegas.EventGraphRuntime

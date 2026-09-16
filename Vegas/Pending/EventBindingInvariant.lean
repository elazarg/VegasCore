/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant
import Interaction.MessageApplicationPolicyLaws

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

omit [DecidableEq Player] in
private theorem bindingInvariant_of_nonbinding_step
    {state next : State graph} (invariant : state.BindingInvariant)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (action : graph.Action event)
    (member : next.config ∈ (state.config.step event ready action).support)
    (acceptedEq : next.accepted = state.accepted)
    (candidatesEq : next.candidates = state.candidates)
    (notBinding : ∀ owner payload,
      graph.outputLayout event ≠ .binding owner payload) :
    next.BindingInvariant := by
  apply State.BindingInvariant.of_successes_before invariant acceptedEq candidatesEq
  intro owner payload ref value stored
  unfold EventGraph.Config.step at member
  rw [FinDist.support_map, Set.mem_image] at member
  obtain ⟨output, _, configEq⟩ := member
  have fieldDifferent : ref.field ≠ .inr event := by
    intro same
    rcases ref with ⟨field, layoutEq⟩
    change field = .inr event at same
    subst field
    exact notBinding owner payload layoutEq
  have storeEq : next.config.store ref.field = state.config.store ref.field := by
    rw [← configEq]
    cases fieldCase : ref.field with
    | inl input => rfl
    | inr query =>
        have different : query ≠ event := by
          intro queryEq
          apply fieldDifferent
          rw [fieldCase, queryEq]
        exact EventGraph.Config.complete_output_of_ne state.config event query ready
          action output different
  exact (ref.get?_congr _ _ storeEq).symm.trans stored

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

namespace State

omit [DecidableEq Player] in
theorem bindingResult_eq_success_iff (state : State graph) (handle : Handle graph)
    (payload : L.Ty) (value : L.Val payload) :
    state.bindingResult handle payload = .success value ↔
      state.candidates.lookup handle = .openable ⟨payload, value⟩ := by
  unfold bindingResult
  cases candidateEq : state.candidates.lookup handle with
  | fresh | unopenable => simp
  | openable raw =>
      rcases raw with ⟨rawTy, rawValue⟩
      by_cases same : rawTy = payload
      · subst rawTy
        simp [Raw.as?]
      · simp [Raw.as?, same]

/-- Accepting a fresh binding field preserves exact handle provenance. -/
theorem BindingInvariant.acceptBinding {state : State graph}
    (invariant : state.BindingInvariant) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (handle : Handle graph) (handleOwner : handle.1 = owner)
    (unused : state.HandleUnused handle) :
    ({ (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (state.bindingResult handle payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (state.bindingResult handle payload))) with
      accepted := Function.update state.accepted (.inr event) (some handle)
      candidates := state.candidates.accept handle }).BindingInvariant := by
  let result := state.bindingResult handle payload
  let completed := state.complete event ready
    (cast (congrArg EventField.Action outputEq.symm) result)
    (cast (congrArg EventField.Value outputEq.symm) result)
  let next : State graph := { completed with
    accepted := Function.update state.accepted (.inr event) (some handle)
    candidates := state.candidates.accept handle }
  change next.BindingInvariant
  refine ⟨?_, ?_, ?_⟩
  · intro field acceptedHandle accepted
    by_cases same : field = .inr event
    · subst field
      have acceptedEq : handle = acceptedHandle := by simpa [next] using accepted
      subst acceptedHandle
      exact ⟨payload, handleOwner.symm ▸ outputEq⟩
    · have old : state.accepted field = some acceptedHandle := by
        simpa [next, same] using accepted
      exact invariant.accepted_typed field acceptedHandle old
  · intro left right acceptedHandle leftAccepted rightAccepted
    by_cases leftNew : left = .inr event
    · subst left
      have acceptedEq : handle = acceptedHandle := by simpa [next] using leftAccepted
      subst acceptedHandle
      by_cases rightNew : right = .inr event
      · exact rightNew.symm
      · have old : state.accepted right = some handle := by
          simpa [next, rightNew] using rightAccepted
        exact (unused right old).elim
    · by_cases rightNew : right = .inr event
      · subst right
        have acceptedEq : handle = acceptedHandle := by simpa [next] using rightAccepted
        subst acceptedHandle
        have old : state.accepted left = some handle := by
          simpa [next, leftNew] using leftAccepted
        exact (unused left old).elim
      · apply invariant.accepted_injective left right acceptedHandle
        · simpa [next, leftNew] using leftAccepted
        · simpa [next, rightNew] using rightAccepted
  · intro refOwner refPayload ref value stored
    by_cases same : ref.field = .inr event
    · rcases ref with ⟨field, layoutEq⟩
      change field = .inr event at same
      subst field
      change graph.outputLayout event = .binding refOwner refPayload at layoutEq
      have kinds : EventField.binding owner payload =
          .binding refOwner refPayload := outputEq.symm.trans layoutEq
      cases kinds
      have layoutProof : layoutEq = outputEq := Subsingleton.elim _ _
      rw [layoutProof] at stored
      have outputStored : completed.config.store (.inr event) =
          some (cast (congrArg EventField.Value outputEq.symm) result) := by
        exact EventGraph.Config.complete_output_same state.config event ready
          (cast (congrArg EventField.Action outputEq.symm) result)
          (cast (congrArg EventField.Value outputEq.symm) result)
      have resultSuccess : result = PublicationResult.success value := by
        unfold FieldRef.get? at stored
        change cast _ (next.config.store (.inr event)) =
          some (PublicationResult.success value) at stored
        rw [show next.config = completed.config by rfl, outputStored] at stored
        change cast (congrArg Option (congrArg EventField.Value outputEq))
          (some (cast (congrArg EventField.Value outputEq.symm) result)) =
            some (PublicationResult.success value) at stored
        have castSome {alpha beta : Type} (typeEq : alpha = beta) (item : alpha) :
            cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
          subst beta
          rfl
        rw [castSome (congrArg EventField.Value outputEq)] at stored
        have castInverse {alpha beta : Type} (typeEq : alpha = beta) (item : beta) :
            cast typeEq (cast typeEq.symm item) = item := by
          subst beta
          rfl
        rw [castInverse] at stored
        simpa [result] using Option.some.inj stored
      refine ⟨handle, by simp [next], handleOwner, ?_⟩
      rw [CommitmentCandidates.lookup_accept_openable_iff]
      exact (bindingResult_eq_success_iff state handle payload value).mp resultSuccess
    · have oldStored : ref.get? state.config.store = some (.success value) := by
        have fieldEq : completed.config.store ref.field =
            state.config.store ref.field := by
          cases fieldCase : ref.field with
          | inl input => rfl
          | inr query =>
              have different : query ≠ event := by
                intro queryEq
                apply same
                rw [fieldCase, queryEq]
              exact EventGraph.Config.complete_output_of_ne state.config event query ready
                (cast (congrArg EventField.Action outputEq.symm) result)
                (cast (congrArg EventField.Value outputEq.symm) result) different
        unfold FieldRef.get? at stored ⊢
        rw [show next.config = completed.config by rfl, fieldEq] at stored
        exact stored
      obtain ⟨oldHandle, oldAccepted, oldOwner, oldCandidate⟩ :=
        invariant.success_provenance ref value oldStored
      refine ⟨oldHandle, ?_, oldOwner, ?_⟩
      · simpa [next, same] using oldAccepted
      · rw [CommitmentCandidates.lookup_accept_openable_iff]
        exact oldCandidate

end State

/-- Every accepted event packet preserves binding-handle provenance. -/
theorem handle_bindingInvariant (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (invariant : state.BindingInvariant)
    (accepted : handle runtime state message = some next) :
    next.BindingInvariant := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | bind owner payload outputEq codeEq =>
              simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
              split at accepted
              · simp_all only [dite_eq_ite, Option.ite_none_right_eq_some,
                    Option.some.injEq]
                rcases accepted with ⟨_ownerEq, _vacant, unused, rfl⟩
                exact invariant.acceptBinding event ready owner payload outputEq candidate
                  (by assumption) unused
              · simp_all only [reduceCtorEq]
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | opening event candidate raw =>
      obtain ⟨completed, _, ready, action, member⟩ :=
        handle_config_mem_step runtime state next ⟨id, .opening event candidate raw⟩ accepted
      have completedEq : completed = event := by simp_all [Payload.event?]
      subst completed
      obtain ⟨acceptedEq, candidatesEq⟩ := handle_resolution_tables runtime state next
        ⟨id, .opening event candidate raw⟩ (by simp) accepted
      apply bindingInvariant_of_nonbinding_step invariant event ready action member
        acceptedEq candidatesEq
      intro owner payload bindingEq
      cases view : nodeView graph event with
      | bind => simp [handle, ready, view] at accepted
      | sample => simp [handle, ready, view] at accepted
      | resolve resolveOwner resolvePayload binding checks outputEq codeEq =>
          rw [outputEq] at bindingEq
          cases bindingEq
  | withhold event =>
      obtain ⟨completed, _, ready, action, member⟩ :=
        handle_config_mem_step runtime state next ⟨id, .withhold event⟩ accepted
      have completedEq : completed = event := by simp_all [Payload.event?]
      subst completed
      obtain ⟨acceptedEq, candidatesEq⟩ := handle_resolution_tables runtime state next
        ⟨id, .withhold event⟩ (by simp) accepted
      apply bindingInvariant_of_nonbinding_step invariant event ready action member
        acceptedEq candidatesEq
      intro owner payload bindingEq
      cases view : nodeView graph event with
      | bind => simp [handle, ready, view] at accepted
      | sample => simp [handle, ready, view] at accepted
      | resolve resolveOwner resolvePayload binding checks outputEq codeEq =>
          rw [outputEq] at bindingEq
          cases bindingEq

omit [DecidableEq Player] in
/-- Every supported environment command preserves binding provenance. -/
theorem environmentStep_bindingInvariant (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (invariant : state.BindingInvariant)
    (member : next ∈ (environmentStep runtime state command).support) :
    next.BindingInvariant := by
  classical
  cases command with
  | grant event | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact invariant.copy rfl rfl rfl
  | executeSample event =>
      by_cases ready : state.config.cut.Ready event
      · cases view : nodeView graph event with
        | bind | resolve =>
            have stepEq : environmentStep runtime state (.executeSample event) =
                FinDist.pure state := by
              apply environmentStep_executeSample_of_nonsample runtime state event ready
              intro samplePayload law sampleOutputEq sampleCodeEq sampleEq
              rw [view] at sampleEq
              cases sampleEq
            rw [stepEq] at member
            simp only [FinDist.mem_support_pure] at member
            subst next
            exact invariant
        | sample payload law outputEq codeEq =>
            rw [environmentStep_executeSample_eq runtime state event ready payload law
              outputEq codeEq view, FinDist.support_map, Set.mem_image] at member
            obtain ⟨config, configMem, rfl⟩ := member
            apply bindingInvariant_of_nonbinding_step
              (next := { state with
                config := config
                activatedAt := State.refreshActivated config state.clock state.activatedAt })
              invariant event ready
              (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) configMem rfl rfl
            intro owner bindingPayload bindingEq
            rw [outputEq] at bindingEq
            cases bindingEq
      · have stepEq : environmentStep runtime state (.executeSample event) =
            FinDist.pure state := by
          exact environmentStep_executeSample_of_not_ready runtime state event ready
        rw [stepEq] at member
        simp only [FinDist.mem_support_pure] at member
        subst next
        exact invariant
  | expire event =>
      by_cases ready : state.config.cut.Ready event
      · cases activated : state.activatedAt event with
        | none =>
            rw [environmentStep_expire_of_not_activated runtime state event ready activated]
              at member
            simp only [FinDist.mem_support_pure] at member
            subst next
            exact invariant
        | some entered =>
            by_cases due : runtime.deadline event ≤ state.clock - entered
            · cases view : nodeView graph event with
              | sample payload law outputEq codeEq =>
                  rw [environmentStep_expire_sample_eq runtime state event ready entered
                    activated due payload law outputEq codeEq view] at member
                  simp only [FinDist.mem_support_pure] at member
                  subst next
                  exact invariant
              | bind owner payload outputEq codeEq =>
                  rw [environmentStep_expire_bind_eq runtime state event ready entered
                    activated due owner payload outputEq codeEq view] at member
                  simp only [FinDist.mem_support_pure] at member
                  subst next
                  apply invariant.complete_of_no_success
                  intro newOwner newPayload newEq value
                  have kinds : EventField.binding owner payload =
                      .binding newOwner newPayload := outputEq.symm.trans newEq
                  cases kinds
                  simp
              | resolve owner payload binding checks outputEq codeEq =>
                  rw [environmentStep_expire_resolve_eq runtime state event ready entered
                    activated due owner payload binding checks outputEq codeEq view] at member
                  simp only [FinDist.mem_support_pure] at member
                  subst next
                  apply invariant.complete_nonbinding
                  intro bindingOwner bindingPayload bindingEq
                  rw [outputEq] at bindingEq
                  cases bindingEq
            · rw [environmentStep_expire_of_not_due runtime state event ready entered
                activated due] at member
              simp only [FinDist.mem_support_pure] at member
              subst next
              exact invariant
      · rw [environmentStep_expire_of_not_ready runtime state event ready] at member
        simp only [FinDist.mem_support_pure] at member
        subst next
        exact invariant

/-- Every native message-application action preserves binding provenance. -/
theorem applicationStep_bindingInvariant (runtime : EventGraphRuntime graph)
    (state next : (application runtime).State)
    (action : (application runtime).Action)
    (invariant : state.application.BindingInvariant)
    (member : next ∈ ((application runtime).step state action).support) :
    next.application.BindingInvariant := by
  exact (application runtime).step_application_invariant
    State.BindingInvariant
    (fun application who command hinvariant =>
      privateStep_bindingInvariant application hinvariant who command)
    (fun application message result hinvariant accepted =>
      handle_bindingInvariant runtime application result message hinvariant accepted)
    (fun application command result hinvariant supported =>
      environmentStep_bindingInvariant runtime application result command hinvariant supported)
    state next action invariant member

/-- A finite native action trace preserves binding provenance. -/
theorem run_bindingInvariant (runtime : EventGraphRuntime graph)
    (actions : List (application runtime).Action)
    (state next : (application runtime).State)
    (invariant : state.application.BindingInvariant)
    (member : next ∈ ((application runtime).run actions state).support) :
    next.application.BindingInvariant := by
  exact (application runtime).run_application_invariant State.BindingInvariant
    (fun application who command hinvariant =>
      privateStep_bindingInvariant application hinvariant who command)
    (fun application message result hinvariant accepted =>
      handle_bindingInvariant runtime application result message hinvariant accepted)
    (fun application command result hinvariant supported =>
      environmentStep_bindingInvariant runtime application result command hinvariant supported)
    state next actions invariant member

/-- Arbitrary player and environment policies preserve binding provenance
through every supported native service prefix. -/
theorem runPolicies_bindingInvariant (runtime : EventGraphRuntime graph)
    (players : Player → (application runtime).PlayerPolicy)
    (environment : (application runtime).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : (application runtime).PolicyExecution)
    (invariant : execution.native.application.BindingInvariant)
    (member : next ∈
      ((application runtime).runPolicies players environment schedule execution).support) :
    next.native.application.BindingInvariant := by
  exact (application runtime).runPolicies_application_invariant State.BindingInvariant
    (fun application who command hinvariant =>
      privateStep_bindingInvariant application hinvariant who command)
    (fun application message result hinvariant accepted =>
      handle_bindingInvariant runtime application result message hinvariant accepted)
    (fun application command result hinvariant supported =>
      environmentStep_bindingInvariant runtime application result command hinvariant supported)
    players environment schedule execution next invariant member

/-- Every supported policy run from the native initial state has binding
provenance, independently of the chosen policies and schedule. -/
theorem runPolicies_initial_bindingInvariant (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs)
    (players : Player → (application runtime).PlayerPolicy)
    (environment : (application runtime).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (next : (application runtime).PolicyExecution)
    (member : next ∈ ((application runtime).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application runtime)
        (MessageApplication.State.initial (application runtime)
          (State.initial inputs)))).support) :
    next.native.application.BindingInvariant := by
  exact runPolicies_bindingInvariant runtime players environment schedule _ next
    (State.initial_bindingInvariant inputs) member

end Vegas.EventGraphRuntime

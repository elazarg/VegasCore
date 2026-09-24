/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventCommitmentBinding
import Vegas.Pending.EventStore

/-! # Accepted associations give candidate openings their graph meaning

An accepted handle is already fixed. If its opening has the binding's type,
the graph store contains exactly that value. This direction also covers a
certificate obtained before the handle was associated with any game field.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

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

structure AssociationInvariant (state : State graph) : Prop where
  accepted_fixed : ∀ field candidate, state.accepted field = some candidate →
    state.candidates.lookup candidate ≠ .fresh
  accepted_present : ∀ field candidate, state.accepted field = some candidate →
    (state.config.store field).isSome = true
  opening_stored : ∀ {owner payload}
      (binding : FieldRef graph.layout (.binding owner payload)) (candidate : Handle graph)
      (value : L.Val payload),
    state.accepted binding.field = some candidate →
    state.candidates.lookup candidate = .openable ⟨payload, value⟩ →
    binding.get? state.config.store = some (.success value)

omit [DecidableEq Player] in
theorem AssociationInvariant.accepted_complete {state : State graph}
    (valid : state.AssociationInvariant) (event : graph.EventId) (candidate : Handle graph)
    (accepted : state.accepted (.inr event) = some candidate) :
    event ∈ state.config.cut.completed :=
  (state.config.output_available event).mp (valid.accepted_present _ candidate accepted)

omit [DecidableEq Player] in
theorem AssociationInvariant.transport {state next : State graph}
    (valid : state.AssociationInvariant) (accepted : next.accepted = state.accepted)
    (fixed : ∀ candidate, state.candidates.lookup candidate ≠ .fresh →
      next.candidates.lookup candidate = state.candidates.lookup candidate)
    (stored : ∀ field value, state.config.store field = some value →
      next.config.store field = some value) : next.AssociationInvariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro field candidate associated
    rw [accepted] at associated
    have prior := valid.accepted_fixed field candidate associated
    rwa [fixed candidate prior]
  · intro field candidate associated
    rw [accepted] at associated
    obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp
      (valid.accepted_present field candidate associated)
    rw [stored field value present]
    rfl
  · intro owner payload binding candidate value associated opened
    rw [accepted] at associated
    rw [fixed candidate (valid.accepted_fixed binding.field candidate associated)] at opened
    exact binding.get?_preserved _ _ stored _
      (valid.opening_stored binding candidate value associated opened)

theorem initial_associationInvariant (inputs : graph.Inputs) :
    (State.initial inputs).AssociationInvariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro field candidate accepted
    obtain ⟨input, owner, payload, rfl, kind, rfl⟩ :=
      initial_accepted_eq_some inputs field candidate accepted
    rw [initial_candidate]
    generalize inputEq : inputs input = value
    have impossible (kind : EventField Player L) (value : kind.Value)
        (eq : kind = .binding owner payload) :
        candidateOfValue owner kind value ≠ .fresh := by
      subst kind
      cases value <;> simp [candidateOfValue]
    exact impossible _ _ kind
  · intro field candidate accepted
    obtain ⟨input, _, _, rfl, _, _⟩ :=
      initial_accepted_eq_some inputs field candidate accepted
    rfl
  · intro owner payload binding candidate value accepted opened
    obtain ⟨input, actualOwner, actualPayload, field, kind, candidateEq⟩ :=
      initial_accepted_eq_some inputs binding.field candidate accepted
    rcases binding with ⟨fieldName, layout⟩
    change fieldName = .inl input at field
    subst fieldName
    change graph.inputLayout input = .binding owner payload at layout
    have equal : EventField.binding actualOwner actualPayload = .binding owner payload :=
      kind.symm.trans layout
    cases equal
    subst candidate
    rw [initial_candidate] at opened
    have inputValue (kind : EventField Player L) (inputValue : kind.Value)
        (eq : kind = .binding owner payload)
        (proof : candidateOfValue owner kind inputValue = .openable ⟨payload, value⟩) :
        cast (congrArg EventField.Value eq) inputValue = .success value := by
      subst kind
      cases inputValue with
      | failure => simp [candidateOfValue] at proof
      | success selected =>
          simp only [candidateOfValue, ↓reduceIte, CommitmentCandidate.openable.injEq] at proof
          cases proof
          rfl
    have result := inputValue _ (inputs input) layout opened
    change cast (congrArg Option (congrArg EventField.Value layout))
      (some (inputs input)) = some (.success value)
    have castSome {α β : Type} (eq : α = β) (x : α) :
        cast (congrArg Option eq) (some x) = some (cast eq x) := by
      subst β
      rfl
    rw [castSome (congrArg EventField.Value layout), result]

omit [DecidableEq Player] in
theorem AssociationInvariant.complete {state : State graph}
    (valid : state.AssociationInvariant) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (output : (graph.outputLayout event).Value) :
    (state.complete event ready action output).AssociationInvariant :=
  valid.transport rfl (fun _ _ => rfl)
    (state.config.complete_store_of_some event ready action output)

theorem AssociationInvariant.acceptBinding {state : State graph}
    (valid : state.AssociationInvariant) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (selected : Handle graph) :
    ({ (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) (state.bindingResult selected payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (state.bindingResult selected payload))) with
      accepted := Function.update state.accepted (.inr event) (some selected)
      candidates := state.candidates.freeze selected }).AssociationInvariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro field candidate associated
    by_cases same : field = .inr event
    · subst field
      have equal : selected = candidate := by simpa using associated
      subst candidate
      exact state.candidates.lookup_freeze_ne_fresh selected
    · have old : state.accepted field = some candidate := by simpa [same] using associated
      have fixed := valid.accepted_fixed field candidate old
      change (state.candidates.freeze selected).lookup candidate ≠ .fresh
      rwa [state.candidates.lookup_freeze_eq_of_not_fresh candidate selected fixed]
  · intro field candidate associated
    by_cases same : field = .inr event
    · subst field
      change ((state.config.complete event ready _ _).outputs event).isSome = true
      rw [EventGraph.Config.complete_output_same]
      rfl
    · have old : state.accepted field = some candidate := by simpa [same] using associated
      obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp
        (valid.accepted_present field candidate old)
      change ((state.config.complete event ready _ _).store field).isSome = true
      rw [state.config.complete_store_of_some event ready _ _ field value present]
      rfl
  · intro refOwner refPayload binding candidate value associated opened
    by_cases same : binding.field = .inr event
    · rcases binding with ⟨field, layout⟩
      change field = .inr event at same
      subst field
      have equal : selected = candidate := by simpa using associated
      subst candidate
      change (state.candidates.freeze selected).lookup selected = _ at opened
      rw [CommitmentCandidates.lookup_freeze_openable_iff] at opened
      change graph.outputLayout event = .binding refOwner refPayload at layout
      have kinds : EventField.binding owner payload = .binding refOwner refPayload :=
        outputEq.symm.trans layout
      cases kinds
      have meaning : state.bindingResult selected payload = .success value :=
        (State.bindingResult_eq_success_iff state selected payload value).mpr opened
      change cast (congrArg Option (congrArg EventField.Value layout))
        ((state.config.complete event ready _ _).outputs event) = _
      rw [EventGraph.Config.complete_output_same]
      rw [meaning]
      have inverse {α β : Type} (eq : α = β) (x : β) :
          cast (congrArg Option eq) (some (cast eq.symm x)) = some x := by
        subst β
        rfl
      exact inverse (congrArg EventField.Value outputEq) (.success value)
    · have old : state.accepted binding.field = some candidate := by simpa [same] using associated
      change (state.candidates.freeze selected).lookup candidate = _ at opened
      rw [CommitmentCandidates.lookup_freeze_openable_iff] at opened
      exact binding.get?_preserved _ _ (state.config.complete_store_of_some event ready _ _) _
        (valid.opening_stored binding candidate value old opened)

end State

theorem privateStep_associationInvariant (state : State graph) (who : Player)
    (command : PrivateCommand graph) (valid : state.AssociationInvariant) :
    (privateStep state who command).AssociationInvariant :=
  valid.transport (congrArg PublicView.accepted (privateStep_publicView state who command))
    (fun candidate fixed => privateStep_lookup_of_not_fresh state who command candidate fixed)
    (fun field value stored => by rw [(privateStep_facts state who command).1]; exact stored)

theorem submitStep_associationInvariant (state : State graph) (who : Player)
    (packet : Payload graph) (valid : state.AssociationInvariant) :
    (submitStep state who packet).AssociationInvariant :=
  valid.transport (congrArg PublicView.accepted (submitStep_publicView state who packet))
    (fun candidate fixed => submitStep_lookup_of_not_fresh state who packet candidate fixed)
    (fun field value stored => by rw [submitStep_config]; exact stored)

theorem handle_associationInvariant (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (valid : state.AssociationInvariant)
    (accepted : handle runtime state message = some next) : next.AssociationInvariant := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | opening event candidate raw | withhold event =>
      exact valid.transport
        (handle_resolution_tables runtime state next _ (by intros; simp) accepted).1
        (fun queried fixed =>
          handle_lookup_of_not_fresh runtime state next _ queried fixed accepted)
        (handle_store_of_some runtime state next _ accepted)
  | commitment event selected =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve | sample => simp [handle, ready, timely, view] at accepted
          | bind owner payload outputEq codeEq =>
              simp only [handle, dite_eq_left ready, dite_eq_left timely, view] at accepted
              split at accepted
              · simp_all only [dite_eq_ite, Option.ite_none_right_eq_some, Option.some.injEq]
                rcases accepted with ⟨_, _, _, rfl⟩
                exact valid.acceptBinding event ready owner payload outputEq selected
              · simp_all only [reduceCtorEq]
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
omit [DecidableEq Player] in
theorem environmentStep_associationInvariant (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (valid : state.AssociationInvariant)
    (reached : next ∈ (environmentStep runtime state command).support) :
    next.AssociationInvariant :=
  valid.transport (environmentStep_tables runtime state next command reached).1
    (fun _ _ => by rw [(environmentStep_tables runtime state next command reached).2])
    (environmentStep_store_of_some runtime state next command reached)

end Vegas.EventGraphRuntime

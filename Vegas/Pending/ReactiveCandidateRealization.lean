/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAllocation
import Vegas.Pending.EventInitialObservation
import Vegas.Pending.EventBindingInvariant

/-! # Candidate catalogues represented by completed bindings

At completed canonical service prefixes every fixed candidate belongs to an
accepted typed binding and has exactly its stored meaning. Dynamic prepared
slots are included. This property permits reconstruction of one owner's whole
catalogue from its semantic graph observation and the public accepted handles.
It is not asserted between submission and inclusion, when a new private
candidate has been prepared but is not yet associated with a completed field.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace State

/-- Every allocated candidate is accounted for by its actual accepted field.
Initial candidates and dynamically allocated candidates obey the same rule. -/
def CandidatesRepresented (state : State graph) : Prop :=
  ∀ candidate, state.candidates.lookup candidate ≠ .fresh →
    ∃ field, ∃ value : (graph.layout field).Value,
      state.accepted field = some candidate ∧ state.config.store field = some value ∧
      state.candidates.lookup candidate = candidateOfValue candidate.1 (graph.layout field) value

omit [IExpr.ResultTypes L] in
private theorem candidateOfValue_fixed (who : Player) (kind : EventField Player L)
    (value : kind.Value) (fixed : candidateOfValue who kind value ≠ .fresh) :
    ∃ payload, kind = .binding who payload := by
  cases kind with
  | publicData payload | publication payload | privateInput owner payload => exact (fixed rfl).elim
  | binding owner payload =>
      by_cases own : owner = who
      · subst owner
        exact ⟨payload, rfl⟩
      · simp only [candidateOfValue, ite_eq_right own] at fixed
        exact (fixed rfl).elim

omit [IExpr.ResultTypes L] in
private theorem candidateOfValue_cast (who : Player) {kind other : EventField Player L}
    (equal : kind = other) (value : other.Value) :
    candidateOfValue who kind (cast (congrArg EventField.Value equal.symm) value) =
      candidateOfValue who other value := by
  cases equal
  rfl

theorem candidatesRepresented_initial (inputs : graph.Inputs) :
    (initial inputs).CandidatesRepresented := by
  rintro ⟨who, slot⟩ fixed
  cases slot with
  | prepared serial => exact (fixed (initial_candidate inputs who (.prepared serial))).elim
  | initial input =>
      have meaning := initial_candidate inputs who (.initial input)
      change (initial inputs).candidates.lookup (who, .initial input) =
        candidateOfValue who (graph.inputLayout input) (inputs input) at meaning
      obtain ⟨payload, binding⟩ := candidateOfValue_fixed who (graph.inputLayout input)
        (inputs input) (meaning ▸ fixed)
      exact ⟨.inl input, inputs input, initial_accepted_binding inputs input who payload binding,
        rfl, meaning⟩

/-- Extensions of the semantic store preserve catalogue realization when
the accepted handles and candidate tables stay fixed. This covers resolved
publications, samples and clocks at the corresponding service steps. -/
theorem CandidatesRepresented.transport {before after : State graph}
    (represented : before.CandidatesRepresented)
    (accepted : after.accepted = before.accepted)
    (candidates : after.candidates = before.candidates)
    (store : ∀ field value, before.config.store field = some value →
      after.config.store field = some value) : after.CandidatesRepresented := by
  intro candidate fixed
  rw [candidates] at fixed
  obtain ⟨field, value, associated, stored, meaning⟩ := represented candidate fixed
  exact ⟨field, value, by rwa [accepted], store field value stored, by rwa [candidates]⟩

/-- Associating the freshly allocated slot with its completed binding extends
the catalogue representation; all older associations retain their meanings. -/
theorem CandidatesRepresented.associate {before after : State graph}
    (represented : before.CandidatesRepresented) (field : graph.Field)
    (candidate : Handle graph) (value : (graph.layout field).Value)
    (vacant : before.accepted field = none)
    (accepted : after.accepted = Function.update before.accepted field (some candidate))
    (candidates : ∀ query, after.candidates.lookup query =
      if query = candidate then candidateOfValue candidate.1 (graph.layout field) value
      else before.candidates.lookup query)
    (stored : after.config.store field = some value)
    (retained : ∀ oldField oldValue, before.config.store oldField = some oldValue →
      after.config.store oldField = some oldValue) : after.CandidatesRepresented := by
  intro query fixed
  by_cases same : query = candidate
  · subst query
    exact ⟨field, value, by simp [accepted], stored, by simp [candidates]⟩
  · have oldFixed : before.candidates.lookup query ≠ .fresh := by
      simpa only [candidates, ite_eq_right same] using fixed
    obtain ⟨oldField, oldValue, associated, oldStored, meaning⟩ := represented query oldFixed
    have different : oldField ≠ field := by
      rintro rfl
      rw [vacant] at associated
      cases associated
    exact ⟨oldField, oldValue, by simp [accepted, different, associated],
      retained oldField oldValue oldStored, by simpa [candidates, same] using meaning⟩

theorem CandidatesRepresented.complete {state : State graph}
    (represented : state.CandidatesRepresented) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (state.complete event ready action value).CandidatesRepresented := by
  exact represented.transport rfl rfl
    (state.config.complete_store_of_some event ready action value)

/-- Samples, deadlines and clock ticks retain the actual
binding-to-candidate representation. Deferred checks need no extra premise. -/
theorem CandidatesRepresented.environmentStep {state : State graph}
    (represented : state.CandidatesRepresented) (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (next : State graph)
    (supported : next ∈ (environmentStep runtime state command).support) :
    next.CandidatesRepresented := by
  obtain ⟨accepted, candidates⟩ := environmentStep_tables runtime state next command supported
  exact represented.transport accepted candidates
    (environmentStep_store_of_some runtime state next command supported)

/-- Owned source-visible fields determine all owned candidate meanings at a
canonical completed prefix. No independence of private initial types is used. -/
theorem CandidatesRepresented.candidates_eq_of_observation
    {left right : State graph} (leftRepresented : left.CandidatesRepresented)
    (rightRepresented : right.CandidatesRepresented)
    (leftValid : left.BindingInvariant) (rightValid : right.BindingInvariant)
    (who : Player) (accepted : left.accepted = right.accepted)
    (observed : graph.playerObserve who left.config = graph.playerObserve who right.config) :
    (fun slot => left.candidates.lookup (who, slot)) =
      fun slot => right.candidates.lookup (who, slot) := by
  funext slot
  by_cases leftFresh : left.candidates.lookup (who, slot) = .fresh
  · by_cases rightFresh : right.candidates.lookup (who, slot) = .fresh
    · exact leftFresh.trans rightFresh.symm
    · obtain ⟨field, _value, associated, _stored, _meaning⟩ :=
        rightRepresented (who, slot) rightFresh
      exact (leftValid.accepted_fixed field (who, slot) (accepted ▸ associated) leftFresh).elim
  · obtain ⟨field, value, associated, stored, meaning⟩ :=
      leftRepresented (who, slot) leftFresh
    have rightAssociated : right.accepted field = some (who, slot) := accepted ▸ associated
    obtain ⟨otherField, otherValue, otherAssociated, otherStored, otherMeaning⟩ :=
      rightRepresented (who, slot) (rightValid.accepted_fixed field _ rightAssociated)
    have fieldEq := rightValid.accepted_injective field otherField _
      rightAssociated otherAssociated
    subst otherField
    obtain ⟨payload, kind⟩ := leftValid.accepted_typed field (who, slot) associated
    have visible : graph.fieldVisibleTo who field := by
      change (graph.layout field).VisibleTo who
      rw [kind]
      rfl
    have storedEq := store_eq_of_playerObserve_eq who left.config right.config observed
      field visible
    have values : value = otherValue := Option.some.inj (stored.symm.trans
      (storedEq.trans otherStored))
    rw [meaning, otherMeaning, values]

end State

/-- The canonical binding response fixes exactly its selected fresh candidate
to the declared typed result, including a genuinely unusable binding. -/
theorem reactiveBinding_candidate_lookup (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (query : Handle graph) :
    let submitted := execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload result serial)
    submitted.application.candidates.lookup query = if query = (owner, .prepared serial) then
          State.candidateOfValue owner (.binding owner payload) result
        else execution.application.candidates.lookup query := by
  let material : Submission graph := ⟨.commitment event (owner, .prepared serial),
    match result with | .failure => none | .success value => some ⟨payload, value⟩⟩
  rcases query with ⟨observer, slot⟩
  by_cases sameOwner : observer = owner
  · subst observer
    change (submitStep (material.register execution.application owner) owner
      material.packet).candidates.lookup (owner, slot) = _
    rw [material.candidateAfter_eq]
    by_cases same : slot = .prepared serial
    · subst slot
      cases result <;> simp [material, Submission.candidateAfter, fresh, State.candidateOfValue]
    · simp [material, Submission.candidateAfter, same]
  · have unchanged := (submitStep_playerView_other (material.register execution.application owner)
      owner observer sameOwner material.packet).trans
        (material.register_other execution.application owner observer sameOwner)
    have candidateEq := congrFun (congrArg PlayerView.candidates unchanged) slot
    change (submitStep (material.register execution.application owner) owner
      material.packet).candidates.lookup (observer, slot) = _
    simpa [sameOwner, State.playerView] using candidateEq

end Vegas.EventGraphRuntime

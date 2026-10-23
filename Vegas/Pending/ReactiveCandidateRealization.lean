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

end State

end Vegas.EventGraphRuntime

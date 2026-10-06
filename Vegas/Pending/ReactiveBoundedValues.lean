/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBoundedHandles
import Vegas.Pending.ReactiveInitialValues
import Vegas.Pending.EventBindingInvariant

/-! # Reachable commitment values stay in the message alphabet

Submission can introduce only its supplied opening material. Inclusion cannot
create a new opening value. Thus covering the finite initial values suffices
to keep every later openable candidate inside the declared response alphabet,
even after arbitrary raw deviations. Publication types need not be finite.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph)

def CandidateValues (state : State graph) : Prop :=
  ∀ candidate raw, state.candidates.lookup candidate = .openable raw → raw ∈ bounds.values

omit [DecidableEq Player] in
/-- Typed values are covered by actual binding provenance; no enumeration of
the entire publication type is needed. -/
theorem binding_value_covered (state : State graph) (valid : state.BindingInvariant)
    (covered : bounds.CandidateValues state) {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload)) (value : L.Val payload)
    (stored : binding.get? state.config.store = some (.success value)) :
    (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
  obtain ⟨candidate, _, _, opened⟩ := valid.success_provenance binding value stored
  exact covered candidate ⟨payload, value⟩ opened

omit [DecidableEq Player] in
theorem resolved_value_covered (state : State graph) (valid : state.BindingInvariant)
    (covered : bounds.CandidateValues state) {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks true state.config.store =
      some (.success value)) : (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
  apply bounds.binding_value_covered state valid covered binding value
  simp only [EventCode.resolveOutput?, ↓reduceIte, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at resolved
  obtain ⟨bound, stored, accepted, _, output⟩ := resolved
  cases accepted with
  | false => cases output
  | true =>
      have same : bound = .success value := Option.some.inj output
      simpa only [same] using stored

theorem candidateValues_submit (state : State graph) (who : Player)
    (material : Submission graph) (valid : bounds.CandidateValues state)
    (allowed : bounds.AllowsOpening material.opening) :
    bounds.CandidateValues (submitStep (material.register state who) who material.packet) := by
  have registered : bounds.CandidateValues (material.register state who) := by
    rcases material with ⟨packet, opening⟩
    cases packet with
    | commitment event candidate =>
        rcases candidate with ⟨owner, slot⟩
        cases slot with
        | initial input => exact valid
        | prepared serial =>
            cases opening with
            | none => exact valid
            | some submitted =>
                by_cases owned : owner = who
                · simp only [Submission.register, owned, ↓reduceIte]
                  intro candidate raw opened
                  rcases state.candidates.lookup_prepare_openable_origin who (.prepared serial)
                    submitted candidate raw opened with previous | ⟨_, same⟩
                  · exact valid candidate raw previous
                  · simpa only [AllowsOpening, same] using allowed
                · simpa only [Submission.register, owned, ↓reduceIte] using valid
    | opening | malformed => exact valid
  intro candidate raw opened
  cases packet : material.packet with
  | commitment event selected =>
      simp only [submitStep, packet] at opened
      split at opened
      · exact registered candidate raw
          ((CommitmentCandidates.lookup_freeze_openable_iff ..).mp opened)
      · exact registered candidate raw opened
  | opening | malformed =>
      exact registered candidate raw (by simpa only [submitStep, packet] using opened)

theorem candidateValues_handle (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (valid : bounds.CandidateValues state)
    (accepted : handle runtime state message = some next) : bounds.CandidateValues next := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | commitment event selected =>
      intro candidate raw opened
      rw [(handle_commitment_tables runtime state next id event selected accepted).1] at opened
      exact valid candidate raw ((CommitmentCandidates.lookup_freeze_openable_iff ..).mp opened)
  | opening event candidate raw =>
      have tables := handle_resolution_tables runtime state next _ (by intros; simp) accepted
      simpa only [CandidateValues, tables.2] using valid
  | malformed raw => simp only [handle] at accepted; contradiction

theorem candidateValues_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (valid : bounds.CandidateValues execution.application)
    (allowed : ∀ material, response.transmission = some material →
      bounds.AllowsOpening material.call.opening) :
    bounds.CandidateValues
      (execution.respond (runtime.reactiveApplication leaks) who response).application := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact valid
  | some material =>
      exact bounds.candidateValues_submit execution.application who
        material.call valid (allowed material rfl)

theorem candidateValues_environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : bounds.CandidateValues execution.application)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : bounds.CandidateValues next.application := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid
      | some message =>
          change bounds.CandidateValues
            (((runtime.reactiveApplication leaks).handle execution.application
              message).getD execution.application)
          cases accepted : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none => exact valid
          | some state =>
              exact bounds.candidateValues_handle runtime execution.application state
                ⟨message.id, message.payload.call⟩ valid (reactiveHandle_call accepted)
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      simpa only [CandidateValues,
        (environmentStep_tables runtime execution.application state command changed).2] using valid

variable [Fintype Player]

theorem candidateValues_raw_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (covered : ∀ state ∈ initial.support, bounds.CandidateValues state) :
    ∀ {state} (_trace : ((bounds.rawMenu runtime leaks).protocol initial
      horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant
        (fun execution => bounds.CandidateValues execution.application) state := by
  have invariant : (bounds.rawMenu runtime leaks).ServiceInvariant scheduler
      (fun execution => bounds.CandidateValues execution.application) := {
    respond := fun execution who response valid legal =>
      bounds.candidateValues_respond runtime leaks execution who response valid (by
        intro material submitted
        rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at legal
        rw [submitted] at legal
        exact ((bounds.submissions_mem _ _).mp legal).1.2)
    environment := fun execution next command valid _ reached =>
      bounds.candidateValues_environment runtime leaks execution next command valid reached }
  intro state trace
  exact invariant.history initial horizon covered trace

theorem candidateValues_initial (inputs : PMF graph.Inputs) (finite : inputs.support.Finite)
    (input : graph.Inputs) (supported : input ∈ inputs.support) :
    (bounds.withInitialValues (inputs.map State.initial)).CandidateValues
      (State.initial input) := by
  intro candidate raw opened
  rcases candidate with ⟨who, slot⟩
  cases slot with
  | initial index =>
      exact bounds.initial_value_covered (inputs.map State.initial)
        (by rw [PMF.support_map]; exact finite.image _) (State.initial input)
        (PMF.support_map .. ▸ ⟨input, supported, rfl⟩) who index raw opened
  | prepared serial =>
      rw [State.initial_candidate] at opened
      contradiction

/-- Every candidate obtainable in the full raw finite game is encodable;
the compiler's finite alphabet is chosen before any strategy. -/
theorem candidateValues_initialized_raw_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (finite : inputs.support.Finite) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : (((bounds.withInitialValues (inputs.map State.initial)).rawMenu runtime leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state) :
    ReactiveApplication.serviceInvariant
      (fun execution => (bounds.withInitialValues (inputs.map State.initial)).CandidateValues
        execution.application) state := by
  apply (bounds.withInitialValues (inputs.map State.initial)).candidateValues_raw_history
    runtime leaks (inputs.map State.initial) horizon scheduler _ trace
  intro initial supported
  obtain ⟨input, present, rfl⟩ := PMF.support_map .. ▸ supported
  exact bounds.candidateValues_initial inputs finite input present

end Vegas.EventGraphRuntime.MessageBounds

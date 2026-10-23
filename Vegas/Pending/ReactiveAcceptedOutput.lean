/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveSignedCommitments
import Vegas.Pending.EventBindingInvariant

/-! # Accepted calls write successful outputs

A field value of a binding or publication kind is a failure when it records a
failed result (`Vegas.EventGraph.EventField.IsFailure`). Every runtime operation keeps the meaning
    of a fixed candidate
(`Vegas.EventGraphRuntime.keepsFixedCandidates_step`) and every stored field
(`Vegas.EventGraphRuntime.keepsStore_step`).

An accepted commitment whose handle holds an openable meaning of the bound type
writes a success to its event's output
(`Vegas.EventGraphRuntime.handle_commitment_output_success`), and an accepted
opening whose resolution, evaluated on the store it is included at, publishes a
success writes that success
(`Vegas.EventGraphRuntime.handle_opening_output_success`).
-/

noncomputable section

namespace Vegas.EventGraph.EventField

variable {Player : Type} {L : IExpr}

/-- A field value records a failed result: a failed binding or a failed
publication. Other field kinds never fail. -/
def IsFailure : (kind : EventField Player L) → kind.Value → Prop
  | .binding _ _, value => value = .failure
  | .publication _, value => value = .failure
  | .publicData _, _ => False
  | .privateInput _ _, _ => False

end Vegas.EventGraph.EventField

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The event's output holds a value that is not a failure. -/
def OutputSucceeded (store : Store graph.layout) (event : graph.EventId) : Prop :=
  ∃ value, store (.inr event) = some value ∧ ¬ (graph.layout (.inr event)).IsFailure value

omit [DecidableEq Player] in
/-- Reading a non-failure through a reference to the event's output field is
a successful output. -/
theorem outputSucceeded_of_ref (store : Store graph.layout) (event : graph.EventId)
    {kind : EventField Player L} (ref : FieldRef graph.layout kind)
    (field : ref.field = .inr event) {value : kind.Value} (read : ref.get? store = some value)
    (succeeded : ¬ kind.IsFailure value) : OutputSucceeded store event := by
  rcases ref with ⟨refField, layoutEq⟩
  change refField = .inr event at field
  subst field
  subst layoutEq
  exact ⟨value, read, succeeded⟩

omit [DecidableEq Player] in
/-- A stored success is kept by every operation that keeps stored fields. -/
theorem OutputSucceeded.mono {before after : Store graph.layout} {event : graph.EventId}
    (succeeded : OutputSucceeded before event)
    (kept : ∀ field value, before field = some value → after field = some value) :
    OutputSucceeded after event := by
  obtain ⟨value, stored, notFailed⟩ := succeeded
  exact ⟨value, kept _ value stored, notFailed⟩

/-- `after` keeps the meaning of every candidate fixed at `before`. -/
def KeepsFixedCandidates (before after : State graph) : Prop :=
  ∀ handle, before.candidates.lookup handle ≠ .fresh →
    after.candidates.lookup handle = before.candidates.lookup handle

/-- `after` keeps every stored field of `before`. -/
def KeepsStore (before after : State graph) : Prop :=
  ∀ field value, before.config.store field = some value → after.config.store field = some value

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- **Fixed meanings stay fixed** under every runtime operation. -/
theorem keepsFixedCandidates_step :
    (runtime.reactiveApplication leaks).StepRelation KeepsFixedCandidates where
  refl _ _ _ := rfl
  submit state who material handle fixed := by
    change (submitStep (material.call.register state who) who
      material.call.packet).candidates.lookup handle = _
    have registered := material.call.register_lookup_of_not_fresh state who handle fixed
    rw [submitStep_lookup_of_not_fresh _ _ _ _ (registered ▸ fixed), registered]
  handle state message next accepted handle fixed := by
    rcases handle_tables_cases runtime state next _ (reactiveHandle_call accepted) with
      ⟨_, candidate, _, candidates, _⟩ | ⟨_, candidates⟩
    · rw [candidates, state.candidates.lookup_freeze_eq_of_not_fresh handle candidate fixed]
    · rw [candidates]
  environment state command next reached handle _ := by
    rw [(environmentStep_tables runtime state next command reached).2]

/-- **Stored fields stay stored** under every runtime operation. -/
theorem keepsStore_step : (runtime.reactiveApplication leaks).StepRelation KeepsStore where
  refl _ _ _ stored := stored
  submit state who material field value stored := by
    change (submitStep (material.call.register state who) who
      material.call.packet).config.store field = some value
    rw [submitStep_config]
    unfold Submission.register
    split
    · split <;> exact stored
    · exact stored
  handle state message next accepted field value stored :=
    handle_store_of_some runtime state next _ (reactiveHandle_call accepted) field value stored
  environment state command next reached field value stored :=
    environmentStep_store_of_some runtime state next command reached field value stored

/-- **An accepted commitment writes a success.** If the contract accepts a
commitment for a binding event whose handle holds an openable meaning of the
bound type, the event's output is that success. -/
theorem handle_commitment_output_success (state next : State graph) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next)
    (valid : state.BindingInvariant) (owner : Player) (payload : L.Ty)
    (layoutEq : graph.layout (.inr event) = .binding owner payload) (value : L.Val payload)
    (fixed : state.candidates.lookup candidate = .openable ⟨payload, value⟩) :
    OutputSucceeded next.config.store event := by
  obtain ⟨candidates, acceptedEq, _⟩ :=
    handle_commitment_tables runtime state next id event candidate accepted
  have nextValid := handle_bindingInvariant runtime state next _ valid accepted
  let ref : FieldRef graph.layout (.binding owner payload) := ⟨.inr event, layoutEq⟩
  have associated : next.accepted ref.field = some candidate := by
    change next.accepted (.inr event) = some candidate
    rw [acceptedEq, Function.update_self]
  have nextFixed : next.candidates.lookup candidate = .openable ⟨payload, value⟩ := by
    rw [candidates, state.candidates.lookup_freeze_eq_of_not_fresh candidate candidate
      (by rw [fixed]; exact fun impossible => by cases impossible), fixed]
  exact outputSucceeded_of_ref _ event ref rfl
    (nextValid.opening_stored ref candidate value associated nextFixed)
    (fun failed => by cases failed)

omit [DecidableEq Player] in
private theorem cast_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [DecidableEq Player] in
private theorem cast_cast_symm {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  cases same
  rfl

/-- **An accepted opening writes a success.** If the contract accepts an
opening for a resolution whose evaluation on the current store publishes a
success, the event's output is that success. -/
theorem handle_opening_output_success (state next : State graph) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (accepted : handle runtime state ⟨id, .opening event candidate raw⟩ = some next)
    (owner : Player) (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks true state.config.store =
      some (.success value)) :
    OutputSucceeded next.config.store event := by
  obtain ⟨ready, action, member, _, _, owner', payload', binding', checks', outputEq', codeEq',
    node', actionEq⟩ := handle_opening_config_step runtime state next id event candidate raw
      accepted
  rw [node] at node'
  cases node'
  subst actionEq
  rw [state.config.step_eq_map_of_code event ready outputEq
    (.resolve owner payload binding checks) codeEq true (PMF.pure (.success value))
    (by rw [EventCode.resolve_eval?, resolved]; rfl)] at member
  rw [PMF.pure_map, PMF.mem_support_pure_iff] at member
  let ref : FieldRef graph.layout (.publication payload) := ⟨.inr event, outputEq⟩
  refine outputSucceeded_of_ref _ event ref rfl (value := .success value) ?_
    (fun failed => by cases failed)
  simp only [ref, FieldRef.get?]
  change cast _ (next.config.outputs event) = _
  rw [member, Config.complete_output_same,
    cast_some (congrArg EventField.Value outputEq), cast_cast_symm]

end Vegas.EventGraphRuntime

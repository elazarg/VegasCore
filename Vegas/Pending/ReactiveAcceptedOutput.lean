/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveSignedCommitments
import Vegas.Pending.EventBindingInvariant
import Vegas.Pending.ExclusionInvariant

/-! # Typed results of accepted calls

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
    obtain ⟨native, handled, rfl⟩ := reactiveHandle_call accepted
    rw [native.drain_tables.2.1]
    rcases handle_tables_cases runtime state native _ handled with
      ⟨_, candidate, _, candidates, _⟩ | ⟨_, candidates⟩
    · rw [candidates, state.candidates.lookup_freeze_eq_of_not_fresh handle candidate fixed]
    · rw [candidates]
  environment state command next reached handle _ := by
    rw [(reactiveApplication_environment_tables runtime leaks state next command reached).2]

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
  handle state message next accepted field value stored := by
    obtain ⟨native, handled, rfl⟩ := reactiveHandle_call accepted
    exact native.drain_store_of_some field value
      (handle_store_of_some runtime state native _ handled field value stored)
  environment state command next reached field value stored := by
    change next ∈ ((environmentStep runtime state command).map State.drain).support at reached
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    exact native.drain_store_of_some field value
      (environmentStep_store_of_some runtime state native command moved field value stored)

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
  have ownerActive : owner ∉ state.config.defaulted := by
    obtain ⟨active, _ready, _timely, actor, input, ref, guards, layoutEq, nativeCode,
      opening, result, nativeNode, sender, _rest⟩ :=
      (handle_opening_iff runtime state next id event candidate raw).mp accepted
    rw [node] at nativeNode
    cases nativeNode
    simpa only [sender] using active
  obtain ⟨ready, action, member, _, _, owner', payload', binding', checks', outputEq', codeEq',
    node', actionEq⟩ := handle_opening_config_step runtime state next id event candidate raw
      accepted
  rw [node] at node'
  cases node'
  subst actionEq
  rw [state.config.step_eq_map_of_code event ready outputEq
    (.resolve owner payload binding checks) codeEq true (PMF.pure (.success value))
    (by
      simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right ownerActive]
      rw [EventCode.resolve_eval?, resolved]
      rfl)] at member
  rw [PMF.pure_map, PMF.mem_support_pure_iff] at member
  let ref : FieldRef graph.layout (.publication payload) := ⟨.inr event, outputEq⟩
  refine outputSucceeded_of_ref _ event ref rfl (value := .success value) ?_
    (fun failed => by cases failed)
  simp only [ref, FieldRef.get?]
  change cast _ (next.config.outputs event) = _
  rw [member, Config.complete_output_same,
    cast_some (congrArg EventField.Value outputEq), cast_cast_symm]

/-- A call's fixed meaning certifies its actual action and typed output when accepted at `sent`. -/
def AcceptanceWitness (event : graph.EventId)
    (message : Message Player (WitnessedPacket graph)) (sent : graph.Config)
    (action : graph.Action event) (output : (graph.outputLayout event).Value)
    (state : State graph) : Prop :=
  (∃ candidate owner payload, ∃ layoutEq : graph.outputLayout event = .binding owner payload,
    message.payload.call = .commitment event candidate ∧
      state.candidates.lookup candidate ≠ .fresh ∧
      action = cast (congrArg EventField.Action layoutEq.symm)
        (some (state.bindingResult candidate payload)) ∧
      output = cast (congrArg EventField.Value layoutEq.symm)
        (state.bindingResult candidate payload)) ∨
  (∃ candidate raw owner payload binding checks outputEq codeEq result,
    message.payload.call = .opening event candidate raw ∧
      nodeView graph event = .resolve owner payload binding checks outputEq codeEq ∧
      EventCode.resolveOutput? binding checks true sent.store = some result ∧
      action = cast (congrArg EventField.Action outputEq.symm) true ∧
      output = cast (congrArg EventField.Value outputEq.symm) result)

omit [DecidableEq Player] in
theorem AcceptanceWitness.keep {event : graph.EventId}
    {message : Message Player (WitnessedPacket graph)} {sent : graph.Config}
    {action : graph.Action event}
    {output : (graph.outputLayout event).Value} {before after : State graph}
    (witness : AcceptanceWitness event message sent action output before)
    (kept : KeepsFixedCandidates before after) :
    AcceptanceWitness event message sent action output after := by
  rcases witness with ⟨candidate, owner, payload, layoutEq, call, fixed, decision, result⟩ | opening
  · have lookup := kept candidate fixed
    have meaning : after.bindingResult candidate payload =
        before.bindingResult candidate payload := by
      unfold State.bindingResult
      rw [lookup]
    refine Or.inl ⟨candidate, owner, payload, layoutEq, call, ?_, ?_, ?_⟩
    · rw [lookup]
      exact fixed
    · rw [meaning]
      exact decision
    · rw [meaning]
      exact result
  · exact Or.inr opening

/-- A certified accepted call performs its actual graph action with its exact typed result. -/
theorem AcceptanceWitness.complete
    {event : graph.EventId} {message : Message Player (WitnessedPacket graph)}
    {sent : graph.Config} {action : graph.Action event} {output : (graph.outputLayout event).Value}
    {state next : State graph}
    (witness : AcceptanceWitness event message sent action output state)
    (sameConfig : state.config = sent)
    (accepted : handle runtime state ⟨message.id, message.payload.call⟩ = some next) :
    ∃ ready : sent.cut.Ready event, sent.actualDecision event action = some action ∧
      next.config = sent.complete event ready action output := by
  subst sent
  rcases witness with ⟨candidate, owner, payload, layoutEq, call, _, decision, outputValue⟩ |
    ⟨candidate, raw, owner, payload, binding, checks, outputEq, codeEq, result,
      call, node, resolved, decision, outputValue⟩
  · rw [call] at accepted
    obtain ⟨active, ready, _, otherOwner, otherPayload, otherLayout, otherCode, _, sender,
      _, _, _, nativeEq⟩ :=
      (handle_commitment_iff runtime state next message.id event candidate).mp accepted
    have sameKind := layoutEq.symm.trans otherLayout
    cases sameKind
    have activeOwner : owner ∉ state.config.defaulted := by simpa only [sender] using active
    have actor := nodeView_bind_actor layoutEq otherCode
    refine ⟨ready, state.config.actualDecision_of_active event owner actor activeOwner action, ?_⟩
    rw [nativeEq]
    change state.config.complete event ready _ _ = state.config.complete event ready action output
    rw [decision, outputValue]
  · rw [call] at accepted
    obtain ⟨active, ready, _, otherOwner, otherPayload, otherBinding, otherChecks,
      otherOutput, otherCode, _, otherResult, actualNode, sender, _, _, _, _, _,
      actualResult, nativeEq⟩ :=
      (handle_opening_iff runtime state next message.id event candidate raw).mp accepted
    rw [node] at actualNode
    cases actualNode
    rw [resolved] at actualResult
    cases Option.some.inj actualResult
    have activeOwner : owner ∉ state.config.defaulted := by simpa only [sender] using active
    have actor := nodeView_resolve_actor outputEq codeEq
    refine ⟨ready, state.config.actualDecision_of_active event owner actor activeOwner action, ?_⟩
    rw [nativeEq]
    change state.config.complete event ready _ _ = state.config.complete event ready action output
    rw [decision, outputValue]

/-- A ready active owner's typed accepted-call result is supported by the graph executor. -/
theorem AcceptanceWitness.complete_mem_step
    {event : graph.EventId} {message : Message Player (WitnessedPacket graph)}
    {sent : graph.Config} {action : graph.Action event} {output : (graph.outputLayout event).Value}
    {state : State graph}
    (witness : AcceptanceWitness event message sent action output state)
    (sameConfig : state.config = sent) (ready : sent.cut.Ready event)
    (who : Player) (owned : graph.actor? event = some who) (active : who ∉ sent.defaulted) :
    sent.complete event ready action output ∈ (sent.step event ready action).support := by
  subst sent
  rcases witness with ⟨candidate, owner, payload, layoutEq, call, _, decision, outputValue⟩ |
    ⟨candidate, raw, owner, payload, binding, checks, outputEq, codeEq, result,
      call, node, resolved, decision, outputValue⟩
  · have codeEq : cast (congrArg (EventCode graph.layout) layoutEq) (graph.nodes event) =
        .bind owner payload := by
      generalize cast (congrArg (EventCode graph.layout) layoutEq) (graph.nodes event) = lowered
      cases lowered
      rfl
    have same : owner = who :=
      Option.some.inj ((nodeView_bind_actor layoutEq codeEq).symm.trans owned)
    subst who
    rw [decision, outputValue]
    rw [state.config.step_eq_map_of_code event ready layoutEq (.bind owner payload) codeEq
      (some (state.bindingResult candidate payload))
      (PMF.pure (state.bindingResult candidate payload))]
    · simp
    · simp only [EventCode.effectiveAction, EventCode.actor, active, ↓reduceIte,
        EventCode.eval?, Option.getD_some]
  · have same : owner = who :=
      Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
    subst who
    rw [decision, outputValue]
    rw [state.config.step_eq_map_of_code event ready outputEq
      (.resolve owner payload binding checks) codeEq true (PMF.pure result)]
    · simp
    · change (EventCode.resolveOutput? binding checks
        (if owner ∈ state.config.defaulted then false else true) state.config.store).map
          PMF.pure = _
      rw [ite_eq_right active, resolved]
      rfl

/-- Acceptance writes the certified result, including a failed publication. -/
theorem AcceptanceWitness.output_eq
    {event : graph.EventId} {message : Message Player (WitnessedPacket graph)}
    {sent : graph.Config} {action : graph.Action event} {output : (graph.outputLayout event).Value}
    {state next : State graph}
    (witness : AcceptanceWitness event message sent action output state)
    (sameConfig : state.config = sent)
    (accepted : handle runtime state ⟨message.id, message.payload.call⟩ = some next) :
    next.config.outputs event = some output := by
  obtain ⟨ready, _, completed⟩ := witness.complete runtime sameConfig accepted
  rw [completed, Config.complete_output_same]

/-- Automatic completions retain the actual decision certified by an accepted call. -/
theorem AcceptanceWitness.reactive_decision
    {event : graph.EventId} {message : Message Player (WitnessedPacket graph)}
    {sent : graph.Config} {action : graph.Action event} {output : (graph.outputLayout event).Value}
    {state next : State graph}
    (witness : AcceptanceWitness event message sent action output state)
    (sameConfig : state.config = sent)
    (accepted : (runtime.reactiveApplication leaks).handle state message = some next) :
    ∃ defaultEvent, (⟨event, some action, defaultEvent⟩ : graph.Completion) ∈
      next.config.history := by
  obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
  obtain ⟨ready, recorded, completed⟩ := witness.complete runtime sameConfig handled
  obtain ⟨tail, historyEq⟩ := Config.Step.path_history_prefix native.drain_graph_steps
  rw [nextEq] at historyEq
  refine ⟨(graph.nodes event).defaultEvent action output, ?_⟩
  rw [← historyEq]
  apply List.mem_append_left
  rw [completed, Config.complete_history, recorded]
  exact List.mem_append_right _ (List.mem_singleton_self _)


/-- A certified result is successful precisely when its typed value is not a failure. -/
theorem AcceptanceWitness.output_success
    {event : graph.EventId} {message : Message Player (WitnessedPacket graph)}
    {sent : graph.Config} {action : graph.Action event} {output : (graph.outputLayout event).Value}
    {state next : State graph}
    (witness : AcceptanceWitness event message sent action output state)
    (sameConfig : state.config = sent)
    (succeeded : ¬ (graph.outputLayout event).IsFailure output)
    (accepted : handle runtime state ⟨message.id, message.payload.call⟩ = some next) :
    OutputSucceeded next.config.store event :=
  ⟨output, witness.output_eq runtime sameConfig accepted, succeeded⟩

end Vegas.EventGraphRuntime

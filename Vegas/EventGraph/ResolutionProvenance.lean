module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Execution

@[expose] public section

/-! # Successful publication comes from the retained binding

Resolution may hide a binding by returning failure. It cannot publish a different
value, and a value it publishes passes the deferred checks on every later
store. Both facts hold throughout every graph-reachable configuration.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem cast_option_none {α β : Type} (same : α = β) :
    cast (congrArg Option same) (none : Option α) = (none : Option β) := by
  cases same
  rfl

theorem EventCode.binding_success_of_resolve_success
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (disclose : Bool) (store : Store graph.layout) (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks disclose store =
      some (.success value)) :
    binding.get? store = some (.success value) := by
  unfold EventCode.resolveOutput? at resolved
  cases boundEq : binding.get? store with
  | none => simp [boundEq] at resolved
  | some bound =>
      cases checksEq : GuardCheck.allAccepted? checks store
          (if disclose then bound else .failure) with
      | none => simp [boundEq, checksEq] at resolved
      | some accepted =>
          cases disclose <;> cases accepted <;>
            simp_all

/-- A successful publication has passed every deferred check on the published
value. This is the same check an auditor can run from the public store. -/
theorem EventCode.guards_pass_of_resolve_success
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (disclose : Bool) (store : Store graph.layout) (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks disclose store =
      some (.success value)) :
    GuardCheck.allAccepted? checks store (.success value) = some true := by
  have stored := EventCode.binding_success_of_resolve_success binding checks disclose
    store value resolved
  unfold EventCode.resolveOutput? at resolved
  cases disclose with
  | false =>
      cases accepted : GuardCheck.allAccepted? checks store .failure with
      | none => simp [stored, accepted] at resolved
      | some flag => cases flag <;> simp [stored, accepted] at resolved
  | true =>
      cases accepted : GuardCheck.allAccepted? checks store (.success value) with
      | none => simp [stored, accepted] at resolved
      | some flag => cases flag <;> simp_all

omit R in
private theorem option_value_cast_roundtrip
    {left right : EventField Player L} (same : left = right)
    (value : right.Value) :
    cast (congrArg Option (congrArg EventField.Value same))
        (some (cast (congrArg EventField.Value same.symm) value)) = some value := by
  cases same
  rfl

variable [DecidableEq Player]

/-- Completing a resolution stores exactly the result of its effective disclosure,
with defaulted owners withheld automatically. The statement transports the endpoint
value back across the public-output identification so callers need not expose
the evaluator's dependent casts. -/
theorem Config.resolution_step_output
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (config next : graph.Config) (ready : config.cut.Ready event)
    (action : graph.Action event)
    (member : next ∈ (config.step event ready action).support) :
    EventCode.resolveOutput? binding checks
        (if owner ∈ config.defaulted then false else
          cast (congrArg EventField.Action outputEq) action) config.store =
      cast (congrArg Option (congrArg EventField.Value outputEq))
        (next.outputs event) := by
  let requested := cast (congrArg EventField.Action outputEq) action
  let disclose := if owner ∈ config.defaulted then false else requested
  have readsEq : (graph.nodes event).readFields =
      insert binding.field (GuardCheck.listReadFields checks) := by
    calc
      (graph.nodes event).readFields =
          (cast (congrArg (EventCode graph.layout) outputEq)
            (graph.nodes event)).readFields := by
        exact (EventCode.readFields_cast outputEq (graph.nodes event)).symm
      _ = (EventCode.resolve owner payload binding checks).readFields :=
        congrArg EventCode.readFields codeEq
      _ = insert binding.field (GuardCheck.listReadFields checks) := rfl
  have available : ∀ field ∈ insert binding.field
      (GuardCheck.listReadFields checks),
      (config.store field).isSome = true := by
    intro field fieldMem
    apply config.read_available ready
    rw [readsEq]
    exact fieldMem
  have defined := EventCode.resolveOutput?_isSome binding checks disclose
    config.store available
  cases resolved : EventCode.resolveOutput? binding checks disclose config.store with
  | none => simp [resolved] at defined
  | some result =>
      have graphLaw := config.step_eq_map_of_code event ready outputEq
        (.resolve owner payload binding checks) codeEq requested (PMF.pure result)
      rw [EventCode.resolve_eval?] at graphLaw
      change (EventCode.resolveOutput? binding checks disclose config.store).map PMF.pure =
        some (PMF.pure result) → _ at graphLaw
      rw [resolved] at graphLaw
      specialize graphLaw rfl
      simp only [PMF.pure_map] at graphLaw
      have actionRoundtrip :
          cast (congrArg EventField.Action outputEq.symm) requested = action := by
        simp [requested]
      rw [actionRoundtrip] at graphLaw
      rw [graphLaw, PMF.mem_support_pure_iff _ _] at member
      subst next
      rw [Config.complete_output_same]
      exact (option_value_cast_roundtrip outputEq result).symm


/-- Every successful resolution in a reachable graph retains the same successful
binding, including after arbitrary subsequent graph events. -/
theorem Config.Reachable.publication_binding {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (value : L.Val payload)
    (published : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      config.store = some (.success value)) :
    binding.get? config.store = some (.success value) := by
  induction reachable with
  | initial =>
      have absent : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
          (Config.initial inputs).store = none := by
        unfold FieldRef.get? Config.store Config.initial
        exact cast_option_none (congrArg EventField.Value outputEq)
      rw [absent] at published
      cases published
  | @step before prior completed ready action after reached ih =>
      apply binding.get?_preserved before.store after.store
        (fun field result stored => before.step_store_of_some after completed ready action
          reached field result stored) (.success value)
      by_cases same : completed = event
      · subst completed
        have resolved := Config.resolution_step_output event owner payload binding checks
          outputEq codeEq before after ready action reached
        change EventCode.resolveOutput? binding checks _ before.store =
          (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
            after.store at resolved
        rw [published] at resolved
        exact EventCode.binding_success_of_resolve_success binding checks _ before.store
          value resolved
      · apply ih
        have storedEq : after.outputs event = before.outputs event := by
          obtain ⟨result, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact before.complete_output_of_ne completed event ready action result (Ne.symm same)
        have viewEq :=
          (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?_congr
          after.store before.store storedEq
        rwa [viewEq] at published

omit [DecidableEq Player] in
/-- The deferred checks of a publication read only inputs and outputs of its
predecessors. A store that retains those outputs keeps their verdict. -/
theorem Config.publication_guards_retained (event : graph.EventId) (owner : Player)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (first second : graph.Config)
    (settled : ∀ predecessor ∈ graph.order.predecessors event,
      predecessor ∈ first.cut.completed)
    (retained : ∀ field value, first.store field = some value →
      second.store field = some value)
    (proposal : PublicationResult (L.Val payload)) :
    GuardCheck.allAccepted? checks first.store proposal =
      GuardCheck.allAccepted? checks second.store proposal := by
  have readsEq : (graph.nodes event).readFields =
      insert binding.field (GuardCheck.listReadFields checks) := by
    calc
      (graph.nodes event).readFields =
          (cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event)).readFields :=
        (EventCode.readFields_cast outputEq (graph.nodes event)).symm
      _ = (EventCode.resolve owner payload binding checks).readFields :=
        congrArg EventCode.readFields codeEq
      _ = insert binding.field (GuardCheck.listReadFields checks) := rfl
  apply GuardCheck.allAccepted?_congr
  intro field member
  have read : field ∈ (graph.nodes event).readFields := by
    rw [readsEq]
    exact Finset.mem_insert_of_mem member
  have available : (first.store field).isSome := by
    cases field with
    | inl input => simp [Config.store]
    | inr producer =>
        rw [Config.store_output, first.output_available]
        exact settled producer (graph.reads_available event (.inr producer) read)
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp available
  rw [stored, retained field value stored]

/-- A successful publication in a reachable configuration passes its deferred
checks on the current store, including after arbitrary later graph events. -/
theorem Config.Reachable.publication_guards {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (value : L.Val payload)
    (published : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      config.store = some (.success value)) :
    GuardCheck.allAccepted? checks config.store (.success value) = some true := by
  induction reachable with
  | initial =>
      have absent : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
          (Config.initial inputs).store = none := by
        unfold FieldRef.get? Config.store Config.initial
        exact cast_option_none (congrArg EventField.Value outputEq)
      rw [absent] at published
      cases published
  | @step before prior completed ready action after reached ih =>
      have retained : ∀ field value, before.store field = some value →
          after.store field = some value := fun field result stored =>
        before.step_store_of_some after completed ready action reached field result stored
      by_cases same : completed = event
      · subst completed
        have resolved := Config.resolution_step_output event owner payload binding checks
          outputEq codeEq before after ready action reached
        change EventCode.resolveOutput? binding checks _ before.store =
          (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
            after.store at resolved
        rw [published] at resolved
        rw [← Config.publication_guards_retained event owner payload binding checks outputEq
          codeEq before after (fun predecessor inside => ready.2 inside) retained]
        exact EventCode.guards_pass_of_resolve_success binding checks _ before.store
          value resolved
      · have storedEq : after.outputs event = before.outputs event := by
          obtain ⟨result, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact before.complete_output_of_ne completed event ready action result (Ne.symm same)
        have viewEq :=
          (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?_congr
          after.store before.store storedEq
        rw [viewEq] at published
        have done : event ∈ before.cut.completed := by
          rw [← before.output_available]
          change (before.store (.inr event)).isSome = true
          unfold FieldRef.get? at published
          revert published
          generalize before.store (.inr event) = stored
          cases stored with
          | none =>
              intro published
              cases published.symm.trans (cast_option_none (congrArg EventField.Value outputEq))
          | some _ => intro _; rfl
        rw [← Config.publication_guards_retained event owner payload binding checks outputEq
          codeEq before after (fun predecessor inside => before.cut.predecessor_closed done inside)
          retained]
        exact ih published

/-- A completed binding stores the value of its optional actual decision.
Automatic completion and public omission both store failure. -/
theorem Config.binding_step_output
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (config next : graph.Config) (ready : config.cut.Ready event)
    (action : graph.Action event)
    (member : next ∈ (config.step event ready action).support) :
    next.outputs event = some (cast (congrArg EventField.Value outputEq.symm)
      (((config.actualDecision event action).bind fun chosen =>
        cast (congrArg EventField.Action outputEq) chosen).getD .failure)) := by
  let choice := cast (congrArg EventField.Action outputEq) action
  have law := config.step_eq_map_of_code event ready outputEq (.bind owner payload) codeEq
    choice (PMF.pure ((if owner ∈ config.defaulted then none else choice).getD .failure)) rfl
  have actionRoundtrip : cast (congrArg EventField.Action outputEq.symm) choice = action := by
    simp [choice]
  rw [actionRoundtrip, PMF.pure_map] at law
  rw [law, PMF.mem_support_pure_iff] at member
  subst next
  rw [Config.complete_output_same]
  have owned : (graph.nodes event).actor = some owner :=
    (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
      (congrArg EventCode.actor codeEq)
  by_cases inactive : owner ∈ config.defaulted <;>
    simp [Config.actualDecision, EventCode.actualDecision, owned, inactive, choice]

/-- Every recorded binding in a reachable graph retains its actual binding value. -/
theorem Config.Reachable.binding_output {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs) (record : graph.Completion)
    (present : record ∈ config.history) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout record.event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes record.event) = .bind owner payload) :
    config.outputs record.event = some (cast (congrArg EventField.Value outputEq.symm)
      ((record.decision.bind fun chosen =>
        cast (congrArg EventField.Action outputEq) chosen).getD .failure)) := by
  induction reachable with
  | initial => cases present
  | step priorReachable event ready action next supported ih =>
      rename_i before
      obtain ⟨value, stored, history⟩ := before.step_completion event ready action next supported
      rw [history] at present
      rcases List.mem_append.mp present with old | new
      · exact before.step_store_of_some next event ready action supported (.inr record.event) _
          (ih old)
      · cases List.mem_singleton.mp new
        exact before.binding_step_output event owner payload outputEq codeEq next ready action
          supported

/-- A successful recorded publication retains an actual disclosure decision,
including after later supported graph completions. -/
theorem Config.Reachable.publication_decision_of_success
    {inputs : graph.Inputs} {config : graph.Config} (reachable : config.Reachable inputs)
    (record : graph.Completion) (member : record ∈ config.history)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout record.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes record.event) =
      .resolve owner payload binding checks)
    (value : L.Val payload)
    (published : (⟨.inr record.event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      config.store = some (.success value)) :
    record.decision.map (cast (congrArg EventField.Action outputEq)) = some true := by
  induction reachable with
  | initial => cases member
  | @step before prior completed ready action after reached ih =>
      obtain ⟨result, _output, history⟩ :=
        before.step_completion completed ready action after reached
      rw [history, List.mem_append] at member
      rcases member with member | fresh
      · have done : record.event ∈ before.cut.completed :=
          (before.history_exact record.event).mp (List.mem_map.mpr ⟨record, member, rfl⟩)
        have different : record.event ≠ completed := by
          intro same
          exact ready.1 (same ▸ done)
        have storedEq : after.outputs record.event = before.outputs record.event := by
          obtain ⟨output, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact before.complete_output_of_ne completed record.event ready action output different
        have viewEq :=
          (⟨.inr record.event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?_congr
            after.store before.store storedEq
        exact ih member (by rwa [viewEq] at published)
      · have same := List.mem_singleton.mp fresh
        subst record
        dsimp only [EventGraph.completion] at outputEq codeEq published ⊢
        have resolved := Config.resolution_step_output completed owner payload binding checks
          outputEq codeEq before after ready action reached
        change EventCode.resolveOutput? binding checks _ before.store =
          (⟨.inr completed, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
            after.store at resolved
        rw [published] at resolved
        have disclosed : (if owner ∈ before.defaulted then false else
            cast (congrArg EventField.Action outputEq) action) = true := by
          cases chosen : (if owner ∈ before.defaulted then false else
              cast (congrArg EventField.Action outputEq) action) with
          | true => rfl
          | false =>
              rw [chosen] at resolved
              unfold EventCode.resolveOutput? at resolved
              cases boundEq : binding.get? before.store with
              | none => simp [boundEq] at resolved
              | some bound =>
                  cases checkEq : GuardCheck.allAccepted? checks before.store .failure with
                  | none => simp [boundEq, checkEq] at resolved
                  | some accepted => cases accepted <;> simp [boundEq, checkEq] at resolved
        have active : owner ∉ before.defaulted := by
          intro inactive
          simp only [inactive, ite_true, Bool.false_eq_true] at disclosed
        have actor : (graph.nodes completed).actor = some owner := by
          rw [← EventCode.actor_cast outputEq (graph.nodes completed), codeEq]
          rfl
        have actual := before.actualDecision_of_active completed owner actor active action
        have requested : cast (congrArg EventField.Action outputEq) action = true := by
          simpa only [active, ite_false] using disclosed
        change (before.actualDecision completed action).map
          (cast (congrArg EventField.Action outputEq)) = some true
        rw [actual, Option.map_some, requested]


end Vegas.EventGraph

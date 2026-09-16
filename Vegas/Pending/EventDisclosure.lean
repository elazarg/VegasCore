/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingInvariant
import Vegas.Pending.EventPolicies

/-! # Prescribed resolution packets execute the graph kernel

The owner-local prevalidation used by `compilePlayerPolicy` is connected here
to the actual shared-message handler.  Binding provenance supplies the unique
typed opening whenever resolution succeeds; rejection and failure use the
canonical withholding packet without changing the remembered graph action.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem binding_success_of_resolve_success
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (disclose : Bool) (store : Store graph.layout) (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks disclose store =
      some (.success value)) :
    binding.get? store = some (.success value) := by
  unfold EventCode.resolveOutput? at resolved
  cases boundEq : binding.get? store with
  | none => simp [boundEq] at resolved
  | some bound =>
      cases checksEq : DeferredCheck.allAccepted? checks store
          (if disclose then bound else .failure) with
      | none => simp [boundEq, checksEq] at resolved
      | some accepted =>
          cases disclose <;> cases accepted <;>
            simp_all

omit [DecidableEq Player] R in
private theorem action_cast_roundtrip
    {left right : EventField Player L} (same : left = right)
    (action : EventField.Action left) :
    cast (congrArg EventField.Action same.symm)
        (cast (congrArg EventField.Action same) action) = action := by
  cases same
  rfl

omit [DecidableEq Player] in
private theorem EventCode.readFields_cast
    {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {left right : EventField Player L}
    (same : left = right) (code : EventCode layout left) :
    (cast (congrArg (EventCode layout) same) code).readFields = code.readFields := by
  cases same
  rfl

/-- The packet selected from an actual owner observation executes exactly the
remembered resolution action and the deterministic graph result.  This covers
false disclosure, rejected true disclosure, and a successful verified opening
in one statement. -/
theorem handle_resolutionSubmission_eq
    (runtime : EventGraphRuntime graph)
    (native : runtime.application.State)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (ready : native.application.config.cut.Ready event)
    (timely : native.application.WithinDeadline runtime event)
    (action : graph.Action event)
    (remembered : native.application.remembered event = some action)
    (invariant : native.application.BindingInvariant)
    (nonce : Nat) :
    ∃ (result : PublicationResult (L.Val payload)) (packet : Payload graph),
      EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) action)
          native.application.config.store = some result ∧
      runtime.resolutionSubmission owner event payload binding checks outputEq action
          (Interaction.MessageApplication.State.observe runtime.application native owner) =
        .submit packet ∧
      handle runtime native.application ⟨(owner, nonce), packet⟩ =
        some (native.application.complete event ready action
          (cast (congrArg EventField.Value outputEq.symm) result)) := by
  let disclose : Bool := cast (congrArg EventField.Action outputEq) action
  have actionRoundtrip :
      cast (congrArg EventField.Action outputEq.symm) disclose = action :=
    action_cast_roundtrip outputEq action
  have readsEq : (graph.nodes event).readFields =
      insert binding.field (DeferredCheck.listReadFields checks) := by
    calc
      (graph.nodes event).readFields =
          (cast (congrArg (EventCode graph.layout) outputEq)
            (graph.nodes event)).readFields := by
        exact (EventCode.readFields_cast outputEq (graph.nodes event)).symm
      _ = (EventCode.resolve owner payload binding checks).readFields :=
        congrArg EventCode.readFields codeEq
      _ = insert binding.field (DeferredCheck.listReadFields checks) := rfl
  have available : ∀ field ∈ insert binding.field
      (DeferredCheck.listReadFields checks),
      (native.application.config.store field).isSome = true := by
    intro field member
    apply native.application.config.read_available ready
    rw [readsEq]
    exact member
  have defined := EventCode.resolveOutput?_isSome binding checks disclose
    native.application.config.store available
  cases resolved : EventCode.resolveOutput? binding checks disclose
      native.application.config.store with
  | none => simp [resolved] at defined
  | some result =>
      have localResolved : EventCode.resolveOutput? binding checks disclose
          (graph.playerStore owner native.application.config.store) = some result := by
        rw [EventCode.resolveOutput?_playerStore]
        exact resolved
      cases result with
      | failure =>
          refine ⟨.failure, .withhold event, rfl, ?_, ?_⟩
          · simp only [resolutionSubmission]
            congr 1
            change (if disclose then
                match EventCode.resolveOutput? binding checks true
                    (graph.playerStore owner native.application.config.store) with
                | some (.success value) =>
                    match native.application.accepted binding.field with
                    | some candidate =>
                        if candidate.1 = owner then
                          Payload.opening event candidate ⟨payload, value⟩
                        else Payload.withhold event
                    | none => Payload.withhold event
                | some .failure | none => Payload.withhold event
              else Payload.withhold event) = Payload.withhold event
            cases disclosed : disclose with
            | false => rfl
            | true =>
                have localResolvedTrue : EventCode.resolveOutput? binding checks true
                    (graph.playerStore owner native.application.config.store) =
                      some .failure := by
                  simpa only [disclosed] using localResolved
                rw [localResolvedTrue]
                rfl
          · have rememberedCast : native.application.remembered event = some
                (cast (congrArg EventField.Action outputEq.symm) disclose) := by
              rw [actionRoundtrip]
              exact remembered
            have handled := handle_withhold_eq runtime native.application
              (owner, nonce) event owner payload binding checks outputEq codeEq node
              ready timely rfl disclose rememberedCast resolved
            rw [actionRoundtrip] at handled
            exact handled
      | success value =>
          have stored : binding.get? native.application.config.store =
              some (.success value) :=
            binding_success_of_resolve_success binding checks disclose
              native.application.config.store value resolved
          have discloseTrue : disclose = true := by
            cases disclosed : disclose with
            | false =>
                have resolvedFalse : EventCode.resolveOutput? binding checks false
                    native.application.config.store = some (.success value) := by
                  simpa only [disclosed] using resolved
                have falseResult := EventCode.resolveOutput?_false_eq_failure binding checks
                  native.application.config.store available
                rw [falseResult] at resolvedFalse
                cases Option.some.inj resolvedFalse
            | true => rfl
          obtain ⟨candidate, accepted, candidateOwner, openable⟩ :=
            invariant.success_provenance binding value stored
          refine ⟨.success value, .opening event candidate ⟨payload, value⟩,
            rfl, ?_, ?_⟩
          · simp only [resolutionSubmission]
            congr 1
            change (if disclose then
                match EventCode.resolveOutput? binding checks true
                    (graph.playerStore owner native.application.config.store) with
                | some (.success found) =>
                    match native.application.accepted binding.field with
                    | some handle =>
                        if handle.1 = owner then
                          Payload.opening event handle ⟨payload, found⟩
                        else Payload.withhold event
                    | none => Payload.withhold event
                | some .failure | none => Payload.withhold event
              else Payload.withhold event) =
                Payload.opening event candidate ⟨payload, value⟩
            rw [discloseTrue]
            simp only [if_true]
            have localResolvedTrue : EventCode.resolveOutput? binding checks true
                (graph.playerStore owner native.application.config.store) =
                  some (.success value) := by
              simpa only [discloseTrue] using localResolved
            rw [localResolvedTrue, accepted]
            simp only [candidateOwner, if_true]
          · have resolvedTrue : EventCode.resolveOutput? binding checks true
                native.application.config.store = some (.success value) := by
              simpa only [discloseTrue] using resolved
            have handled := handle_opening_eq runtime native.application (owner, nonce)
              event candidate owner payload binding checks outputEq codeEq node ready timely
              rfl candidateOwner accepted value openable stored (.success value) resolvedTrue
            have trueAction : cast (congrArg EventField.Action outputEq.symm) true =
                action := by
              rw [← discloseTrue]
              exact actionRoundtrip
            rw [trueAction] at handled
            exact handled

end Vegas.EventGraphRuntime

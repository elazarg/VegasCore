/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingBlock
import Vegas.Compile.EventGraphState
import Vegas.Compile.EventGraphHistory
import Vegas.Source.ValueBindingContinuation

/-! # Source binding repair through an actual native service block

An atomic binding response and reserved inclusion extend the compiler's typed
source-store agreement. Paired blocks carry the existing source `Patched`
invariant, including source histories and deferred obligations, through a hidden
failed binding. They do not yet simulate an arbitrary future native policy.
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem complete_commit_agrees
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (source : Config Player L Γ) (refs : ContextRefs graph.layout Γ)
    (native : graph.Config) (agree : refs.Agrees source.state native.store)
    (event : graph.EventId) (ready : native.cut.Ready event)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (choice : PublicationResult (L.Val payload)) :
    (refs.cons (name := name) ⟨.inr event, outputEq⟩).Agrees
      (commitSuccessor name guard source choice).state
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)).store := by
  apply ContextRefs.Agrees.cons
  · exact ContextRefs.Agrees.complete ready _ _ refs source.state agree before
  · rw [EventGraph.store_complete]
    simp only [EventGraph.FieldRef.get?, Function.update_self]
    have castSome {A B : Type} (same : A = B) (value : A) :
        cast (congrArg Option same) (some value) = some (cast same value) := by
      cases same
      rfl
    rw [castSome (congrArg EventGraph.EventField.Value outputEq)]
    have castInverse {A B : Type} (same : A = B) (value : B) :
        cast same (cast same.symm value) = value := by
      cases same
      rfl
    exact congrArg some (castInverse (congrArg EventGraph.EventField.Value outputEq) _)

/-- A supported actual reserved binding block agrees with the existing source
successor. The guard is recorded in that source successor and is not evaluated
at commitment. -/
theorem reactive_commit_agrees
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (source : Config Player L Γ) (refs : ContextRefs graph.layout Γ)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : graph.EventId) (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (choice : PublicationResult (L.Val payload)) (serial : Nat)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (supported : next ∈ (runtime.interactionStep leaks players network (.includeLatest event owner)
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload choice serial))).support) :
    (refs.cons (name := name) ⟨.inr event, outputEq⟩).Agrees
      (commitSuccessor name guard source choice).state next.application.config.store := by
  have law := runtime.reactiveBinding_reserved_config leaks execution owner event payload outputEq
    codeEq node choice serial ready timely fresh vacant unused serials players network
  have projected : (next.application.config, next.receipts) ∈
      ((runtime.interactionStep leaks players network (.includeLatest event owner)
        (execution.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload choice serial))).map
            (fun final => (final.application.config, final.receipts))).support := by
    rw [PMF.support_map]
    exact ⟨next, supported, rfl⟩
  rw [law, PMF.mem_support_pure_iff _ _] at projected
  have configEq := congrArg Prod.fst projected
  change next.application.config = _ at configEq
  rw [configEq]
  dsimp only
  intro readName cell ref
  exact complete_commit_agrees name guard source refs execution.application.config agree event
    ready outputEq before choice ref

/-- Decoding the actual native completion appends the source commitment
action, including its original failed or repaired value. No native response
memory is mistaken for an additional source decision. -/
theorem reactive_commit_history
    {Γ₀ : SourceCtx Player L} {O₀ : Finset VarId}
    (whole : SourceProgram Player L Γ₀ O₀)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload) (source : Config Player L Γ)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (history : decodeHistory whole execution.application.config.history = source.history)
    (event : (toEventGraph whole).EventId)
    (outputEq : (toEventGraph whole).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (toEventGraph whole).layout) outputEq)
      ((toEventGraph whole).nodes event) = .bind owner payload)
    (node : nodeView (toEventGraph whole) event = .bind owner payload outputEq codeEq)
    (choice : PublicationResult (L.Val payload))
    (decoded : decodeEventAction whole event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice))
    (serial : Nat) (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (supported : next ∈ (runtime.interactionStep leaks players network (.includeLatest event owner)
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload choice serial))).support) :
    decodeHistory whole next.application.config.history =
      (commitSuccessor name guard source choice).history := by
  have law := runtime.reactiveBinding_reserved_config leaks execution owner event payload outputEq
    codeEq node choice serial ready timely fresh vacant unused serials players network
  have projected : (next.application.config, next.receipts) ∈
      ((runtime.interactionStep leaks players network (.includeLatest event owner)
        (execution.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload choice serial))).map
            (fun final => (final.application.config, final.receipts))).support := by
    rw [PMF.support_map]
    exact ⟨next, supported, rfl⟩
  rw [law, PMF.mem_support_pure_iff _ _] at projected
  have configEq := congrArg Prod.fst projected
  change next.application.config = _ at configEq
  rw [configEq]
  change decodeHistory whole (execution.application.config.history ++ [⟨event, _⟩]) = _
  rw [decodeHistory_append_completion, decoded, history]
  rfl

/-- The original and repaired source successors agree with their respective
actual native blocks. One reconstruction function is fixed before the hidden
state; the step does not choose a different source policy after observing it. -/
theorem reactive_commit_repair
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (source : Bool → Config Player L Γ) (refs : ContextRefs graph.layout Γ)
    (execution final : Bool → (runtime.reactiveApplication leaks).Execution)
    (unpatch : ViewMap owner Γ) (patched : PatchMap owner Γ)
    (invariant : Patched unpatch patched (source false).state (source true).state
      (source false).history (source true).history)
    (registry : (source false).registry = (source true).registry)
    (revelations : @Eq (Revelations Γ) (source false).revelations (source true).revelations)
    (agree : ∀ repaired, refs.Agrees (source repaired).state
      (execution repaired).application.config.store)
    (event : graph.EventId) (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (binding : PublicationResult (L.Val payload))
    (repairedBinding : PublicationResult (L.Val payload))
    (repair : repairedBinding = match binding with
      | .failure => .success (L.someValue payload)
      | .success value => .success value)
    (original : DecisionView owner Γ → Option (PublicationResult (L.Val payload)))
    (chosen : original (sourceObserve owner (source true).state, (source true).history owner) =
      some binding)
    (serial : Nat)
    (ready : ∀ repaired, (execution repaired).application.config.cut.Ready event)
    (timely : ∀ repaired, (execution repaired).application.WithinDeadline runtime event)
    (fresh : ∀ repaired,
      (execution repaired).application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : ∀ repaired, (execution repaired).application.accepted (.inr event) = none)
    (unused : ∀ repaired,
      (execution repaired).application.HandleUnused (owner, .prepared serial))
    (serials : ∀ repaired, (execution repaired).network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (supported : ∀ repaired, final repaired ∈
      (runtime.interactionStep leaks players network (.includeLatest event owner)
        ((execution repaired).respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload
            (if repaired then repairedBinding else binding) serial))).support) :
    let first := commitSuccessor name guard (source false) binding
    let second := commitSuccessor name guard (source true) repairedBinding
    Patched (unpatch.afterCommit (decide (owner = owner)) name owner payload original)
        (patched.afterCommit (decide (owner = owner)) name owner payload original)
        first.state second.state first.history second.history ∧
      first.registry = second.registry ∧
      @Eq (Revelations ((name, .commitment owner payload) :: Γ))
        first.revelations second.revelations ∧
      ∀ repaired, (refs.cons (name := name) ⟨.inr event, outputEq⟩).Agrees
        (commitSuccessor name guard (source repaired)
          (if repaired then repairedBinding else binding)).state
        (final repaired).application.config.store := by
  dsimp only
  refine ⟨patched_commit_own invariant name payload binding _ repair original chosen, ?_, ?_, ?_⟩
  · simp only [commitSuccessor, registry]
  · simp only [commitSuccessor, revelations]
  · intro repaired readName cell ref
    exact reactive_commit_agrees runtime leaks name guard (source repaired) refs
      (execution repaired) (final repaired) (agree repaired) event outputEq codeEq node before
      _ serial (ready repaired) (timely repaired) (fresh repaired) (vacant repaired)
      (unused repaired) (serials repaired) players network (supported repaired) ref

end Vegas

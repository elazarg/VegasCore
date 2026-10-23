/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphState
import Vegas.Pending.ReactiveBinding
import Interaction.ReactiveProvenance
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveAllocation
import Vegas.Pending.EventSequentialTiming
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

end Vegas

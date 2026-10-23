/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePolicy
import Vegas.Game.BindingRepairBlock
import Vegas.Compile.EventGraphStep
import Vegas.Source.DisclosureAliases

/-! # Full-source steps in the actual native service

Public sampling uses the source's exact chance law. A randomized binding
response and reserved inclusion use the source's exact binding kernel, with
freshness checked at entry. Source-store agreement for disclosure includes
deferred guards; no empty-registry or initial-only binding assumption is used.

These local equations preserve the existing source configuration and runtime
completion functions. They are ingredients for the multi-phase correspondence,
not an assumption of that correspondence or of sequential rationality.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Sampling extends the existing source environment by the actual sampled
value while keeping every earlier typed cell unchanged. -/
theorem complete_sample_agrees {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (source : Config Player L Γ) (refs : ContextRefs graph.layout Γ)
    (native : EventGraphRuntime.State graph)
    (agree : refs.Agrees source.state native.config.store)
    (event : graph.EventId) (ready : native.config.cut.Ready event)
    (outputEq : graph.outputLayout event = .publicData payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field) (value : L.Val payload) :
    (refs.cons (name := name) ⟨.inr event, outputEq⟩).Agrees
      (sampleSuccessor name source value).state
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)).config.store := by
  apply ContextRefs.Agrees.cons
  · exact ContextRefs.Agrees.complete ready _ _ refs source.state agree before
  · rw [EventGraphRuntime.State.complete, EventGraph.store_complete]
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

/-- The source successor stores the deferred-check result, including guard
failure. It is unnecessary to discard the registry to obtain store agreement. -/
theorem complete_guarded_reveal_agrees
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs graph.layout Γ)
    (native : EventGraphRuntime.State graph)
    (agree : refs.Agrees source.state native.config.store)
    (event : graph.EventId) (ready : native.config.cut.Ready event)
    (outputEq : graph.outputLayout event = .publication payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field) (disclose : Bool) :
    (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
      (revealSuccessor published selected source disclose).state
      (native.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (disclosureResult published selected source disclose))).config.store := by
  change (refs.cons _).Agrees (Env.cons _ source.state) _
  apply ContextRefs.Agrees.cons
  · exact ContextRefs.Agrees.complete ready _ _ refs source.state agree before
  · rw [EventGraphRuntime.State.complete, EventGraph.store_complete]
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

/-- The owner's compiled guard check returns the existing source publication
result, even with deferred obligations from earlier commitments. -/
theorem compiled_disclosure_result {Γ : SourceCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs graph.layout Γ)
    (store : EventGraph.Store graph.layout) (agree : refs.Agrees source.state store)
    (disclose : Bool) :
    EventGraph.EventCode.resolveOutput? (refs.get selected)
        (compileChecks (published := published) refs source.registry source.revelations selected)
        disclose (graph.playerStore owner store) =
      some (disclosureResult published selected source disclose) := by
  rw [EventGraph.EventCode.resolveOutput?_playerStore]
  have evaluated := compileResolve_eval? refs source.registry source.revelations
    source.state store agree (published := published) selected disclose
  rw [EventGraph.EventCode.resolve_eval?] at evaluated
  change Option.map PMF.pure _ =
    some (PMF.pure (disclosureResult published selected source disclose)) at evaluated
  cases result : EventGraph.EventCode.resolveOutput? (refs.get selected)
      (compileChecks (published := published) refs source.registry source.revelations selected)
      disclose store with
  | none => simp only [result, Option.map_none, reduceCtorEq] at evaluated
  | some value =>
      rw [result, Option.map_some, Option.some.injEq] at evaluated
      have member : value ∈ (PMF.pure value).support := by simp
      rw [evaluated, PMF.mem_support_pure_iff _ _] at member
      exact congrArg some member

end Vegas

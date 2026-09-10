/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingDefault
import Vegas.Compile.BindingSourceCoupling
import Vegas.Compile.ApplicationImageReadout

/-! # Public binding-default state and its source continuation

The default value is retained in the public disposition. It is independent of
private preparation and directly represents the corresponding source binding.
These lemmas concern the state update and its executable public expression;
they do not provide a timeout transaction, admit its inclusion, or extend the
commitment-only conditional handler to public-default continuations.
-/

namespace Vegas.ApplicationImage

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
theorem State.defaultBind_accepted (state : State P L) (code : BindingCode P)
    (value : TypedValue L) :
    (state.defaultBind code value).memory.accepted code.sourceField =
      some (.publicDefault value) := by
  simp [State.defaultBind]

omit [DecidableEq P] in
/-- Installing a default neither repairs an unopenable commitment nor changes
any private registration. Its value is held in the public disposition alone. -/
theorem State.defaultBind_private_unchanged (state : State P L) (code : BindingCode P)
    (value : TypedValue L) :
    (state.defaultBind code value).prepared = state.prepared ∧
      (state.defaultBind code value).frozen = state.frozen ∧
      (state.defaultBind code value).memory.store = state.memory.store := ⟨rfl, rfl, rfl⟩

theorem State.defaultBind_register (state : State P L) (code : BindingCode P)
    (value : TypedValue L) (who : P) (slot : Nat) (prepared : TypedValue L) :
    (state.defaultBind code value).register who slot prepared =
      (state.register who slot prepared).defaultBind code value := rfl

omit [DecidableEq P] in
/-- Private preparation cannot influence the public effect of a selected
default. The default's selection and timing remain visible public events. -/
theorem State.defaultBind_public_eq (first second : State P L)
    (hpublic : first.memory = second.memory) (code : BindingCode P) (value : TypedValue L) :
    (first.defaultBind code value).memory = (second.defaultBind code value).memory := by
  simp only [State.defaultBind, hpublic]

/-- The actual opaque-binding handler cannot overwrite an installed default,
even if the owner subsequently prepares a valid, differently valued opening. -/
theorem handle_binding_after_default (image : ApplicationImage P L)
    (state : State P L) (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (value : TypedValue L) (id : MessageId P) (handle : CommitmentHandle P Nat) :
    image.handle (state.defaultBind code value) ⟨id, .binding address handle⟩ = none := by
  rw [image.handle_binding _ address code hcode id handle]
  simp [State.defaultBind]

/-- Reading a defaulted source field does not recover a conflicting private
cache entry. A previously published field, if any, retains public precedence. -/
theorem ownerReadStore_defaultBind (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (state : State P L)
    (code : BindingCode P) (value : TypedValue L)
    (hpublic : state.memory.store code.sourceField = none) :
    image.ownerReadStore who history (state.defaultBind code value).memory code.sourceField =
      some value := by
  exact image.ownerReadStore_publicDefault who history _ code.sourceField value hpublic
    (state.defaultBind_accepted code value)

/-- Even with no private cache, a public default remains readable. Thus
replacing its disposition by an opaque handle does not preserve local readout.
This is an operational distinction, not a strategic impossibility theorem. -/
theorem defaultBind_opaque_readout_ne (image : ApplicationImage P L) (who : P)
    (state : State P L) (code : BindingCode P) (value : TypedValue L)
    (handle : CommitmentHandle P Nat) (hpublic : state.memory.store code.sourceField = none) :
    image.ownerReadStore who [] (state.defaultBind code value).memory code.sourceField ≠
      image.ownerReadStore who [] (state.bind code handle).memory code.sourceField := by
  rw [image.ownerReadStore_defaultBind who [] state code value hpublic]
  simp [ownerReadStore, State.bind, hpublic, registrationCache,
    MessageApplication.ChoiceEncoding.cachedValue]

end Vegas.ApplicationImage

noncomputable section

namespace Vegas.SourceDecisionSite.BindingDefault

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The emitted public expression and default-state update agree with the
original source commit at an exact source-prefix checkpoint. No owner's policy
or private preparation is assumed. Admission and continuation by the message
handler remain separate obligations. -/
theorem defaultBind_source_coupling
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : BindingDefault (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (native : ApplicationImage.State P L)
    (hrefines : native.Refines current.current.graph.1) :
    let value := L.eval fallback.expr current.current.source.erasePubEnv
    let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
      .here guard tail
    let code := site.bindingCode fresh build (site.compiledField fresh build)
    (fallback.compiled fresh build).evalStore? native.memory.store = some value ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard tail) fresh build).graph
          (build.addCommitEvent name who guard fresh.1).1,
        next.current.source = current.current.source.cons value ∧
        (native.defaultBind code ⟨ty, value⟩).Refines next.current.graph.1 := by
  dsimp only
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let value := L.eval fallback.expr current.current.source.erasePubEnv
  let node := site.compiledNode fresh build
  let code := site.bindingCode fresh build (site.compiledField fresh build)
  have heval := fallback.compiled_evalStore?_eq_source fresh build current.current.graph.1.store
    native.memory.store current.current.source current.current.agrees
    (fun ref href => hrefines.memory.publicFields ref
      (fallback.compiled_reads_public fresh build ref href))
  refine ⟨heval, ?_⟩
  obtain ⟨next, hsource, hgraph⟩ := binding_source_successor guard tail fresh build current
    value (fallback.legal current.current.source)
  refine ⟨next, hsource, ?_⟩
  rw [hgraph]
  have hrow : (compileCore (.commit name who guard tail) fresh build).graph.nodes[node]? =
      some (build.commitEvent who guard) := by
    rcases decisionSite_compiledRow site fresh build with ⟨located, hlocated, hrow⟩
    have heq : located = node := Fin.ext hlocated
    subst located
    exact hrow
  have hready := current.current.nextReady current.completedPrefix node (by rfl)
  let step := build.sourceCommitStep who guard current.current.graph.1
    current.current.source current.current.agrees node hrow hready value
    (fallback.legal current.current.source)
  exact hrefines.defaultBind (compileCore (.commit name who guard tail) fresh build).graphWF
    code node rfl rfl ⟨ty, value⟩ step

end Vegas.SourceDecisionSite.BindingDefault

/-- info: 'Vegas.SourceDecisionSite.BindingDefault.defaultBind_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.BindingDefault.defaultBind_source_coupling

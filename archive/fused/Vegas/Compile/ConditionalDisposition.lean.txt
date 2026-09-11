/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationResolvedBindings
import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.ConditionalPublicationSite

/-! # Typed conditional dispositions at source prefixes -/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Static binding origins and actual resolved-binding provenance reconstruct
the typed disposition consumed by a generated conditional source head. Public
defaults are type-checked through source refinement; opaque dispositions retain
the compiler-generated owner and source slot. -/
theorem bindingDisposition_at_source_prefix
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L) (native : ApplicationImage.State P L)
    (hrefines : native.Refines current.current.graph.1)
    (hresolved : image.ResolvedBindings native)
    (horigins : image.HasBindingOrigins)
    (hconditional : .conditional
      ((atHead name publicName who guard tail spec).code fresh build sourceSlot deadline) ∈
        image.instructions) :
    let site := atHead name publicName who guard tail spec
    let code := site.code fresh build sourceSlot deadline
    ∃ disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy),
      code.binding? native.memory = some disposition ∧
        ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot) := by
  intro site code
  have hcompleted : ∀ node,
      node < code.endpoint.choiceNode → native.memory.done node = true := by
    intro node hlt
    have hchoiceNode : code.endpoint.choiceNode = build.nodes.length := rfl
    have hltBuild : node < build.nodes.length := by
      rwa [hchoiceNode] at hlt
    let graphNode : Fin
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph.nodeCount :=
      ⟨node, lt_trans hlt (site.choice.choiceNode fresh build).isLt⟩
    apply (hrefines.memory.completed graphNode).mpr
    apply (current.completedPrefix graphNode).mpr
    exact hltBuild
  obtain ⟨rawDisposition, haccepted, hcanonicalRaw⟩ :=
    hresolved.conditionalDisposition horigins code hconditional
      code.endpoint.choiceNode rfl hcompleted
  cases rawDisposition with
  | «opaque» handle =>
      refine ⟨.opaque handle,
        (code.binding?_opaque_iff native.memory handle).2 haccepted, ?_⟩
      intro candidate heq
      have hsame : handle = candidate := BindingDisposition.opaque.inj heq
      subst candidate
      have hownerCode : code.endpoint.owner = who := rfl
      have hslotCode : code.endpoint.sourceSlot = sourceSlot := rfl
      simpa only [hownerCode, hslotCode] using hcanonicalRaw handle rfl
  | publicDefault typed =>
      obtain ⟨fieldSpec, hfield, _, htypedTy, _⟩ :=
        hrefines.bindings.publicDefault code.sourceField typed haccepted
      obtain ⟨compiledSpec, hcompiled, hsecret, _⟩ := site.compiledSourceField fresh build
      have hspec : fieldSpec = compiledSpec := Option.some.inj (hfield.symm.trans hcompiled)
      subst fieldSpec
      have hty : typed.ty = spec.secretTy := htypedTy.trans hsecret
      let value : L.Val spec.secretTy := cast (congrArg L.Val hty) typed.value
      have hdecode : typed.as? spec.secretTy = some value := by
        simp [TypedValue.as?, hty, value]
      refine ⟨.publicDefault value,
        (code.binding?_publicDefault_iff native.memory value).2
          ⟨typed, haccepted, hdecode⟩, ?_⟩
      intro handle hfalse
      cases hfalse

end Vegas.ConditionalPublicationSite

/-- info: 'Vegas.ConditionalPublicationSite.bindingDisposition_at_source_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.bindingDisposition_at_source_prefix

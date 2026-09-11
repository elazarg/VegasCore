/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.ConditionalImageRefinement

/-! # Full-state refinement for generated publication endpoints

The checkpoint-local publication laws lift from public memory and graph
reachability to the complete application-image refinement relation.  Existing
accepted bindings remain fixed because both generated publication updates
leave the accepted-handle and frozen-snapshot maps unchanged.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction

private theorem frozen_consistent_at_equal_type
    {L : IExpr} (frozen : Option (TypedValue L))
    (store : Store L) (field : Nat) {storedTy requestedTy : L.Ty}
    (hty : storedTy = requestedTy) (bound : L.Val storedTy)
    (hstored : Store.getAs store field storedTy = some bound)
    (hfrozen : ∀ recovered,
      frozen.bind (fun typed => typed.as? storedTy) = some recovered →
        recovered = bound) :
    ∀ value, frozen.bind (fun typed => typed.as? requestedTy) = some value →
      Store.getAs store field requestedTy = some value := by
  subst requestedTy
  intro value hrecovered
  have heq := hfrozen value hrecovered
  simpa [heq] using hstored

namespace PublicChoiceSite

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Resolution at an ordinary generated public-choice endpoint preserves the
full native-to-graph refinement relation. -/
theorem resolution_refines
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (build : BuildState P L Γ)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrefines : native.Refines cfg)
    (heligible : site.PubliclyValidatable fresh build)
    (message : Message P (L.Val site.ty)) (value : L.Val site.ty)
    (hresolve : (site.code fresh build).endpoint.resolve? native.memory.done
      ((site.code fresh build).guard.validate native.memory.store) message = some value) :
    (native.publish (site.code fresh build) value).Refines
      (site.completePublication fresh build cfg value) := by
  let G := (compileCore prog fresh build).graph
  let choice := site.choiceNode fresh build
  let publication := site.publicationNode fresh build
  let written : TypedValue L := ⟨site.ty, value⟩
  have haccepted := ((site.code fresh build).endpoint.resolve_iff
    native.memory.done ((site.code fresh build).guard.validate native.memory.store)
    message value).mp hresolve
  have hreadiness := G.publicChoice_ready cfg site.owner choice publication
    native.memory.done hrefines.memory.completed haccepted.1
  have hlower := native.publicChoice_resolution_refines site fresh build cfg
    hrefines.memory heligible hrefines.reachable message value hresolve
  refine ⟨hlower.1, hlower.2, ?_⟩
  have hbindings := hrefines.bindings.completePair hrefines.reachable
    choice publication written hreadiness.1.1 hreadiness.2.1
  constructor
  · intro field handle haccepted
    have hprior : native.memory.accepted field = some (.opaque handle) := by
      simpa only [ApplicationImage.State.publish, ApplicationImage.Memory.publish]
        using haccepted
    simpa only [ApplicationImage.State.publish, ApplicationImage.Memory.publish,
      PublicChoiceSite.completePublication, written] using
      hbindings.opaqueBinding field handle hprior
  · intro field typed haccepted
    have hprior : native.memory.accepted field = some (.publicDefault typed) := by
      simpa only [ApplicationImage.State.publish, ApplicationImage.Memory.publish]
        using haccepted
    simpa only [ApplicationImage.State.publish, ApplicationImage.Memory.publish,
      PublicChoiceSite.completePublication, written] using
      hbindings.publicDefault field typed hprior

end PublicChoiceSite

namespace ConditionalPublicationSite

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Resolution at a generated conditional endpoint preserves the full
native-to-graph relation. Opaque snapshot consistency and public-default value
agreement are both derived from the existing binding-provenance component,
rather than exposed as additional premises. -/
theorem resolution_refines
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (initial : VEnv L Γ) (legal : Legal prog)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrefines : native.Refines cfg)
    (heligible : site.PubliclyValidatable fresh build)
    (message : Message P
      (ConditionalPublication.Payload P (L.Val site.specification.secretTy)))
    (result : Option (L.Val site.specification.secretTy))
    (hresolve : (site.code fresh build sourceSlot deadline).endpoint.resolveDisposition?
      native.memory.clock (native.verify (site.code fresh build sourceSlot deadline))
      ((site.code fresh build sourceSlot deadline).binding? native.memory) native.memory.done
      ((site.code fresh build sourceSlot deadline).canOpen native.memory.store)
      message = some result) :
    (native.publishConditional (site.code fresh build sourceSlot deadline) result).Refines
      (site.completePublication fresh build cfg result) := by
  let G := (compileCore prog fresh build).graph
  let choice := site.choice.choiceNode fresh build
  let publication := site.choice.publicationNode fresh build
  let code := site.code fresh build sourceSlot deadline
  let written : TypedValue L :=
    ⟨site.choice.ty, site.specification.encoding.symm result⟩
  have hruntimeReady := code.endpoint.resolveDisposition_success_inversion native.memory.clock
    (native.verify code) (code.binding? native.memory) native.memory.done
    (code.canOpen native.memory.store) message result hresolve
  have hreadyParts := hruntimeReady
  simp only [ConditionalPublication.defaultReady, Bool.and_eq_true,
    Bool.not_eq_true'] at hreadyParts
  obtain ⟨sourceSpec, hsourceField, hsourceTy, _hsourceOwner⟩ :=
    site.compiledSourceField fresh build
  have hopaque : ∀ handle value,
      code.binding? native.memory = some (.opaque handle) →
      (native.frozen (site.sourceField fresh build)).bind
          (fun typed => typed.as? site.specification.secretTy) = some value →
        Store.getAs cfg.store (site.sourceField fresh build)
          site.specification.secretTy = some value := by
    intro handle value hbinding hsnapshot
    have haccepted := (code.binding?_opaque_iff native.memory handle).1 hbinding
    obtain ⟨spec, bound, hfield, _howner, hstored, hfrozen⟩ :=
      hrefines.bindings.opaqueBinding (site.sourceField fresh build) handle haccepted
    have hspec : spec = sourceSpec :=
      Option.some.inj (hfield.symm.trans hsourceField)
    subst spec
    exact frozen_consistent_at_equal_type
      (native.frozen (site.sourceField fresh build)) cfg.store
      (site.sourceField fresh build) hsourceTy bound hstored hfrozen value hsnapshot
  have hdefault : ∀ value,
      code.binding? native.memory = some (.publicDefault value) →
        Store.getAs cfg.store (site.sourceField fresh build)
          site.specification.secretTy = some value := by
    intro value hbinding
    obtain ⟨typed, haccepted, htyped⟩ :=
      (code.binding?_publicDefault_iff native.memory value).1 hbinding
    obtain ⟨spec, hfield, _howner, _hty, hstored⟩ :=
      hrefines.bindings.publicDefault (site.sourceField fresh build) typed haccepted
    have hspec : spec = sourceSpec :=
      Option.some.inj (hfield.symm.trans hsourceField)
    subst spec
    rw [Store.getAs, hstored]
    exact htyped
  have hlower := site.conditional_resolution_refines fresh build sourceSlot deadline
    initial legal native cfg hrefines.memory hrefines.reachable heligible hopaque hdefault
    message result hresolve
  have hreadiness := G.publication_ready cfg choice publication native.memory.done
    hrefines.memory.completed hreadyParts.1.1 hreadyParts.1.2 hreadyParts.2
  refine ⟨hlower.1, hlower.2, ?_⟩
  have hbindings := hrefines.bindings.completePair hrefines.reachable
    choice publication written hreadiness.1.1 hreadiness.2.1
  constructor
  · intro field handle haccepted
    have hprior : native.memory.accepted field = some (.opaque handle) := by
      simpa only [ApplicationImage.State.publishConditional] using haccepted
    simpa only [ApplicationImage.State.publishConditional,
      ConditionalPublicationSite.completePublication, written] using
      hbindings.opaqueBinding field handle hprior
  · intro field typed haccepted
    have hprior : native.memory.accepted field = some (.publicDefault typed) := by
      simpa only [ApplicationImage.State.publishConditional] using haccepted
    simpa only [ApplicationImage.State.publishConditional,
      ConditionalPublicationSite.completePublication, written] using
      hbindings.publicDefault field typed hprior

end ConditionalPublicationSite

end Vegas

/-- info: 'Vegas.PublicChoiceSite.resolution_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.resolution_refines

/-- info: 'Vegas.ConditionalPublicationSite.resolution_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.resolution_refines

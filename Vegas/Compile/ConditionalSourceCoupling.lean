/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceSourceCoupling

/-! # Source continuations after conditional publication

Disposition-appropriate opening and decline messages execute the same adjacent
source pair. Readiness follows from the source prefix and an accepted canonical
opaque handle or typed public default. Opaque opening uses the frozen snapshot;
default publication uses authenticated cleartext equal to the source value.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The source-order checkpoint supplies the common node readiness. An opaque
disposition must carry the generated canonical handle; a public default needs
no fabricated handle. -/
theorem readyDisposition_at_source_prefix
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (native : ApplicationImage.State P L)
    (hrefines : native.Refines current.current.graph.1)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : ((atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? native.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot)) :
    ((atHead name publicName who guard tail spec).runtimeSite
      fresh build sourceSlot deadline).readyDisposition
        (((atHead name publicName who guard tail spec).code
          fresh build sourceSlot deadline).binding? native.memory)
        native.memory.done = true := by
  have hpublic := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    native.memory.done hrefines.memory.completed
  rw [hbinding]
  cases disposition with
  | «opaque» handle =>
      have hhandle := hcanonical handle rfl
      subst handle
      simpa only [ConditionalPublication.readyDisposition, runtimeSite,
        Graph.conditionalPublication, ConditionalPublication.ready, beq_self_eq_true,
        Bool.true_and, atHead, PublicChoiceSite.atHead, PublicChoiceSite.runtimeSite,
        Graph.publicChoice, PublicChoice.ready] using hpublic
  | publicDefault value =>
      simpa only [ConditionalPublication.readyDisposition,
        ConditionalPublication.defaultReady, runtimeSite,
        Graph.conditionalPublication, atHead, PublicChoiceSite.atHead,
        PublicChoiceSite.runtimeSite, Graph.publicChoice, PublicChoice.ready] using hpublic

/-- The proof-side reference request uses an opaque opening only for an opaque
disposition. A public default is sent as cleartext; decline is common. -/
def sourceRequestPayload
    {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : ConditionalPublicationSite prog)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (sourceSlot deadline : Nat)
    (disposition : BindingDisposition (CommitmentHandle P Nat)
      (L.Val site.specification.secretTy))
    (result : Option (L.Val site.specification.secretTy)) :
    ConditionalPublication.Payload P (TypedValue L) :=
  match disposition, result with
  | .opaque _, result => (site.code fresh build sourceSlot deadline).requestPayload result
  | .publicDefault _, none => .decline
  | .publicDefault _, some value => .cleartext ⟨site.specification.secretTy, value⟩

/-- Actual inclusion realizes the selected legal source opening or decline and
preserves its exact continuation. Snapshot availability is needed only for the
opening branch. No bound on the current clock is assumed: an unresolved endpoint
accepts its owner's request even after the deadline. -/
theorem include_source_coupling
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (heligible : (atHead name publicName who guard tail spec).PubliclyValidatable fresh build)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : ((atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? execution.application.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (address serial : Nat)
    (hcode : image.lookup address = some (.conditional
      ((atHead name publicName who guard tail spec).code fresh build sourceSlot deadline)))
    (chosen : L.Val ty)
    (hlookup : execution.pool.lookup (who, serial) = some ⟨(who, serial), .conditional address
      ((atHead name publicName who guard tail spec).sourceRequestPayload
        fresh build sourceSlot deadline disposition (spec.encoding chosen))⟩)
    (hlegal : evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true)
    (hfrozen : ∀ handle value, disposition = .opaque handle →
      spec.encoding chosen = some value →
      (execution.application.frozen (build.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value) :
    ∃ next : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons chosen).cons chosen ∧
      (image.application.includePending execution (who, serial)).application.Refines
        next.current.graph.1 := by
  let site := atHead name publicName who guard tail spec
  let G := (compileCore (.commit name who guard (.reveal publicName who name .here tail))
    fresh build).graph
  let code := site.code fresh build sourceSlot deadline
  change code.binding? execution.application.memory = some disposition at hbinding
  let choice := site.choice.choiceNode fresh build
  let publication := site.choice.publicationNode fresh build
  let result := spec.encoding chosen
  let payload := site.sourceRequestPayload fresh build sourceSlot deadline disposition result
  have hdefault : ∀ value, disposition = .publicDefault value →
      value = current.current.source.get spec.binding := by
    intro value hdisposition
    subst disposition
    obtain ⟨typed, haccepted, htyped⟩ :=
      (code.binding?_publicDefault_iff execution.application.memory value).1 hbinding
    obtain ⟨_fieldSpec, _hfield, _howner, _hty, hstored⟩ :=
      hrefines.bindings.publicDefault code.sourceField typed haccepted
    have hgraphValue : Store.getAs current.current.graph.1.store code.sourceField
        spec.secretTy = some value := by
      rw [Store.getAs, hstored]
      exact htyped
    have hsourceValue := current.current.agrees spec.binding
    change Store.getAs current.current.graph.1.store (build.fieldOf spec.binding)
      spec.secretTy = some (current.current.source.get spec.binding) at hsourceValue
    have hfield : code.sourceField = build.fieldOf spec.binding := rfl
    rw [hfield] at hgraphValue
    exact Option.some.inj (hgraphValue.symm.trans hsourceValue)
  have hready := readyDisposition_at_source_prefix guard tail spec fresh build sourceSlot deadline
    current execution.application hrefines disposition hbinding hcanonical
  change code.endpoint.readyDisposition (code.binding? execution.application.memory)
    execution.application.memory.done = true at hready
  have hdecode : ∃ decoded, code.decode payload = some decoded ∧
      code.endpoint.resolveDisposition? execution.application.memory.clock
        (execution.application.verify code) (code.binding? execution.application.memory)
        execution.application.memory.done (code.canOpen execution.application.memory.store)
        ⟨(who, serial), decoded⟩ = some result := by
    cases disposition with
    | «opaque» handle =>
        have hhandle := hcanonical handle rfl
        subst handle
        refine ⟨code.endpoint.requestPayload result, code.decode_requestPayload result, ?_⟩
        simp only [ConditionalPublication.resolveDisposition?, hbinding]
        have hopaqueReady : code.endpoint.ready (some (who, sourceSlot))
            execution.application.memory.done = true := by
          simpa only [ConditionalPublication.readyDisposition, hbinding] using hready
        apply (code.endpoint.resolve_requestPayload execution.application.memory.clock
          (execution.application.verify code) (some (who, sourceSlot))
          execution.application.memory.done (code.canOpen execution.application.memory.store)
          hopaqueReady serial result).2
        cases hresult : result with
        | none => trivial
        | some value =>
            constructor
            · simpa [ApplicationImage.State.verify, code, ConditionalPublicationSite.code,
                site, atHead, sourceField, PublicChoiceSite.siteState,
                PublicChoiceSite.atHead, decisionSiteState]
                using hfrozen (who, sourceSlot) value rfl hresult
            · change site.canOpen fresh build execution.application.memory.store value = true
              have hvalue := spec.successful_value_eq_binding current.current.source
                chosen value hlegal hresult
              rw [site.canOpen_source fresh build current.current.graph.1.store
                execution.application.memory.store current.current.source heligible
                current.current.agrees hrefines.memory.publicFields value hvalue]
              have hchosen : spec.encoding.symm (some value) = chosen := by
                rw [← hresult]
                exact spec.encoding.symm_apply_apply chosen
              change evalGuard guard (spec.encoding.symm (some value))
                ((current.current.source.toView who).eraseEnv) = true
              rw [hchosen]
              exact hlegal
    | publicDefault stored =>
        have hdefaultReady :
            code.endpoint.defaultReady execution.application.memory.done = true := by
          simpa only [ConditionalPublication.readyDisposition, hbinding] using hready
        cases hresult : result with
        | none =>
            refine ⟨.decline, by
              simp [payload, sourceRequestPayload, result, hresult,
                ConditionalCode.decode], ?_⟩
            simp only [ConditionalPublication.resolveDisposition?, hbinding]
            exact (code.endpoint.resolveDefault_decline execution.application.memory.clock stored
              execution.application.memory.done (code.canOpen execution.application.memory.store)
              (who, serial)).2 ⟨hdefaultReady, rfl⟩
        | some value =>
            refine ⟨.cleartext value, ?_, ?_⟩
            · simp only [payload, sourceRequestPayload, result, hresult]
              change code.decode (.cleartext ⟨code.secretTy, value⟩) =
                some (.cleartext value)
              simp [ConditionalCode.decode, TypedValue.as?]
            simp only [ConditionalPublication.resolveDisposition?, hbinding]
            apply (code.endpoint.resolveDefault_cleartext execution.application.memory.clock
              stored value execution.application.memory.done
              (code.canOpen execution.application.memory.store) (who, serial)).2
            have hvalue := spec.successful_value_eq_binding current.current.source
              chosen value hlegal hresult
            have hstored := hdefault stored rfl
            have heq : value = stored := hvalue.trans hstored.symm
            refine ⟨hdefaultReady, rfl, heq, ?_⟩
            change site.canOpen fresh build execution.application.memory.store value = true
            rw [site.canOpen_source fresh build current.current.graph.1.store
              execution.application.memory.store current.current.source heligible
              current.current.agrees hrefines.memory.publicFields value hvalue]
            have hchosen : spec.encoding.symm (some value) = chosen := by
              rw [← hresult]
              exact spec.encoding.symm_apply_apply chosen
            change evalGuard guard (spec.encoding.symm (some value))
              ((current.current.source.toView who).eraseEnv) = true
            rw [hchosen]
            exact hlegal
  obtain ⟨decoded, hdecode, hresolve⟩ := hdecode
  have hhandle := image.handle_conditional execution.application address code hcode
    (who, serial) payload decoded hdecode
  rw [hresolve, Option.map_some] at hhandle
  have hincluded := image.include_accepted execution (who, serial)
    ⟨(who, serial), .conditional address payload⟩
    (execution.application.publishConditional code result) hlookup hhandle
  obtain ⟨next, hsource, hgraph⟩ :=
    PublicChoiceSite.source_successor guard tail fresh build current chosen hlegal
  have hpublic := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    execution.application.memory.done hrefines.memory.completed
  have hnodes := G.publicChoice_ready current.current.graph.1 who choice publication
    execution.application.memory.done hrefines.memory.completed hpublic
  have hmemory := execution.application.publishConditional_represents current.current.graph.1
    hrefines.memory code choice publication rfl rfl rfl rfl result
  change (execution.application.publishConditional code result).memory.Represents
    ((current.current.graph.1.completeNode choice
      ⟨ty, spec.encoding.symm (spec.encoding chosen)⟩).completeNode publication
        ⟨ty, spec.encoding.symm (spec.encoding chosen)⟩) at hmemory
  rw [Equiv.symm_apply_apply] at hmemory
  have hbindings := hrefines.bindings.completePair hrefines.reachable choice publication
    ⟨ty, chosen⟩ hnodes.1.1 hnodes.2.1
  have hnext : (execution.application.publishConditional code result).Refines
      next.current.graph.1 := by
    refine ⟨?_, next.current.graph.2, ?_⟩
    · rw [hgraph]
      exact hmemory
    · rw [hgraph]
      constructor
      · intro field handle haccepted
        have hprior : execution.application.memory.accepted field =
            some (.opaque handle) := by
          simpa only [ApplicationImage.State.publishConditional] using haccepted
        exact hbindings.opaqueBinding field handle hprior
      · intro field typed haccepted
        have hprior : execution.application.memory.accepted field =
            some (.publicDefault typed) := by
          simpa only [ApplicationImage.State.publishConditional] using haccepted
        exact hbindings.publicDefault field typed hprior
  refine ⟨next, hsource, ?_⟩
  have hstate : (image.application.includePending execution (who, serial)).application =
      execution.application.publishConditional code result := hincluded.1
  exact hstate.symm ▸ hnext

end Vegas.ConditionalPublicationSite

/-- info: 'Vegas.ConditionalPublicationSite.readyDisposition_at_source_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.readyDisposition_at_source_prefix

/-- info: 'Vegas.ConditionalPublicationSite.include_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.include_source_coupling

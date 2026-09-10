/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage
import Vegas.Compile.ConditionalOpeningValidation

/-! # Generated binding and conditional-publication instructions

The instructions use the same compiler allocation as ordinary public choices.
Opaque binding admission does not establish source guard legality. Generated
application plans require unrestricted original guards until a binding
validation mechanism is supplied; controller legality alone does not constrain
arbitrary runtime deviations.
Conditional validation checks the retained source guard using public fields
and either an acceptance-time verified opaque claim or the recorded typed
public default. No source environment is runtime data.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace SourceDecisionSite

/-- The exact graph node allocated to this source decision occurrence. -/
def compiledNode {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    Fin (compileCore prog fresh state).graph.nodeCount :=
  ⟨(decisionSiteState site fresh state).nodes.length, by
    rcases decisionSite_compiledRow site fresh state with ⟨node, hnode, _⟩
    rw [← hnode]
    exact node.isLt⟩

/-- Generate opaque binding metadata. Assembly supplies the service slot;
structural application plans use the compiler's source-field address. -/
def bindingCode {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) (sourceSlot : Nat) :
    BindingCode P L where
  owner := who
  ty := ty
  node := (site.compiledNode fresh state).val
  sourceField := (compileCore prog fresh state).graph.nodeTarget
    (site.compiledNode fresh state)
  sourceSlot := sourceSlot
  requires := (compileCore prog fresh state).graph.messagePrerequisites
    (site.compiledNode fresh state)

end SourceDecisionSite

namespace ConditionalPublicationSite

variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Emit a conditional-publication instruction from its source occurrence,
conditional-publication certificate, and compiler-allocated node and field addresses. -/
def code (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat) : ConditionalCode P L where
  endpoint := site.runtimeSite fresh state sourceSlot deadline
  guard := site.choice.compiledGuard fresh state
  secretTy := site.specification.secretTy
  sourceField := site.sourceField fresh state
  encoding := site.specification.encoding
  choiceField := (compileCore prog fresh state).graph.nodeTarget
    (site.choice.choiceNode fresh state)
  publicationField := (compileCore prog fresh state).graph.nodeTarget
    (site.choice.publicationNode fresh state)

/-- The reference request uses an opaque opening only for an opaque
disposition. A public default is sent as cleartext; decline is common. -/
def sourceRequestPayload
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

/-- Any resolved native result is source-legal, including declines and expiry
from an unopenable binding. Opaque claims use weak snapshot consistency;
public-default claims use their explicit equality with the source value. -/
theorem code_resolution_source_legal
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (native : ApplicationImage.State P L) (representedStore : Store L)
    (env : VEnv L site.choice.context)
    (heligible : site.PubliclyValidatable fresh state)
    (hagrees : (decisionSiteState site.choice.decision fresh state).Agrees
      representedStore env)
    (hpublicStore : ∀ ref, (compileCore prog fresh state).graph.fieldRefPublic ref →
      Store.getAs native.memory.store ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty)
    (hfrozen : ∀ value,
      (native.frozen (site.sourceField fresh state)).bind
          (fun typed => typed.as? site.specification.secretTy) = some value →
        value = env.get site.specification.binding)
    (hdefault : ∀ value,
      (site.code fresh state sourceSlot deadline).binding? native.memory =
          some (.publicDefault value) →
        value = env.get site.specification.binding)
    (message : Message P
      (ConditionalPublication.Payload P (L.Val site.specification.secretTy)))
    (result : Option (L.Val site.specification.secretTy))
    (hresolve : (site.code fresh state sourceSlot deadline).endpoint.resolveDisposition?
      native.memory.clock (native.verify (site.code fresh state sourceSlot deadline))
      ((site.code fresh state sourceSlot deadline).binding? native.memory) native.memory.done
      ((site.code fresh state sourceSlot deadline).canOpen native.memory.store)
      message = some result) :
    (result = none ∨ result = some (env.get site.specification.binding)) ∧
      evalGuard site.choice.guard (site.specification.encoding.symm result)
        ((env.toView site.choice.owner).eraseEnv) = true := by
  let emitted := site.code fresh state sourceSlot deadline
  cases result with
  | none => exact ⟨Or.inl rfl, site.specification.decline_legal env⟩
  | some value =>
      have hevidence := emitted.endpoint.resolveDisposition_some_evidence
        native.memory.clock (native.verify emitted) (emitted.binding? native.memory)
        native.memory.done (emitted.canOpen native.memory.store) message value hresolve
      have hvalue : value = env.get site.specification.binding := by
        rcases hevidence.2 with hopaque | hpublic
        · have hsnapshot : (native.frozen (site.sourceField fresh state)).bind
              (fun typed => typed.as? site.specification.secretTy) = some value := by
            simpa [ApplicationImage.State.verify, emitted, code] using hopaque.2
          exact hfrozen value hsnapshot
        · exact hdefault value hpublic
      refine ⟨Or.inr (congrArg some hvalue), ?_⟩
      have hcanOpen := emitted.endpoint.resolveDisposition_some_canOpen native.memory.clock
        (native.verify emitted) (emitted.binding? native.memory)
        native.memory.done (emitted.canOpen native.memory.store) message value hresolve
      change site.canOpen fresh state native.memory.store value = true at hcanOpen
      rw [site.canOpen_source fresh state representedStore native.memory.store env
        heligible hagrees hpublicStore value hvalue] at hcanOpen
      exact hcanOpen

end ConditionalPublicationSite

end Vegas

/-- info: 'Vegas.ConditionalPublicationSite.code_resolution_source_legal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.code_resolution_source_legal

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBindingDefault
import Vegas.Compile.ApplicationBindingTimeouts

/-! # Compiling source-authorized binding expiry

A public source fallback is emitted as typed expression code at the existing
binding address. Including a pending expiry packet after its deadline performs
the original source decision with that value. The theorem derives executable
read availability and readiness from an exact source-prefix checkpoint.

The sender is unrestricted and no private preparation is assumed. Packet
production and timely inclusion remain service obligations. The public default
also exposes its occurrence before conditional publication; this result is an
operational correspondence, not an information-flow or strategy theorem.
-/

noncomputable section

namespace Vegas.SourceDecisionSite.PublicFallback

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Emit the fallback at the original generated binding instruction. -/
def bindingTimeoutCode {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {who : P} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : PublicFallback site) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (deadline : Nat) : BindingCode P L :=
  { site.bindingCode fresh build (site.compiledField fresh build) with
    timeout := some ⟨deadline, fallback.compiled fresh build⟩ }

/-- Select the source-allocated binding address and its type. Other binding
instructions retain their metadata. Generated plans ensure unique addresses. -/
def selectBindingTimeout {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {who : P} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : PublicFallback site) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (deadline : Nat)
    (code : BindingCode P L) : Option (PublicFallbackCode L code.ty) :=
  if code.node = (site.compiledNode fresh build).val then
    if hty : code.ty = ty then
      some (cast (congrArg (PublicFallbackCode L) hty.symm)
        (⟨deadline, fallback.compiled fresh build⟩ : PublicFallbackCode L ty))
    else code.timeout
  else code.timeout

def installBindingTimeout {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {who : P} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : PublicFallback site) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (deadline : Nat)
    (image : ApplicationImage P L) : ApplicationImage P L :=
  image.withBindingTimeouts (fallback.selectBindingTimeout fresh build deadline)

theorem lookup_installBindingTimeout {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {who : P} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    {site : SourceDecisionSite who prog Δ name ty guard}
    (fallback : PublicFallback site) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (deadline : Nat)
    (image : ApplicationImage P L) (address : Nat)
    (hcode : image.lookup address = some (.bind
      (site.bindingCode fresh build (site.compiledField fresh build)))) :
    (fallback.installBindingTimeout fresh build deadline image).lookup address =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)) := by
  simp only [installBindingTimeout, ApplicationImage.lookup_withBindingTimeouts, hcode,
    Option.map_some, ApplicationInstruction.withBindingTimeouts]
  have hselect : fallback.selectBindingTimeout fresh build deadline
      (site.bindingCode fresh build (site.compiledField fresh build)) =
      some ⟨deadline, fallback.compiled fresh build⟩ := by
    unfold selectBindingTimeout
    rw [if_pos (by rfl)]
    simp only [dif_pos (show
      (site.bindingCode fresh build (site.compiledField fresh build)).ty = ty from rfl), cast_eq]
  rw [hselect]
  rfl

/-- Actual inclusion advances one original source decision and retains the
authentic expiry packet and receipt. No owner-authored substitute is constructed. -/
theorem expiry_include_source_coupling
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (image : ApplicationImage P L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (hoverdue : deadline < execution.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (id : MessageId P)
    (hlookup : execution.pool.lookup id = some ⟨id, .expireBinding address⟩) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    let included := image.application.includePending execution id
    ∃ next : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1,
      next.current.source = current.current.source.cons chosen ∧
        included.application.Refines next.current.graph.1 ∧
        included.receipts = execution.receipts ++ [(id, true)] ∧
        included.pool.ledger = execution.pool.ledger ++ [⟨id, .expireBinding address⟩] ∧
        included.pool.sent = execution.pool.sent ∧
        included.pool.inbox = execution.pool.inbox := by
  dsimp only
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let code := fallback.bindingTimeoutCode fresh build deadline
  let chosen := L.eval fallback.expr current.current.source.erasePubEnv
  have hready := binding_ready_at_source_prefix guard tail fresh build current
    execution.application.memory.done hrefines.memory.completed
  have hunbound : execution.application.memory.accepted code.sourceField = none :=
    hrefines.accepted_eq_none_of_not_done (site.compiledNode fresh build) hready.1.1
  obtain ⟨hvalue, next, hsource, hnext⟩ := fallback.defaultBind_source_coupling
    guard tail fresh build current execution.application hrefines
  have hincluded := image.include_expireBinding execution address code hcode id
    ⟨deadline, fallback.compiled fresh build⟩ rfl hunbound hready.2.1 hready.2.2
    hoverdue chosen hvalue hlookup
  refine ⟨next, hsource, ?_, hincluded.2⟩
  rw [hincluded.1]
  exact hnext

end Vegas.SourceDecisionSite.PublicFallback

/-- info: 'Vegas.SourceDecisionSite.PublicFallback.expiry_include_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.PublicFallback.expiry_include_source_coupling

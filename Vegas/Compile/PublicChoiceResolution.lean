/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicResolution
import Vegas.Compile.ApplicationChoiceTimeouts
import Vegas.Compile.PublicChoiceSourceCoupling
import Interaction.MessageApplicationPolicies

/-! # Compiling source-authorized public-choice expiry

An explicit public expression supplies the resolution value. It is compiled to
typed field reads and installed as optional code in the existing application
image. Expiry requests may come from any sender. Their
acceptance realizes the original adjacent source choice and reveal, using the
annotated value rather than asserting equality with the owner's original policy.
-/

noncomputable section

namespace Vegas.PublicResolutionChoice

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The source expression and deadline are emitted as ordinary typed code. -/
def timeout {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) (deadline : Nat) :
    PublicChoiceTimeout L site.ty :=
  ⟨deadline, resolution.compiled fresh build⟩

/-- The same generated endpoint, with an explicit public resolution annotation. -/
def timeoutCode {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) (deadline : Nat) :
    PublicChoiceCode P L :=
  { site.code fresh build with timeout := some (resolution.timeout fresh build deadline) }

/-- Select one existing publication address and type. Other instructions retain
their own timeout metadata. Address uniqueness is supplied by generated plans;
this pass does not invent another dispatcher or runtime.
-/
def select {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) (deadline : Nat)
    (code : PublicChoiceCode P L) : Option (PublicChoiceTimeout L code.guard.ty) :=
  if code.endpoint.publicationNode = (site.publicationNode fresh build).val then
    if hty : code.guard.ty = site.ty then
      some (cast (congrArg (PublicChoiceTimeout L) hty.symm)
        (resolution.timeout fresh build deadline))
    else code.timeout
  else code.timeout

/-- Install the source-authorized fallback at the selected publication address
and type. Generated plans supply address uniqueness. -/
def install {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) (deadline : Nat)
    (image : ApplicationImage P L) : ApplicationImage P L :=
  image.withChoiceTimeouts (resolution.select fresh build deadline)

/-- A loaded source-generated endpoint remains at its allocated address and
receives exactly its compiled resolution expression. -/
theorem lookup_install {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {site : PublicChoiceSite prog} (resolution : PublicResolutionChoice site)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) (deadline : Nat)
    (image : ApplicationImage P L) (address : Nat)
    (hcode : image.lookup address = some (.publicChoice (site.code fresh build))) :
    (resolution.install fresh build deadline image).lookup address =
      some (.publicChoice (resolution.timeoutCode fresh build deadline)) := by
  simp only [install, ApplicationImage.lookup_withChoiceTimeouts, hcode, Option.map_some,
    ApplicationInstruction.withChoiceTimeouts]
  have hselect : resolution.select fresh build deadline (site.code fresh build) =
      some (resolution.timeout fresh build deadline) := by
    unfold select
    rw [if_pos (by rfl)]
    simp only [dif_pos (show (site.code fresh build).guard.ty = site.ty from rfl), cast_eq]
  rw [hselect]
  rfl

/-- An actual expiry inclusion at a source-order checkpoint advances both source
nodes to the annotated legal value. Readiness and executable read availability
are derived from refinement; the message's sender is unrestricted. -/
theorem expiry_include_source_coupling
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (resolution : PublicResolutionChoice
      (PublicChoiceSite.atHead name publicName who guard tail))
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L)
    (execution included : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (hoverdue : deadline < execution.native.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.publicChoice
      (resolution.timeoutCode fresh build deadline)))
    (id : MessageId P)
    (hlookup : execution.native.pool.lookup id = some ⟨id, .expireChoice address⟩)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support) :
    let chosen := L.eval resolution.expr current.current.source.erasePubEnv
    included.native = image.application.includePending execution.native id ∧
      included.principalHistory = execution.principalHistory ∧
      included.environmentHistory = execution.environmentHistory ++
        [⟨State.environmentView image.application execution.native, .include id⟩] ∧
      included.nativeTrace = execution.nativeTrace ++ [.include id] ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen).cons chosen ∧
          included.native.application.Refines next.current.graph.1 := by
  dsimp only
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let code := resolution.timeoutCode fresh build deadline
  let chosen := L.eval resolution.expr current.current.source.erasePubEnv
  have hready := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    execution.native.application.memory.done hrefines.memory.completed
  have hvalue := resolution.compiled_evalStore?_eq_source fresh build
    current.current.graph.1.store execution.native.application.memory.store current.current.source
    current.current.agrees (fun ref href =>
      hrefines.memory.publicFields ref (resolution.compiled_reads_public fresh build ref href))
  obtain ⟨reads, hreads, heval⟩ := Option.map_eq_some_iff.mp hvalue
  have hvalid : (site.code fresh build).guard.validate
      execution.native.application.memory.store chosen = true := by
    change site.validator fresh build execution.native.application.memory.store chosen = true
    rw [site.validator_source_of_publiclyValidatable fresh build
      current.current.graph.1.store execution.native.application.memory.store current.current.source
      heligible current.current.agrees hrefines.memory.publicFields]
    exact resolution.legal current.current.source
  have hnative := image.include_expireChoice execution.native address code hcode id
    (resolution.timeout fresh build deadline) rfl hready hoverdue reads hreads
    (by
      change (site.code fresh build).guard.validate execution.native.application.memory.store
        ((resolution.compiled fresh build).eval reads) = true
      rw [heval]
      exact hvalid) hlookup
  simp only [MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hincluded
  subst included
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  obtain ⟨next, hsource, hgraph⟩ := PublicChoiceSite.source_successor guard tail fresh build
    current chosen (resolution.legal current.current.source)
  have hresolve : (site.code fresh build).endpoint.resolve?
      execution.native.application.memory.done
      ((site.code fresh build).guard.validate execution.native.application.memory.store)
      ⟨(who, 0), chosen⟩ = some chosen := by
    apply (PublicChoice.resolve_iff _ _ _ _ _).mpr
    exact ⟨hready, rfl, hvalid, rfl⟩
  have hnextRefines := site.resolution_refines fresh build execution.native.application
    current.current.graph.1 hrefines heligible ⟨(who, 0), chosen⟩ chosen hresolve
  refine ⟨next, hsource, ?_⟩
  rw [hnative.1]
  change (execution.native.application.publish (site.code fresh build)
    ((resolution.compiled fresh build).eval reads)).Refines next.current.graph.1
  rw [heval, hgraph]
  exact hnextRefines

end Vegas.PublicResolutionChoice

/-- info: 'Vegas.PublicResolutionChoice.expiry_include_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicResolutionChoice.expiry_include_source_coupling

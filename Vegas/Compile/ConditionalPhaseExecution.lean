/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImageController
import Vegas.Compile.ConditionalSourceCoupling
import Vegas.Compile.ApplicationImageReadout
import Interaction.MessagePoolFreshness

/-! # Exact execution of a generated conditional-publication phase

One owner invocation submits the source-profile choice and one environment
invocation includes that fresh envelope.  The theorem retains the complete
shared policy execution for opaque bindings and public defaults. Its snapshot
premise applies only to opaque openings. Default publication uses the accepted
public value; decline needs no recoverable commitment value.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Exact two-invocation source law for a generated conditional publication or
decline under either binding disposition. The environment premise specifies
only the local inclusion action, without a general progress guarantee. -/
theorem conditional_phase_source_law
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L)
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (heligible : (atHead name publicName who guard tail spec).PubliclyValidatable fresh build)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : ((atHead name publicName who guard tail spec).code fresh build
      sourceSlot deadline).binding? execution.native.application.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (hcode : image.lookup
        ((atHead name publicName who guard tail spec).code fresh build
          sourceSlot deadline).endpoint.publicationNode = some (.conditional
      ((atHead name publicName who guard tail spec).code fresh build sourceSlot deadline)))
    (reads : ReadEnv L (eventGuardOf build who guard).choiceReads)
    (hpolicy : ∀ history,
      players who history
          (MessageApplication.State.observe image.application execution.native who) =
        (atHead name publicName who guard tail spec).imagePolicy fresh build
          sourceSlot deadline image
          (image.ownerReadout? who (eventGuardOf build who guard).choiceReads)
          sourcePolicy (fun _ _ => false) history
            (MessageApplication.State.observe image.application execution.native who))
    (henvironment : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit (.conditional
          ((atHead name publicName who guard tail spec).code fresh build sourceSlot
            deadline).endpoint.publicationNode
          ((atHead name publicName who guard tail spec).sourceRequestPayload fresh build
            sourceSlot deadline disposition (spec.encoding chosen.1))))).support,
      environment submitted.environmentHistory
          (MessageApplication.State.environmentView image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)))
    (hlookupFresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hcache : ChoiceEncoding.cachedValue image.application
      (((atHead name publicName who guard tail spec).choiceEncodingFor fresh build
        sourceSlot deadline disposition
        (ApplicationImage.conditionalTransport spec.secretTy)).submission
          image.application)
      (execution.principalHistory who) = none)
    (hreadout : image.ownerReadout? who (eventGuardOf build who guard).choiceReads
      (execution.principalHistory who)
      (MessageApplication.State.observe image.application execution.native who) = some reads)
    (hreads : ReadEnv.ofStore? current.current.graph.1.store
      (eventGuardOf build who guard).choiceReads = some reads)
    (hfrozen : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ handle value, disposition = .opaque handle → spec.encoding chosen.1 = some value →
        (execution.native.application.frozen (build.fieldOf spec.binding)).bind
          (fun typed => typed.as? spec.secretTy) = some value) :
    let site := atHead name publicName who guard tail spec
    let code := site.code fresh build sourceSlot deadline
    let id := (who, execution.native.pool.nextSerial who)
    (image.application.runPolicies players environment [.player who, .environment] execution =
      (sourcePolicy ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
        (image.application.playerStep who execution
          (.submit (.conditional code.endpoint.publicationNode
            (site.sourceRequestPayload fresh build sourceSlot deadline disposition
              (spec.encoding chosen.1))))).bind
            fun submitted => image.application.environmentPolicyStep submitted (.include id)) ∧
    ∀ chosen ∈ (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit (.conditional code.endpoint.publicationNode
          (site.sourceRequestPayload fresh build sourceSlot deadline disposition
            (spec.encoding chosen.1))))).support,
      ∀ included ∈
        (image.application.environmentPolicyStep submitted (.include id)).support,
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
          included.native.application.Refines next.current.graph.1 := by
  dsimp only
  let site := atHead name publicName who guard tail spec
  let code := site.code fresh build sourceSlot deadline
  let id := (who, execution.native.pool.nextSerial who)
  change code.binding? execution.native.application.memory = some disposition at hbinding
  have hreadyDisposition : code.endpoint.readyDisposition
      (Value := L.Val spec.secretTy)
      (some disposition) execution.native.application.memory.done = true := by
    have hready := readyDisposition_at_source_prefix guard tail spec fresh build
      sourceSlot deadline current execution.native.application hrefines
      disposition hbinding hcanonical
    change code.endpoint.readyDisposition (code.binding? execution.native.application.memory)
      execution.native.application.memory.done = true at hready
    simpa only [hbinding] using hready
  have hresolved : execution.native.application.memory.done code.endpoint.publicationNode =
      false := by
    have hready := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
      execution.native.application.memory.done hrefines.memory.completed
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hready
    exact hready.1.2
  have hfirst := site.imagePolicy_first_submission_source_law fresh build sourceSlot
    deadline image disposition
    (image.ownerReadout? who (eventGuardOf build who guard).choiceReads)
    sourcePolicy (fun _ _ => false) (execution.principalHistory who)
    (MessageApplication.State.observe image.application execution.native who)
    current.current.graph.1.store current.current.source reads hbinding hresolved hcache
    hreadyDisposition hreadout (BuildState.Agrees.view current.current.agrees who) hreads
  simp only [choiceEncodingFor_encode] at hfirst
  constructor
  · simp only [MessageApplication.runPolicies, MessageApplication.invoke]
    rw [hpolicy, hfirst, FinDist.bind_map, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro chosen hchosen
    apply FinDist.bind_congr
    intro submitted hsubmitted
    rw [henvironment chosen hchosen submitted hsubmitted]
    simp only [FinDist.pure_bind]
    exact FinDist.bind_pure _
  · intro chosen hchosen submitted hsubmitted included hincluded
    have hnative : submitted.native ∈
          ((image.application.playerStep who execution
            (.submit (.conditional code.endpoint.publicationNode
              (site.sourceRequestPayload fresh build sourceSlot deadline disposition
                (spec.encoding chosen.1))))).map
              MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨submitted, hsubmitted, rfl⟩
    rw [image.application.playerStep_native] at hnative
    simp only [PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative
    have hlookup : submitted.native.pool.lookup id = some
        ⟨id, .conditional code.endpoint.publicationNode
          (site.sourceRequestPayload fresh build sourceSlot deadline disposition
            (spec.encoding chosen.1))⟩ := by
      rw [hnative]
      exact execution.native.pool.lookup_submit_fresh who _ hlookupFresh
    have happlication : submitted.native.application = execution.native.application := by
      simpa using congrArg MessageInterface.State.application hnative
    have hincludedNative : included.native =
        image.application.includePending submitted.native id := by
      simp only [MessageApplication.environmentPolicyStep,
        EnvironmentPolicyCommand.toAction, MessageApplication.advance,
        MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hincluded
      exact congrArg MessageInterface.PolicyExecution.native hincluded
    obtain ⟨next, hsource, hrefinesNext⟩ := include_source_coupling guard tail spec fresh
      build sourceSlot deadline current image submitted.native (happlication.symm ▸ hrefines)
      heligible disposition (happlication.symm ▸ hbinding) hcanonical
      code.endpoint.publicationNode
      (execution.native.pool.nextSerial who) hcode chosen.1 hlookup chosen.2 (by
        intro handle value hopaque hvalue
        rw [happlication]
        exact hfrozen chosen hchosen handle value hopaque hvalue)
    exact ⟨next, hsource, hincludedNative.symm ▸ hrefinesNext⟩

end Vegas.ConditionalPublicationSite

/-- info: 'Vegas.ConditionalPublicationSite.conditional_phase_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.conditional_phase_source_law

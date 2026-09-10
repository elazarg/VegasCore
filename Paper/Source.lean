/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.SourceCorrelated
import Vegas.Scheduled.SourceCorrespondence
import Vegas.Core.AccountingIntegrity
import Vegas.Compile.ApplicationPlanOutcome
import Vegas.Compile.ApplicationForwardLaw
import Vegas.Compile.ApplicationTimeoutForwardLaw
import Vegas.Compile.PublicChoiceResolution
import Vegas.Compile.BindingTimeoutCompilation
import Vegas.Compile.ApplicationWithholding
import Vegas.Compile.ConditionalExpirationSourceCoupling
import Vegas.Compile.ConditionalPhaseExecution

/-! # Paper-facing independent-source correspondence claims -/

noncomputable section
namespace Vegas.Paper.Source
open GameTheory GameTheory.Math.Probability GameTheory.Protocol
open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

theorem committed_binding_accounted (source : WFProgram Player L) (name : VarId)
    (hname : name ∈ CommittedVars source.core.prog) :
    name ∈ RevealedSources source.core.prog ∨
      name ∈ source.accounted.dispositions :=
  source.committed_source_resolved name hname

theorem initial_binding_accounted (source : WFProgram Player L) (name : VarId)
    (hname : name ∈ SealedVars source.core.Γ) :
    name ∈ RevealedSources source.core.prog ∨
      name ∈ source.accounted.dispositions :=
  source.initial_sealed_source_resolved name hname

theorem binding_resolutions_nodup (source : WFProgram Player L) :
    source.accounted.resolvedSources.Nodup :=
  source.resolutions_nodup

/-- Public-message compilation preserves possible completed public outcomes;
the source run and runtime initialization are both explicit. -/
theorem public_application_outcome (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode Player L) →
      Option (PublicFallbackCode L code.guard.ty))
    (actions : List ((plan.image deadlineOf).withChoiceTimeouts select).application.Action)
    (next : ((plan.image deadlineOf).withChoiceTimeouts select).application.State)
    (hnext : next ∈ (((plan.image deadlineOf).withChoiceTimeouts select).application.run actions
      (Interaction.MessageApplication.State.initial
        ((plan.image deadlineOf).withChoiceTimeouts select).application
        (ApplicationImage.State.initial
          (ApplicationImage.Memory.initial (ToEventGraph.compile source.core).graph)))).support)
    (hfinished : next.application.memory.finished
      (ToEventGraph.compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
      (ToEventGraph.compile source.core).readPublicTerminal? next.application.memory =
        some terminalEnv.erasePubEnv :=
  ApplicationPlan.run_source_public_outcome source plan deadlineOf select actions next hnext
    hfinished

/-- The same public-outcome safety statement quantifies over arbitrary
randomized policies, without asserting a source-policy correspondence. -/
theorem public_application_policy_outcome (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode Player L) →
      Option (PublicFallbackCode L code.guard.ty))
    (players : Player →
      ((plan.image deadlineOf).withChoiceTimeouts select).application.PlayerPolicy)
    (environment :
      ((plan.image deadlineOf).withChoiceTimeouts select).application.EnvironmentPolicy)
    (schedule : List (@Interaction.MessageApplication.Invocation Player))
    (next : ((plan.image deadlineOf).withChoiceTimeouts select).application.PolicyExecution)
    (hnext : next ∈
      (((plan.image deadlineOf).withChoiceTimeouts select).application.runPolicies
      players environment schedule
      (Interaction.MessageApplication.PolicyExecution.initial
        ((plan.image deadlineOf).withChoiceTimeouts select).application
        (Interaction.MessageApplication.State.initial
          ((plan.image deadlineOf).withChoiceTimeouts select).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial (ToEventGraph.compile source.core).graph))))).support)
    (hfinished : next.native.application.memory.finished
      (ToEventGraph.compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
      (ToEventGraph.compile source.core).readPublicTerminal? next.native.application.memory =
        some terminalEnv.erasePubEnv :=
  ApplicationPlan.runPolicies_source_public_outcome source plan deadlineOf select players
    environment schedule next hnext hfinished

/-- For an eligible application plan, lifting one source profile and running
the emitted serial reference service gives the source law of joint completion
and public terminal output, including with optional binding and public-choice
fallbacks. -/
theorem public_application_reference_law (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode Player L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode Player L) → Option (PublicFallbackCode L code.guard.ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    (((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).application.runPolicies
      (plan.liftProfile deadlineOf profile) (plan.image deadlineOf).serialService
      (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)).map
        (fun out =>
          (out.native.application.memory.finished
              (ToEventGraph.compile source.core).graph.nodeCount,
            (ToEventGraph.compile source.core).readPublicTerminal?
              out.native.application.memory))) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (ToEventGraph.compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog
            source.core.fresh
            (ToEventGraph.BuildState.fromInitial
              (ToEventGraph.initialState source.core.Γ source.core.env
                source.core.wctx))).symm) terminal).erasePubEnv) :=
  plan.timeout_service_source_public_law source deadlineOf binding choice profile hinitial horigins

/-- Source-ordered admission with optional binding and public-choice fallbacks
retains the generated reference service's exact joint completion and public-output
law. It asserts neither progress under other services nor deviation simulation. -/
theorem public_application_ordered_reference_law (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode Player L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode Player L) → Option (PublicFallbackCode L code.guard.ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    (((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).orderedApplication.runPolicies
      (plan.liftProfile deadlineOf profile) (plan.image deadlineOf).serialService
      (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)).map
        (fun out =>
          (out.native.application.memory.finished
              (ToEventGraph.compile source.core).graph.nodeCount,
            (ToEventGraph.compile source.core).readPublicTerminal?
              out.native.application.memory))) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (ToEventGraph.compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog
            source.core.fresh
            (ToEventGraph.BuildState.fromInitial
              (ToEventGraph.initialState source.core.Γ source.core.env
                source.core.wctx))).symm) terminal).erasePubEnv) :=
  plan.ordered_timeout_service_source_public_law source deadlineOf binding choice
    profile hinitial horigins

/-- A missing authenticated submission cannot be supplied by scheduling.
The generated code's submission requirement is an inspectable static premise. -/
theorem public_application_withholding (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat) (node : Nat) (who : Player)
    (required : (plan.image deadlineOf).RequiresSubmission node who)
    (hnode : node < (ToEventGraph.compile source.core).graph.nodeCount)
    (profile : SourceBehavioralProfile source.core.prog)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Interaction.MessageApplication.Invocation Player)) :
    (((plan.image deadlineOf).application.runPolicies
      (Profile.update
        (sig := Interaction.MessageApplication.policySignature Player
          (plan.image deadlineOf).application)
        (plan.liftProfile deadlineOf profile) who (fun _ _ => FinDist.pure .wait))
      environment schedule (plan.initialExecution deadlineOf)).map
        (fun out => out.native.application.memory.finished
          (ToEventGraph.compile source.core).graph.nodeCount)) = FinDist.pure false :=
  plan.withholding_finished_law source deadlineOf node who required hnode
    (plan.liftProfile deadlineOf profile) environment schedule

/-- At a ready generated conditional endpoint, one owner invocation followed
by the assumed inclusion action has exactly the supplied randomized source
law. Every supported inclusion advances the adjacent source pair and native
refinement under either accepted binding disposition. -/
theorem public_application_conditional_phase
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (sourceSlot deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L)
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (players : Player → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (heligible :
      (ConditionalPublicationSite.atHead name publicName who guard tail spec).PubliclyValidatable
        fresh build)
    (disposition : Interaction.BindingDisposition (Interaction.CommitmentHandle Player Nat)
      (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? execution.native.application.memory =
        some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (hcode : image.lookup
        ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
          fresh build sourceSlot deadline).endpoint.publicationNode = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (reads : ReadEnv L (ToEventGraph.eventGuardOf build who guard).choiceReads)
    (hpolicy : ∀ history,
      players who history
          (Interaction.MessageApplication.State.observe image.application execution.native who) =
        (ConditionalPublicationSite.atHead name publicName who guard tail spec).imagePolicy
          fresh build sourceSlot deadline image
          (image.ownerReadout? who (ToEventGraph.eventGuardOf build who guard).choiceReads)
          sourcePolicy (fun _ _ => false) history
            (Interaction.MessageApplication.State.observe
              image.application execution.native who))
    (henvironment : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit (.conditional
          ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
            fresh build sourceSlot deadline).endpoint.publicationNode
          (ConditionalPublicationSite.sourceRequestPayload
            (ConditionalPublicationSite.atHead name publicName who guard tail spec)
            fresh build sourceSlot deadline disposition (spec.encoding chosen.1))))).support,
      environment submitted.environmentHistory
          (Interaction.MessageApplication.State.environmentView
            image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)))
    (hlookupFresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hcache : Interaction.MessageApplication.ChoiceEncoding.cachedValue image.application
      ((ConditionalPublicationSite.choiceEncodingFor
        (ConditionalPublicationSite.atHead name publicName who guard tail spec)
        fresh build sourceSlot deadline disposition
        (ApplicationImage.conditionalTransport spec.secretTy)).submission image.application)
      (execution.principalHistory who) = none)
    (hreadout : image.ownerReadout? who
        (ToEventGraph.eventGuardOf build who guard).choiceReads
      (execution.principalHistory who)
      (Interaction.MessageApplication.State.observe image.application execution.native who) =
        some reads)
    (hreads : ReadEnv.ofStore? current.current.graph.1.store
      (ToEventGraph.eventGuardOf build who guard).choiceReads = some reads)
    (hfrozen : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ handle value, disposition = .opaque handle → spec.encoding chosen.1 = some value →
        (execution.native.application.frozen (build.fieldOf spec.binding)).bind
          (fun typed => typed.as? spec.secretTy) = some value) :
    let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
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
      ∃ next : ToEventGraph.CoupledAt
          (ToEventGraph.compileCore
            (.commit name who guard (.reveal publicName who name .here tail)) fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
          included.native.application.Refines next.current.graph.1 := by
  have result := ConditionalPublicationSite.conditional_phase_source_law guard tail spec fresh build
    sourceSlot deadline current image sourcePolicy players environment execution hrefines
    heligible disposition hbinding hcanonical hcode reads hpolicy henvironment hlookupFresh
    hcache hreadout hreads hfrozen
  exact ⟨result.1, result.2.1⟩

/-- Inclusion of a legal generated conditional request advances the exact
adjacent source choice/reveal pair. Opaque dispositions require the canonical
handle and matching frozen opening; public defaults require neither premise. -/
theorem public_application_conditional_continuation
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (sourceSlot deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (heligible :
      (ConditionalPublicationSite.atHead name publicName who guard tail spec).PubliclyValidatable
        fresh build)
    (disposition : Interaction.BindingDisposition (Interaction.CommitmentHandle Player Nat)
      (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? execution.application.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (address serial : Nat)
    (hcode : image.lookup address = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (chosen : L.Val ty)
    (hlookup : execution.pool.lookup (who, serial) = some ⟨(who, serial), .conditional address
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).sourceRequestPayload
        fresh build sourceSlot deadline disposition (spec.encoding chosen))⟩)
    (hlegal : evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true)
    (hfrozen : ∀ handle value, disposition = .opaque handle →
      spec.encoding chosen = some value →
      (execution.application.frozen (build.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value) :
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons chosen).cons chosen ∧
        (image.application.includePending execution (who, serial)).application.Refines
          next.current.graph.1 :=
  ConditionalPublicationSite.include_source_coupling guard tail spec fresh build sourceSlot
    deadline current image execution hrefines heligible disposition hbinding hcanonical address
    serial hcode chosen hlookup hlegal hfrozen

/-- An included overdue expiry at a generated conditional endpoint implements
the existing source decline, with no requirement that its sender be the owner. -/
theorem public_application_conditional_expiry
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (sourceSlot deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L)
    (execution included : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (disposition : Interaction.BindingDisposition (Interaction.CommitmentHandle Player Nat)
      (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? execution.native.application.memory =
        some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (hoverdue : deadline < execution.native.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (id : Interaction.MessageId Player)
    (hlookup : execution.native.pool.lookup id = some ⟨id, .conditional address .expire⟩)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support) :
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons (spec.encoding.symm none)).cons
        (spec.encoding.symm none) ∧
        included.native.application.Refines next.current.graph.1 :=
  (ConditionalPublicationSite.expiry_include_source_coupling guard tail spec fresh build
    sourceSlot deadline current image execution included hrefines disposition hbinding hcanonical
    hoverdue
    address hcode id hlookup hincluded).2.2.2

/-- An included public-choice expiry follows an explicitly annotated legal
public source expression, without supplying a command by the endpoint owner. -/
theorem public_application_choice_expiry
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L)
    (execution included : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (hoverdue : deadline < execution.native.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
        fallback fresh build deadline)))
    (id : Interaction.MessageId Player)
    (hlookup : execution.native.pool.lookup id = some ⟨id, .expireChoice address⟩)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons chosen).cons chosen ∧
        included.native.application.Refines next.current.graph.1 :=
  (PublicChoiceSite.expiry_include_source_coupling guard tail fallback fresh build deadline
    current image execution included hrefines heligible hoverdue address hcode id hlookup
    hincluded).2.2.2.2

/-- Actual inclusion of source-authorized binding expiry advances the original
source decision to the public fallback without requiring private preparation. -/
theorem public_application_binding_expiry
    {Γ : VCtx Player L} {name : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : ToEventGraph.BuildState Player L Γ) (deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard tail) fresh build).graph build)
    (image : ApplicationImage Player L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (hoverdue : deadline < execution.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (id : Interaction.MessageId Player)
    (hlookup : execution.pool.lookup id = some ⟨id, .expireBinding address⟩) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1,
      next.current.source = current.current.source.cons chosen ∧
        (image.application.includePending execution id).application.Refines
          next.current.graph.1 := by
  obtain ⟨next, hsource, hnext, _⟩ := fallback.expiry_include_source_coupling guard tail
    fresh build deadline current image execution hrefines hoverdue address hcode id hlookup
  exact ⟨next, hsource, hnext⟩

/-- info: 'Vegas.Paper.Source.public_application_binding_expiry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_binding_expiry

variable [Fintype Player]

theorem native_honest_law (source : WFProgram Player L)
    (profile : SourceBehavioralProfile source.core.prog) :
    (source.boundedGame.behavioralForm.play
      (source.sourceOutcomeSimulation.compileProfile profile)).map
        source.sourceOutcomeSimulation.decodeOutcome =
      (sourceGameForm source.core.prog source.core.env).play profile :=
  source.sourceOutcomeSimulation.honest_law profile

theorem native_unilateral_law (source : WFProgram Player L)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : source.boundedGame.behavioralForm.sig.Strategy who) :
    (source.boundedGame.behavioralForm.play
      (Profile.update (source.sourceOutcomeSimulation.compileProfile profile)
        who replacement)).map source.sourceOutcomeSimulation.decodeOutcome =
      (sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who
          (source.sourceOutcomeSimulation.backtranslateStrategy who replacement)) :=
  source.sourceOutcomeSimulation.deviation_law profile who replacement trivial

theorem native_nash_iff (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) :
    IsNash
      ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).behavioral.form
      (euPreference ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).utility)
      (source.sourceOutcomeSimulation.compileProfile profile) ↔
      IsNash (sourceGameForm source.core.prog source.core.env)
        (euPreference valuation) profile :=
  source.source_native_nash_iff valuation profile

theorem native_approximate_nash_iff (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ) :
    IsεNash
      ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).behavioral.form
      ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).utility ε
      (source.sourceOutcomeSimulation.compileProfile profile) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env) valuation ε profile :=
  source.source_native_approximate_nash_iff valuation profile ε

theorem native_correlated_preservation (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (law : FinDist (Profile (sourceGameSignature source.core.prog)))
    (hsource : IsCorrelatedEq (sourceGameForm source.core.prog source.core.env)
      (euPreference valuation) law) :
    IsCorrelatedEq source.boundedGame.behavioralForm
      (euPreference fun outcome who =>
        valuation (source.sourceOutcomeSimulation.decodeOutcome outcome) who)
      (source.sourceOutcomeSimulation.compileLaw law) :=
  source.source_native_correlatedEq_of valuation law hsource

theorem native_coarse_correlated_iff (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (law : FinDist (Profile (sourceGameSignature source.core.prog))) :
    IsCoarseCorrelatedEq source.boundedGame.behavioralForm
      (euPreference fun outcome who =>
        valuation (source.sourceOutcomeSimulation.decodeOutcome outcome) who)
      (source.sourceOutcomeSimulation.compileLaw law) ↔
    IsCoarseCorrelatedEq (sourceGameForm source.core.prog source.core.env)
      (euPreference valuation) law :=
  source.source_native_coarseCorrelatedEq_iff valuation law

theorem scheduled_honest_law (source : WFProgram Player L)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) :
    ((Machine.compile source).serializedInformation.runBehavioral
      ((Machine.compile source).compileSerializedBehavioralProfile scheduler
        (fun who => ToEventGraph.compileSourceBehavioral source.core source.legal
          who (profile who))) (Machine.compile source).graph.nodeCount).map
      (fun history => ToEventGraph.observeSourceOutcome source.core source.legal
        history.state.base) =
      denoteSource source.core.prog profile source.core.env :=
  source.source_serialized_honest_law scheduler profile

theorem scheduled_deviation_mixture (source : WFProgram Player L)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : (Machine.compile source).serializedInformation.BehavioralPolicy
      (.player who)) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy source.core.prog who),
      ((Machine.compile source).serializedInformation.runBehavioral
        (Function.update
          ((Machine.compile source).compileSerializedBehavioralProfile scheduler
            (fun player => ToEventGraph.compileSourceBehavioral source.core source.legal
              player (profile player))) (.player who) replacement)
        (Machine.compile source).graph.nodeCount).map
          (fun history => ToEventGraph.observeSourceOutcome source.core source.legal
            history.state.base) =
        alternatives.bind fun alternative =>
          denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog)
              profile who alternative) source.core.env :=
  source.source_serialized_deviation_law scheduler profile who replacement

theorem scheduled_request_honest_law (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) :
    ((source.serializedRequestGame interface schedulerUtility).form.play
      (source.compileSourceSerializedRequestProfile interface schedulerUtility
        scheduler profile)).map
        (fun state => ToEventGraph.observeSourceOutcome source.core source.legal
          state.1.state.base) =
      denoteSource source.core.prog profile source.core.env :=
  source.source_serialized_request_honest_law interface schedulerUtility scheduler profile

theorem scheduled_request_deviation_mixture (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy source.core.prog who),
      ((source.serializedRequestGame interface schedulerUtility).form.play
        (Profile.update (source.compileSourceSerializedRequestProfile interface schedulerUtility
          scheduler profile) (.player who) replacement)).map
          (fun state => ToEventGraph.observeSourceOutcome source.core source.legal
            state.1.state.base) =
        alternatives.bind fun alternative => denoteSource source.core.prog
          (Profile.update (sig := sourceGameSignature source.core.prog)
            profile who alternative) source.core.env :=
  source.source_serialized_request_deviation_law interface schedulerUtility scheduler
    profile who replacement

theorem scheduled_request_guarantee (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (value : VEnv L (sourceTerminalCtx source.core.prog) → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : SourceBehavioralPolicy source.core.prog who,
      bound ≤ (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
        source.core.env).expect value)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    bound ≤ ((source.serializedRequestGame interface schedulerUtility).form.play
      (Profile.update (source.compileSourceSerializedRequestProfile interface schedulerUtility
        scheduler profile) (.player who) replacement)).expect
          (fun state => value (ToEventGraph.observeSourceOutcome source.core source.legal
            state.1.state.base)) :=
  source.source_serialized_request_guarantee interface schedulerUtility scheduler profile who
    value bound hbound replacement

theorem scheduled_request_nash_iff (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) :
    Participant.IsPlayerNash
      (source.sourceSerializedRequestGame interface schedulerUtility valuation)
      (source.compileSourceSerializedRequestProfile interface schedulerUtility
        scheduler profile) ↔
      IsNash (sourceGameForm source.core.prog source.core.env)
        (euPreference valuation) profile :=
  source.source_serialized_request_nash_iff interface schedulerUtility valuation
    scheduler profile

theorem scheduled_request_approximate_nash_iff (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ) :
    (∀ who replacement,
      expectedUtility (source.sourceSerializedRequestGame interface schedulerUtility
        valuation).utility (.player who)
        ((source.sourceSerializedRequestGame interface schedulerUtility valuation).form.play
          (Profile.update (source.compileSourceSerializedRequestProfile interface
            schedulerUtility scheduler profile) (.player who) replacement)) ≤
      expectedUtility (source.sourceSerializedRequestGame interface schedulerUtility
        valuation).utility (.player who)
        ((source.sourceSerializedRequestGame interface schedulerUtility valuation).form.play
          (source.compileSourceSerializedRequestProfile interface schedulerUtility
            scheduler profile)) + ε) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env) valuation ε profile :=
  source.source_serialized_request_approximate_nash_iff interface schedulerUtility valuation
    scheduler profile ε

/-- info: 'Vegas.Paper.Source.native_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_honest_law
/-- info: 'Vegas.Paper.Source.native_unilateral_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_unilateral_law
/-- info: 'Vegas.Paper.Source.native_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_nash_iff
/-- info: 'Vegas.Paper.Source.native_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_approximate_nash_iff
/-- info: 'Vegas.Paper.Source.native_correlated_preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_correlated_preservation
/-- info: 'Vegas.Paper.Source.native_coarse_correlated_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_coarse_correlated_iff

/-- info: 'Vegas.Paper.Source.committed_binding_accounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.committed_binding_accounted
/-- info: 'Vegas.Paper.Source.initial_binding_accounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.initial_binding_accounted
/-- info: 'Vegas.Paper.Source.binding_resolutions_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.binding_resolutions_nodup

/-- info: 'Vegas.Paper.Source.scheduled_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_honest_law
/-- info: 'Vegas.Paper.Source.scheduled_deviation_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_deviation_mixture
/-- info: 'Vegas.Paper.Source.scheduled_request_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_honest_law
/-- info: 'Vegas.Paper.Source.scheduled_request_deviation_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_deviation_mixture
/-- info: 'Vegas.Paper.Source.scheduled_request_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_guarantee
/-- info: 'Vegas.Paper.Source.scheduled_request_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_nash_iff
/-- info: 'Vegas.Paper.Source.scheduled_request_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_approximate_nash_iff

/-- info: 'Vegas.Paper.Source.public_application_outcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_outcome

/-- info: 'Vegas.Paper.Source.public_application_policy_outcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_policy_outcome

/-- info: 'Vegas.Paper.Source.public_application_reference_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_reference_law

/-- info: 'Vegas.Paper.Source.public_application_ordered_reference_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_ordered_reference_law

/-- info: 'Vegas.Paper.Source.public_application_withholding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_withholding

/-- info: 'Vegas.Paper.Source.public_application_conditional_phase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_conditional_phase

/-- info: 'Vegas.Paper.Source.public_application_conditional_continuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_conditional_continuation

/-- info: 'Vegas.Paper.Source.public_application_conditional_expiry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_conditional_expiry

/-- info: 'Vegas.Paper.Source.public_application_choice_expiry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_choice_expiry

end Vegas.Paper.Source

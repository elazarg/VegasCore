/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedConditionalBlockPrivacy
import Vegas.Compile.WindowedPublicAction
import Vegas.Compile.WindowedSourcePrivacy
import VegasTests.WindowedSourceCoverage
import VegasTests.GeneratedApplicationSourceLaw
import VegasTests.ApplicationBindingOrigins

/-! # Conditional publication in the checked windowed application -/

noncomputable section

namespace VegasTests.WindowedConditional

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage

def unchangedPlayers (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    TestPlayer → runtime.application.PlayerPolicy :=
  applicationPlan.windowedPlayers profile (fun _ => 10) bindingSelector choiceSelector
    (fun _ => 10) 1 replacement

private def afterInitialBindingPlan :=
  match applicationPlan with
  | .binding _ next => next

private def afterMarkerPlan :=
  match afterInitialBindingPlan with
  | .publicChoice _ next => next
  | .conditionalCopy _ _ next => next

private def firstConditionalPlan :=
  match afterMarkerPlan with
  | .sample next => next

private def afterFirstConditionalPlan :=
  match firstConditionalPlan with
  | .conditional _ next => next

private def secondConditionalPlan :=
  match afterFirstConditionalPlan with
  | .publicChoice _ next => next

/-- The checked plan's first conditional is the accounting-discharge
constructor of the shared head interface. -/
theorem checked_discharge_head :
    ApplicationPlan.ConditionalHead DisclosureAccounting.persistentFirstSpec
      firstConditionalPlan := by
  unfold firstConditionalPlan afterMarkerPlan afterInitialBindingPlan applicationPlan
  exact .discharge _ _

/-- The checked plan's later repeated disclosure is the copy constructor of
the same shared head interface. -/
theorem checked_copy_head :
    ApplicationPlan.ConditionalHead secondSpecification secondConditionalPlan := by
  unfold secondConditionalPlan afterFirstConditionalPlan firstConditionalPlan
    afterMarkerPlan afterInitialBindingPlan applicationPlan
  exact .copy _ _

/-- At either kind of conditional head in the checked persistent-disclosure
plan, every supported ordinary polling outcome contains the canonical packet
for an actual source draw. The accepted disposition, including its canonical
opaque handle when applicable, is derived from the checkpoint. -/
theorem checked_conditional_ordinary_packet
    {Γ : VCtx TestPlayer simpleExpr} {pending : Finset VarId}
    {name publicName : VarId} {ty : simpleExpr.Ty}
    {guard : simpleExpr.Expr
      ((name, ty) :: eraseVCtx (viewVCtx (0 : TestPlayer) Γ)) simpleExpr.bool}
    {tail : VegasCore TestPlayer simpleExpr
      ((publicName, .pub ty) :: (name, .sealed 0 ty) :: Γ)}
    {spec : ConditionalOpening guard}
    {accounted : CommitmentAccounting pending
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {fresh : FreshBindings (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {state : BuildState TestPlayer simpleExpr Γ}
    {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {current : CoupledAt
      (compileCore (.commit name 0 guard (.reveal publicName 0 name .here tail))
        fresh state).graph state}
    (rootProfile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (blockIndex : Nat)
    (execution : runtime.application.PolicyExecution)
    (head : ApplicationPlan.ConditionalHead spec plan)
    (checkpoint : ApplicationPlan.WindowedCheckpoint applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 1 replacement
      blockIndex plan profile current execution)
    (polled : runtime.application.PolicyExecution)
    (hpolled : polled ∈ (runtime.application.runPolicies
      (unchangedPlayers rootProfile replacement) (runtime.blockEnvironment [0, 1])
      ([0, 1].flatMap fun actor => [Invocation.player actor, .player actor])
      execution).support) :
    let site := ConditionalPublicationSite.atHead name publicName 0 guard tail spec
    ∃ disposition : BindingDisposition (CommitmentHandle TestPlayer Nat)
        (simpleExpr.Val spec.secretTy),
      ∃ chosen ∈ (profile 0 site.choice.decision
          ((current.current.source.toView 0).eraseEnv)).support,
        polled.native.pool.nextSerial 0 = execution.native.pool.nextSerial 0 + 1 ∧
        polled.native.pool.lookup (0, execution.native.pool.nextSerial 0) =
          some ⟨(0, execution.native.pool.nextSerial 0),
            .conditional (site.choice.publicationNode fresh state)
              (site.sourceRequestPayload fresh state (site.sourceField fresh state)
                (10 : Nat) disposition (spec.encoding chosen.1))⟩ := by
  intro site
  obtain ⟨disposition, hbinding, _⟩ := checkpoint.conditional_binding_disposition head
    ApplicationBindingOrigins.persistent_image_has_binding_origins
  have hpolled' : polled ∈ ((applicationPlan.windowed (fun _ => 10) bindingSelector
      choiceSelector (fun _ => 10)).application.runPolicies
      (applicationPlan.windowedPlayers rootProfile (fun _ => 10) bindingSelector
        choiceSelector (fun _ => 10) 1 replacement)
      ((applicationPlan.windowed (fun _ => 10) bindingSelector choiceSelector
        (fun _ => 10)).blockEnvironment [0, 1])
      ([0, 1].flatMap fun actor => [Invocation.player actor, .player actor])
      execution).support := by
    simpa only [WindowedSourceCoverage.runtime, unchangedPlayers] using hpolled
  refine ⟨disposition, ?_⟩
  exact checkpoint.conditional_ordinary_submission head
    GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins
    (by decide) (by simp) (checkpoint.referenceOwner_of_ne 0 (by decide))
    disposition hbinding polled hpolled'

/-- Normal service really includes the generated packet and deactivates the
conditional instruction; this is not a rejected-message privacy witness. -/
theorem checked_conditional_ordinary_inclusion
    {Γ : VCtx TestPlayer simpleExpr} {pending : Finset VarId}
    {name publicName : VarId} {ty : simpleExpr.Ty}
    {guard : simpleExpr.Expr
      ((name, ty) :: eraseVCtx (viewVCtx (0 : TestPlayer) Γ)) simpleExpr.bool}
    {tail : VegasCore TestPlayer simpleExpr
      ((publicName, .pub ty) :: (name, .sealed 0 ty) :: Γ)}
    {spec : ConditionalOpening guard}
    {accounted : CommitmentAccounting pending
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {fresh : FreshBindings (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {state : BuildState TestPlayer simpleExpr Γ}
    {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {current : CoupledAt
      (compileCore (.commit name 0 guard (.reveal publicName 0 name .here tail))
        fresh state).graph state}
    (rootProfile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) (blockIndex : Nat)
    (execution polled included : runtime.application.PolicyExecution)
    (head : ApplicationPlan.ConditionalHead spec plan)
    (checkpoint : ApplicationPlan.WindowedCheckpoint applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 1 replacement
      blockIndex plan profile current execution)
    (hpolled : polled ∈ (runtime.application.runPolicies
      (unchangedPlayers rootProfile replacement) (runtime.blockEnvironment [0, 1])
      ([0, 1].flatMap fun actor => [Invocation.player actor, .player actor])
      execution).support)
    (hincluded : included ∈ (runtime.application.invoke
      (unchangedPlayers rootProfile replacement) (runtime.blockEnvironment [0, 1])
      polled .environment).support) :
    let site := ConditionalPublicationSite.atHead name publicName 0 guard tail spec
    ∃ chosen ∈ (profile 0 site.choice.decision
        ((current.current.source.toView 0).eraseEnv)).support,
      included ∈ (runtime.application.environmentPolicyStep polled
        (.include (0, execution.native.pool.nextSerial 0))).support ∧
      runtime.image.activeAddress? included.native.application.base.memory ≠
        some (site.choice.publicationNode fresh state) := by
  intro site
  obtain ⟨_, chosen, hchosen, _, _, _, hincludedStep, hinactive⟩ :=
    checkpoint.conditional_ordinary_inclusion head
      GeneratedApplicationSourceLaw.initial_reads_public
      ApplicationBindingOrigins.persistent_image_has_binding_origins
      (by decide) (by simp) (checkpoint.referenceOwner_of_ne 0 (by decide)) polled included
      (by simpa only [WindowedSourceCoverage.runtime, unchangedPlayers] using hpolled)
      (by simpa only [WindowedSourceCoverage.runtime, unchangedPlayers] using hincluded)
  exact ⟨chosen, hchosen, hincludedStep, hinactive⟩

/-- At either checked conditional head, agreement before two actual complete
blocks extends to agreement at their recorded common source result. -/
theorem checked_conditional_block_agreement_at_source
    {Γ : VCtx TestPlayer simpleExpr} {pending : Finset VarId}
    {name publicName : VarId} {ty : simpleExpr.Ty}
    {guard : simpleExpr.Expr
      ((name, ty) :: eraseVCtx (viewVCtx (0 : TestPlayer) Γ)) simpleExpr.bool}
    {tail : VegasCore TestPlayer simpleExpr
      ((publicName, .pub ty) :: (name, .sealed 0 ty) :: Γ)}
    {spec : ConditionalOpening guard}
    {accounted : CommitmentAccounting pending
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {fresh : FreshBindings (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {state : BuildState TestPlayer simpleExpr Γ}
    {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name 0 guard (.reveal publicName 0 name .here tail))
        fresh state).graph state}
    (rootProfile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (blockIndex : Nat)
    (left right finalLeft finalRight : runtime.application.PolicyExecution)
    (head : ApplicationPlan.ConditionalHead spec plan)
    (leftCheckpoint : ApplicationPlan.WindowedCheckpoint applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 1 replacement
      blockIndex plan profile leftCurrent left)
    (rightCheckpoint : ApplicationPlan.WindowedCheckpoint applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 1 replacement
      blockIndex plan profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement runtime 1 left right)
    (result : Option (simpleExpr.Val spec.secretTy))
    (recordedLeft recordedRight : CoupledAt
      (compileCore tail fresh.2.2
        (((state.addCommitEvent name 0 guard fresh.1).1).addRevealEvent
          publicName 0 .here fresh.2.1).1).graph
      (((state.addCommitEvent name 0 guard fresh.1).1).addRevealEvent
        publicName 0 .here fresh.2.1).1)
    (hsourceLeft : recordedLeft.current.source =
      (leftCurrent.current.source.cons (spec.encoding.symm result)).cons
        (spec.encoding.symm result))
    (hsourceRight : recordedRight.current.source =
      (rightCurrent.current.source.cons (spec.encoding.symm result)).cons
        (spec.encoding.symm result))
    (hrefinesLeft : finalLeft.native.application.base.Refines recordedLeft.current.graph.1)
    (hrefinesRight : finalRight.native.application.base.Refines recordedRight.current.graph.1)
    (hfinalLeft : finalLeft ∈ (runtime.application.runPolicies
      (unchangedPlayers rootProfile replacement) (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) left).support)
    (hfinalRight : finalRight ∈ (runtime.application.runPolicies
      (unchangedPlayers rootProfile replacement) (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) right).support) :
    WindowedApplication.PolicyAgreement runtime 1 finalLeft finalRight := by
  apply leftCheckpoint.conditional_block_agreement_at_source head leftCurrent rightCurrent
    left right finalLeft finalRight rightCheckpoint agreement
    GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins command hpure
    (by decide) (by simp) (by decide) result recordedLeft recordedRight hsourceLeft hsourceRight
    hrefinesLeft hrefinesRight
  · simpa only [WindowedSourceCoverage.runtime, unchangedPlayers] using hfinalLeft
  · simpa only [WindowedSourceCoverage.runtime, unchangedPlayers] using hfinalRight

/-- Equal focal source information at a shared checked-plan prefix determines
runtime agreement for any two actual source-prefix derivations. -/
theorem checked_source_prefix_agreement
    (rootProfile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (initial : CoupledAt
      (compileCore source.prog source.fresh compilerInitial).graph compilerInitial)
    (blockIndex : Nat) (point : ApplicationPlan.ProfilePoint TestPlayer simpleExpr)
    (leftCurrent rightCurrent : point.Coupled)
    (left right : runtime.application.PolicyExecution)
    (leftPrefix : ApplicationPlan.WindowedSourcePrefix applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 1 replacement initial
      blockIndex point.plan point.profile leftCurrent left)
    (rightPrefix : ApplicationPlan.WindowedSourcePrefix applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 1 replacement initial
      blockIndex point.plan point.profile rightCurrent right)
    (hview : (leftCurrent.current.source.toView 1).eraseEnv =
      (rightCurrent.current.source.toView 1).eraseEnv) :
    WindowedApplication.PolicyAgreement runtime 1 left right := by
  apply ApplicationPlan.WindowedSourcePrefix.policyAgreement_of_sourceView_eq
    GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins
    (by decide) (by
      intro instruction hinstruction owner hsubmitter
      fin_cases owner <;> simp)
    command hpure blockIndex leftPrefix rightPrefix hview

/-- At a focal-owned conditional head, two actual source prefixes with equal
focal predecessor information cannot record different public results after
supported complete blocks.  The result equality is recovered from final
public memory rather than assumed by the block comparison. -/
theorem checked_focal_conditional_action_eq
    {Γ : VCtx TestPlayer simpleExpr} {pending : Finset VarId}
    {name publicName : VarId} {ty : simpleExpr.Ty}
    {guard : simpleExpr.Expr
      ((name, ty) :: eraseVCtx (viewVCtx (0 : TestPlayer) Γ)) simpleExpr.bool}
    {tail : VegasCore TestPlayer simpleExpr
      ((publicName, .pub ty) :: (name, .sealed 0 ty) :: Γ)}
    {spec : ConditionalOpening guard}
    {accounted : CommitmentAccounting pending
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {fresh : FreshBindings (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    {state : BuildState TestPlayer simpleExpr Γ}
    {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile
      (.commit name 0 guard (.reveal publicName 0 name .here tail))}
    (rootProfile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (initial : CoupledAt
      (compileCore source.prog source.fresh compilerInitial).graph compilerInitial)
    (blockIndex : Nat)
    (leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name 0 guard (.reveal publicName 0 name .here tail))
        fresh state).graph state)
    (left right finalLeft finalRight : runtime.application.PolicyExecution)
    (head : ApplicationPlan.ConditionalHead spec plan)
    (leftPrefix : ApplicationPlan.WindowedSourcePrefix applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 0 replacement initial
      blockIndex plan profile leftCurrent left)
    (rightPrefix : ApplicationPlan.WindowedSourcePrefix applicationPlan rootProfile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
      (runtime.blockService [0, 1]) 0 replacement initial
      blockIndex plan profile rightCurrent right)
    (hview : (leftCurrent.current.source.toView 0).eraseEnv =
      (rightCurrent.current.source.toView 0).eraseEnv)
    (leftResult rightResult : Option (simpleExpr.Val spec.secretTy))
    (leftNext rightNext : CoupledAt (compileCore tail fresh.2.2
      (((state.addCommitEvent name 0 guard fresh.1).1).addRevealEvent
        publicName 0 .here fresh.2.1).1).graph
      (((state.addCommitEvent name 0 guard fresh.1).1).addRevealEvent
        publicName 0 .here fresh.2.1).1)
    (hleftSource : leftNext.current.source =
      (leftCurrent.current.source.cons (spec.encoding.symm leftResult)).cons
        (spec.encoding.symm leftResult))
    (hrightSource : rightNext.current.source =
      (rightCurrent.current.source.cons (spec.encoding.symm rightResult)).cons
        (spec.encoding.symm rightResult))
    (hleftRefines : finalLeft.native.application.base.Refines leftNext.current.graph.1)
    (hrightRefines : finalRight.native.application.base.Refines rightNext.current.graph.1)
    (hleft : finalLeft ∈ (runtime.application.runPolicies
      (applicationPlan.windowedPlayers rootProfile (fun _ => 10) bindingSelector
        choiceSelector (fun _ => 10) 0 replacement)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) left).support)
    (hright : finalRight ∈ (runtime.application.runPolicies
      (applicationPlan.windowedPlayers rootProfile (fun _ => 10) bindingSelector
        choiceSelector (fun _ => 10) 0 replacement)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) right).support) :
    leftResult = rightResult := by
  have leftCheckpoint := leftPrefix.checkpoint
  have rightCheckpoint := rightPrefix.checkpoint
  have agreement : WindowedApplication.PolicyAgreement runtime 0 left right := by
    apply ApplicationPlan.WindowedSourcePrefix.policyAgreement_of_sourceView_eq
      (roster := [0, 1])
      (point := ApplicationPlan.ProfilePoint.of plan profile)
      GeneratedApplicationSourceLaw.initial_reads_public
      ApplicationBindingOrigins.persistent_image_has_binding_origins
      (by decide) (by
        intro instruction hinstruction owner hsubmitter
        fin_cases owner <;> simp)
      command hpure blockIndex leftPrefix rightPrefix hview
  let site := ConditionalPublicationSite.atHead name publicName 0 guard tail spec
  let code := site.code fresh state (site.sourceField fresh state)
    (10 : Nat)
  obtain ⟨rest, hhead⟩ := head.instructions (fun _ => 10)
  have hvalue := leftCheckpoint.public_block_action_eq rightCheckpoint agreement command hpure
    (.conditional code) rest hhead rfl (by decide) finalLeft finalRight hleft hright
    (spec.encoding.symm leftResult) (spec.encoding.symm rightResult) leftNext rightNext
    hleftSource hrightSource hleftRefines hrightRefines
  exact spec.encoding.symm.injective hvalue

end VegasTests.WindowedConditional

/-- info: 'VegasTests.WindowedConditional.checked_conditional_ordinary_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedConditional.checked_conditional_ordinary_packet

/-- info: 'VegasTests.WindowedConditional.checked_conditional_ordinary_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedConditional.checked_conditional_ordinary_inclusion

/-- info: 'VegasTests.WindowedConditional.checked_conditional_block_agreement_at_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.WindowedConditional.checked_conditional_block_agreement_at_source

/-- info: 'VegasTests.WindowedConditional.checked_source_prefix_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedConditional.checked_source_prefix_agreement

/-- info: 'VegasTests.WindowedConditional.checked_focal_conditional_action_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedConditional.checked_focal_conditional_action_eq

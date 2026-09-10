/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationContinuationReadout
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.ConditionalPhaseExecution

/-! # An unchanged owner's conditional choice after arbitrary native interaction -/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem conditional_sample_common
    {rootContext Γ : VCtx P L} {rootPending headPending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    (spec : ConditionalOpening guard)
    {headAccounted : CommitmentAccounting headPending
      (.commit name who guard (.reveal publicName who name .here tail))}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    {headPlan : ApplicationPlan headAccounted fresh state}
    {profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail))}
    (continuation : ProfileContinuation root rootProfile headPlan profile)
    (deadlineOf : Nat → Nat)
    (players : P → (root.image deadlineOf).application.PlayerPolicy)
    (howner : players who = root.liftProfile deadlineOf rootProfile who)
    (priorEnvironment : (root.image deadlineOf).application.EnvironmentPolicy)
    (previous : List (@Invocation P))
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (hreached : execution ∈ ((root.image deadlineOf).application.runPolicies
      players priorEnvironment previous
      (PolicyExecution.initial (root.image deadlineOf).application
        (MessageApplication.State.initial (root.image deadlineOf).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial
              (compileCore rootProg rootFresh rootState).graph))))).support)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state) (eventGuardOf state who guard).choiceReads)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh state
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).sourceField
        fresh state)
      (deadlineOf ((ConditionalPublicationSite.atHead name publicName who guard tail
    spec).choice
        |>.publicationNode fresh state))).binding?
          execution.native.application.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle →
      handle = (who, (ConditionalPublicationSite.atHead name publicName who guard tail spec)
        |>.sourceField fresh state))
    (hcache : let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      ChoiceEncoding.cachedValue (root.image deadlineOf).application
        ((site.choiceEncodingFor fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state)) disposition
          (ApplicationImage.conditionalTransport spec.secretTy)).submission
            (root.image deadlineOf).application) (execution.principalHistory who) = none)
    (hdispatch : ∀ history,
      (root.liftProfile deadlineOf rootProfile who) history
          (State.observe (root.image deadlineOf).application execution.native who) =
        let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
        site.imagePolicy fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state)) (root.image deadlineOf)
          ((root.image deadlineOf).ownerReadout? who
            (site.choice.compiledGuard fresh state).choiceReads)
          (profile who site.choice.decision) (fun _ _ => false) history
            (State.observe (root.image deadlineOf).application execution.native who)) :
    let image := root.image deadlineOf
    let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
    let sourceSlot := site.sourceField fresh state
    let deadline := deadlineOf (site.choice.publicationNode fresh state)
    let encoding := site.choiceEncodingFor fresh state sourceSlot deadline disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    let choices := profile who site.choice.decision
      ((current.current.source.toView who).eraseEnv)
    (players who (execution.principalHistory who)
        (State.observe image.application execution.native who) =
      choices.map fun chosen => .submit (encoding.encode chosen.1)) ∧
    ∀ environment schedule,
      (image.application.runPolicies players environment (.player who :: schedule)
    execution).map
          (fun next => ((encoding.submission image.application).cachedValue image.application
            (next.principalHistory who), next)) =
        choices.bind fun chosen =>
          ((image.application.playerStep who execution (.submit (encoding.encode
    chosen.1))).bind
            (image.application.runPolicies players environment schedule)).map
              (fun next => (some chosen.1, next)) := by
  let image := root.image deadlineOf
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let sourceSlot := site.sourceField fresh state
  let deadline := deadlineOf (site.choice.publicationNode fresh state)
  let encoding := site.choiceEncodingFor fresh state sourceSlot deadline disposition
    (ApplicationImage.conditionalTransport spec.secretTy)
  let choices := profile who site.choice.decision
    ((current.current.source.toView who).eraseEnv)
  have hready := current.current.nextReady current.completedPrefix
    (site.choice.choiceNode fresh state) rfl
  obtain ⟨reads, hreadout, hreads, _⟩ :=
    continuation.runPolicies_ownerReadout?_of_ready_source_view deadlineOf who players howner
      priorEnvironment previous execution hreached site.choice.decision current.current.graph.1
      hrefines hready hinitial current.current.source
      (BuildState.Agrees.view current.current.agrees who)
  have hreadyDisposition := ConditionalPublicationSite.readyDisposition_at_source_prefix
    guard tail spec fresh state sourceSlot deadline current execution.native.application
    hrefines
    disposition hbinding hcanonical
  have hreadyDisposition' : (site.runtimeSite fresh state sourceSlot deadline).readyDisposition
      (some disposition) execution.native.application.memory.done = true := by
    change (site.code fresh state sourceSlot deadline).binding?
      execution.native.application.memory = some disposition at hbinding
    change (site.runtimeSite fresh state sourceSlot deadline).readyDisposition
      ((site.code fresh state sourceSlot deadline).binding?
        execution.native.application.memory) execution.native.application.memory.done = true
      at hreadyDisposition
    rw [hbinding] at hreadyDisposition
    exact hreadyDisposition
  have hresolved : execution.native.application.memory.done
      (site.choice.publicationNode fresh state) = false := by
    have hr := PublicChoiceSite.ready_at_source_prefix guard tail fresh state current
      execution.native.application.memory.done hrefines.memory.completed
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hr
    exact hr.1.2
  have hcommand : players who (execution.principalHistory who)
      (State.observe image.application execution.native who) =
        choices.map fun chosen => .submit (encoding.encode chosen.1) := by
    rw [howner, hdispatch]
    exact site.imagePolicy_first_submission_source_law fresh state sourceSlot deadline image
      disposition (image.ownerReadout? who (site.choice.compiledGuard fresh state).choiceReads)
      (profile who site.choice.decision) (fun _ _ => false)
      (execution.principalHistory who) (State.observe image.application execution.native who)
      current.current.graph.1.store current.current.source reads hbinding hresolved hcache
      hreadyDisposition' hreadout (BuildState.Agrees.view current.current.agrees who) hreads
  refine ⟨hcommand, ?_⟩
  intro environment schedule
  have hjoint := (encoding.submission image.application).runPolicies_sample_joint
    image.application who players environment schedule execution (choices.map Subtype.val)
    (by simpa only [FinDist.map_comp, Function.comp_def, ChoiceEncoding.submission]
      using hcommand) hcache
  rw [FinDist.bind_map] at hjoint
  exact hjoint

/- The public constructors below intentionally expose the same operational law;
their only difference is the accounting derivation carried by `ApplicationPlan`. -/

theorem conditional_sample_of_unchanged_owner
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {rootAccounted : CommitmentAccounting rootPending
    rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState} {rootProfile :
    SourceBehavioralProfile rootProg}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {spec : ConditionalOpening guard} {unresolved : spec.source ∈ pending} {newName : name
    ∉ pending}
    {accounted : CommitmentAccounting (pending.erase spec.source) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ} {publicGuard : (ConditionalPublicationSite.atHead name
    publicName who guard tail spec).PubliclyValidatable fresh state}
    {nextPlan : ApplicationPlan accounted fresh.2.2 (((state.addCommitEvent name who guard
    fresh.1).1).addRevealEvent publicName who .here fresh.2.1).1}
    {profile : SourceBehavioralProfile (.commit name who guard (.reveal publicName who name
    .here tail))}
    (continuation : ProfileContinuation root rootProfile (.conditional (unresolved :=
    unresolved) (newName := newName) (fresh := fresh) publicGuard nextPlan) profile)
    (deadlineOf : Nat → Nat) (players : P → (root.image
    deadlineOf).application.PlayerPolicy)
    (howner : players who = root.liftProfile deadlineOf rootProfile who)
    (priorEnvironment : (root.image deadlineOf).application.EnvironmentPolicy) (previous : List
    (@Invocation P))
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (hreached : execution ∈ ((root.image deadlineOf).application.runPolicies players
    priorEnvironment previous (PolicyExecution.initial (root.image deadlineOf).application
    (MessageApplication.State.initial (root.image deadlineOf).application
    (ApplicationImage.State.initial (ApplicationImage.Memory.initial (compileCore rootProg
    rootFresh rootState).graph))))).support)
    (current : CoupledAt (compileCore (.commit name who guard (.reveal publicName who name
    .here tail)) fresh state).graph state)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic (compileCore (.commit name who guard (.reveal
    publicName who name .here tail)) fresh state) (eventGuardOf state who guard).choiceReads)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding :
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who,
    (ConditionalPublicationSite.atHead name publicName who guard tail spec).sourceField fresh
    state))
    (hcache :
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state)) disposition
        (ApplicationImage.conditionalTransport spec.secretTy)
      ChoiceEncoding.cachedValue (root.image deadlineOf).application
        (encoding.submission (root.image deadlineOf).application)
        (execution.principalHistory who) = none) :
    let image := root.image deadlineOf
    let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
    let sourceSlot := site.sourceField fresh state
    let deadline := deadlineOf (site.choice.publicationNode fresh state)
    let encoding := site.choiceEncodingFor fresh state sourceSlot deadline disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    let choices := profile who site.choice.decision
      ((current.current.source.toView who).eraseEnv)
    (players who
    (execution.principalHistory who) (State.observe image.application execution.native who) =
    choices.map fun chosen => .submit (encoding.encode chosen.1)) ∧ ∀ environment schedule,
    (image.application.runPolicies players environment (.player who :: schedule) execution).map
    (fun next => ((encoding.submission image.application).cachedValue image.application
    (next.principalHistory who), next)) = choices.bind fun chosen =>
    ((image.application.playerStep who execution (.submit (encoding.encode chosen.1))).bind
    (image.application.runPolicies players environment schedule)).map (fun next => (some
    chosen.1, next)) := by
  apply conditional_sample_common spec continuation deadlineOf players howner priorEnvironment
    previous execution hreached current hrefines hinitial disposition hbinding hcanonical hcache
  intro history
  unfold ApplicationPlan.liftProfile
  rw [continuation.liftProfileIn_eq_of_refines (root.image deadlineOf) deadlineOf current
    execution.native hrefines who history]
  have hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false
    := by
    apply Bool.eq_false_iff.mpr; intro hd
    have hm := (hrefines.memory.completed ⟨state.nodes.length + 1,
    (ConditionalPublicationSite.atHead name publicName who guard tail
    spec).choice.publicationNode fresh state |>.isLt⟩).mp hd
    have hlt := (current.completedPrefix _).mp hm
    change state.nodes.length + 1 < state.nodes.length at hlt
    omega
  have hdoneView : (State.observe (root.image deadlineOf).application execution.native
    who).application.done (state.nodes.length + 1) = false := hunresolved
  simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true, ↓reduceIte]

theorem conditionalCopy_sample_of_unchanged_owner
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId} {rootProg : VegasCore P L
    rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg} {rootFresh : FreshBindings
    rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState} {rootProfile :
    SourceBehavioralProfile rootProg}
    {name publicName : VarId} {who : P} {ty : L.Ty} {guard : L.Expr ((name, ty) :: eraseVCtx
    (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)} (spec :
    ConditionalOpening guard)
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending} {accounted :
    CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    {publicGuard : (ConditionalPublicationSite.atHead name publicName who guard tail
    spec).PubliclyValidatable fresh state}
    {nextPlan : ApplicationPlan accounted fresh.2.2 (((state.addCommitEvent name who guard
    fresh.1).1).addRevealEvent publicName who .here fresh.2.1).1}
    {profile : SourceBehavioralProfile (.commit name who guard (.reveal publicName who name
    .here tail))}
    (continuation : ProfileContinuation root rootProfile (.conditionalCopy (newName := newName)
    (unresolved := unresolved) (fresh := fresh) spec publicGuard nextPlan) profile)
    (deadlineOf : Nat → Nat) (players : P → (root.image
    deadlineOf).application.PlayerPolicy) (howner : players who = root.liftProfile deadlineOf
    rootProfile who)
    (priorEnvironment : (root.image deadlineOf).application.EnvironmentPolicy) (previous : List
    (@Invocation P)) (execution : (root.image deadlineOf).application.PolicyExecution)
    (hreached : execution ∈ ((root.image deadlineOf).application.runPolicies players
    priorEnvironment previous (PolicyExecution.initial (root.image deadlineOf).application
    (MessageApplication.State.initial (root.image deadlineOf).application
    (ApplicationImage.State.initial (ApplicationImage.Memory.initial (compileCore rootProg
    rootFresh rootState).graph))))).support)
    (current : CoupledAt (compileCore (.commit name who guard (.reveal publicName who name
    .here tail)) fresh state).graph state) (hrefines : execution.native.application.Refines
    current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic (compileCore (.commit name who guard (.reveal
    publicName who name .here tail)) fresh state) (eventGuardOf state who guard).choiceReads)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding :
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who,
    (ConditionalPublicationSite.atHead name publicName who guard tail spec).sourceField fresh
    state))
    (hcache :
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state)) disposition
        (ApplicationImage.conditionalTransport spec.secretTy)
      ChoiceEncoding.cachedValue (root.image deadlineOf).application
        (encoding.submission (root.image deadlineOf).application)
        (execution.principalHistory who) = none) :
    let image := root.image deadlineOf
    let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
    let sourceSlot := site.sourceField fresh state
    let deadline := deadlineOf (site.choice.publicationNode fresh state)
    let encoding := site.choiceEncodingFor fresh state sourceSlot deadline disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    let choices := profile who site.choice.decision
      ((current.current.source.toView who).eraseEnv)
    (players who
    (execution.principalHistory who) (State.observe image.application execution.native who) =
    choices.map fun chosen => .submit (encoding.encode chosen.1)) ∧ ∀ environment schedule,
    (image.application.runPolicies players environment (.player who :: schedule) execution).map
    (fun next => ((encoding.submission image.application).cachedValue image.application
    (next.principalHistory who), next)) = choices.bind fun chosen =>
    ((image.application.playerStep who execution (.submit (encoding.encode chosen.1))).bind
    (image.application.runPolicies players environment schedule)).map (fun next => (some
    chosen.1, next)) := by
  apply conditional_sample_common spec continuation deadlineOf players howner priorEnvironment
    previous execution hreached current hrefines hinitial disposition hbinding hcanonical hcache
  intro history
  unfold ApplicationPlan.liftProfile
  rw [continuation.liftProfileIn_eq_of_refines (root.image deadlineOf) deadlineOf current
    execution.native hrefines who history]
  have hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false
    := by
    apply Bool.eq_false_iff.mpr; intro hd
    have hm := (hrefines.memory.completed ⟨state.nodes.length + 1,
    (ConditionalPublicationSite.atHead name publicName who guard tail
    spec).choice.publicationNode fresh state |>.isLt⟩).mp hd
    have hlt := (current.completedPrefix _).mp hm
    change state.nodes.length + 1 < state.nodes.length at hlt
    omega
  have hdoneView : (State.observe (root.image deadlineOf).application execution.native
    who).application.done (state.nodes.length + 1) = false := hunresolved
  simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true, ↓reduceIte]

end Vegas.ApplicationPlan.ProfileContinuation

/-- info:
'Vegas.ApplicationPlan.ProfileContinuation.conditional_sample_of_unchanged_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.ProfileContinuation.conditional_sample_of_unchanged_owner

/-- info:
'Vegas.ApplicationPlan.ProfileContinuation.conditionalCopy_sample_of_unchanged_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.ProfileContinuation.conditionalCopy_sample_of_unchanged_owner

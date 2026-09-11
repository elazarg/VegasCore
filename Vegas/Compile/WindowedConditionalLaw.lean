/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedConditionalInversion
import Vegas.Compile.WindowedConditionalCheckpoint

/-! # Exact complete-block law for unchanged conditional owners

Both conditional plan constructors have the same source-indexed native law.
The accepted binding disposition is an explicit input to the factorization;
it is not reconstructed from a supported output. Each supported fixed source
draw has its corresponding sequential successor and native checkpoint, for
both discharge and copy. These are block laws, not whole-program deviation laws.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal owner : P}
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}

/-- A complete conditional or conditional-copy block factors through the
unchanged owner's guarded source kernel. Each source value indexes the exact
submit/wait branch formed using the supplied accepted binding disposition. -/
theorem conditional_block_source_factorization
    (head : ConditionalHead spec plan)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (reference : checkpoint.ReferenceOwner owner)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let environment := runtime.blockEnvironment roster
    let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
    let remaining :=
      (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
        [.environment, .environment] ++
          roster.flatMap fun actor => [.player actor, .environment]
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    let kernel := profile owner site.choice.decision
      ((current.current.source.toView owner).eraseEnv)
    runtime.application.runPolicies players environment
        (WindowedApplication.blockInvocations roster) execution =
      kernel.bind fun chosen =>
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.submit (encoding.encode chosen.1))).bind fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment remaining waited := by
  dsimp only
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let remaining :=
    (afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
      [Invocation.environment, .environment] ++
        roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hnotOwner : owner ∉ beforeRoster := by
    intro hmem
    have hparts := List.nodup_append.mp (hsplit ▸ hroster)
    exact hparts.2.2 owner hmem owner (by simp) rfl
  have hbeforeEnvironment : Invocation.environment ∉ before := by simp [before]
  have hbeforeOwner : Invocation.player owner ∉ before := by simp [before, hnotOwner]
  have hpolls := checkpoint.conditional_polls_source_law_after_others head hinitial horigins
    hroster howner reference disposition hbinding environment before hbeforeEnvironment hbeforeOwner
  have hschedule : WindowedApplication.blockInvocations roster =
      (before ++ [Invocation.player owner, .player owner]) ++ remaining := by
    simp only [WindowedApplication.blockInvocations, before, remaining, hsplit,
      List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hschedule, MessageApplication.runPolicies_append, hpolls]
  simp only [FinDist.bind_bind]
  rw [FinDist.bind_comm]

private theorem fixed_result_eq
    (chosen : L.Val ty) (result : Option (L.Val spec.secretTy))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (sourceNext : CoupledAt
      (compileCore tail fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1).graph
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hstored : Store.getAs final.native.application.base.memory.store
      (state.nextField + 1) ty = some chosen)
    (hsource : sourceNext.current.source =
      (current.current.source.cons (spec.encoding.symm result)).cons
        (spec.encoding.symm result))
    (hrefines : final.native.application.base.Refines sourceNext.current.graph.1) :
    result = spec.encoding chosen := by
  let added := ((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
    publicName owner .here fresh.2.1
  obtain ⟨fieldSpec, hfield, hty, hownerField⟩ :=
    compileCore_fieldOf_spec tail fresh.2.2 added.1 (VHasVar.here)
  have hpublicField : (compileCore tail fresh.2.2 added.1).graph.fieldRefPublic
      ⟨added.1.fieldOf VHasVar.here, ty⟩ :=
    ⟨fieldSpec, hfield, hty, hownerField⟩
  have hrepresented := hrefines.memory.publicFields _ hpublicField
  rw [sourceNext.current.agrees VHasVar.here] at hrepresented
  have hsourceValue := congrArg (fun env => env.get VHasVar.here) hsource
  simp only [VEnv.get, VEnv.cons] at hsourceValue
  have hfieldEq : added.1.fieldOf VHasVar.here = state.nextField + 1 := by
    simp [added, BuildState.nextField, BuildState.nextNode]
    omega
  rw [hfieldEq] at hrepresented
  have heq : chosen = spec.encoding.symm result :=
    Option.some.inj (hstored.symm.trans (hrepresented.trans (congrArg some hsourceValue)))
  rw [heq, Equiv.apply_symm_apply]

/-- A supported fixed draw in a conditional-discharge branch determines the
actual source successor and continuation checkpoint produced by the block. -/
theorem conditional_fixed_branch_source_coupling
    {pending : Finset VarId} {unresolved : spec.source ∈ pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (pending.erase spec.source) tail}
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex
        (.conditional (unresolved := unresolved) (newName := newName)
          (fresh := fresh) publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (reference : checkpoint.ReferenceOwner owner)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (chosen : { value // evalGuard guard value
      ((current.current.source.toView owner).eraseEnv) = true })
    (hchosen : chosen ∈ (profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((current.current.source.toView owner).eraseEnv)).support)
    (hbranch : final ∈
      (let runtime := root.windowed deadlineOf binding choice windowOf
       let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
         replacement
       let environment := runtime.blockEnvironment roster
       let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
       let remaining :=
         (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
           [.environment, .environment] ++
             roster.flatMap fun actor => [.player actor, .environment]
       let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
       let payload := ApplicationImage.Payload.conditional
         (site.choice.publicationNode fresh state)
         (site.sourceRequestPayload fresh state (site.sourceField fresh state)
           (deadlineOf (site.choice.publicationNode fresh state)) disposition
           (spec.encoding chosen.1))
       (runtime.application.runPolicies players environment before execution).bind fun middle =>
         (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
           (runtime.application.playerStep owner submitted .wait).bind fun waited =>
             runtime.application.runPolicies players environment remaining waited).support) :
    ∃ sourceNext : CoupledAt
        (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1,
      sourceNext.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster focal
          replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let payload := ApplicationImage.Payload.conditional
    (P := P) (L := L) (site.choice.publicationNode fresh state)
    (site.sourceRequestPayload fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (spec.encoding chosen.1))
  have hencode : (site.choiceEncodingFor fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)).encode chosen.1 = payload :=
    site.choiceEncodingFor_encode fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition chosen.1
  have hfactor := checkpoint.conditional_block_source_factorization
    (.discharge publicGuard nextPlan) profile current execution hinitial horigins hroster
      howner reference disposition hbinding beforeRoster afterRoster hsplit
  have hfull : final ∈ (runtime.application.runPolicies players environment
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor]
    rw [FinDist.support_bind]
    simp only [Set.mem_iUnion]
    refine ⟨chosen, hchosen, ?_⟩
    rw [hencode]
    exact hbranch
  obtain ⟨result, sourceNext, _, hsource, _, hsteps, hnext, _⟩ :=
    checkpoint.conditional_block publicGuard nextPlan profile horigins current execution final
      hroster owner howner reference.policy hfull
  have hstored := checkpoint.conditional_fixed_branch_publication
    (.discharge publicGuard nextPlan) current execution final hinitial horigins hroster howner
      reference beforeRoster afterRoster hsplit disposition hbinding chosen hchosen hbranch
  have hresult : result = spec.encoding chosen.1 :=
    fixed_result_eq chosen.1 result current sourceNext final hstored hsource hnext.refines
  rw [hresult, Equiv.symm_apply_apply] at hsource
  exact ⟨sourceNext, hsource, hsteps, hnext⟩

/-- The copied-conditional constructor has the same fixed-draw coupling. -/
theorem conditionalCopy_fixed_branch_source_coupling
    {pending : Finset VarId} {unresolved : name ∈ insert name pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex
        (.conditionalCopy (newName := newName) (unresolved := unresolved)
          (fresh := fresh) spec publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (reference : checkpoint.ReferenceOwner owner)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (chosen : { value // evalGuard guard value
      ((current.current.source.toView owner).eraseEnv) = true })
    (hchosen : chosen ∈ (profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((current.current.source.toView owner).eraseEnv)).support)
    (hbranch : final ∈
      (let runtime := root.windowed deadlineOf binding choice windowOf
       let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
         replacement
       let environment := runtime.blockEnvironment roster
       let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
       let remaining :=
         (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
           [.environment, .environment] ++
             roster.flatMap fun actor => [.player actor, .environment]
       let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
       let payload := ApplicationImage.Payload.conditional
         (site.choice.publicationNode fresh state)
         (site.sourceRequestPayload fresh state (site.sourceField fresh state)
           (deadlineOf (site.choice.publicationNode fresh state)) disposition
           (spec.encoding chosen.1))
       (runtime.application.runPolicies players environment before execution).bind fun middle =>
         (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
           (runtime.application.playerStep owner submitted .wait).bind fun waited =>
             runtime.application.runPolicies players environment remaining waited).support) :
    ∃ sourceNext : CoupledAt
        (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1,
      sourceNext.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster focal
          replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let payload := ApplicationImage.Payload.conditional
    (P := P) (L := L) (site.choice.publicationNode fresh state)
    (site.sourceRequestPayload fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (spec.encoding chosen.1))
  have hencode : (site.choiceEncodingFor fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)).encode chosen.1 = payload :=
    site.choiceEncodingFor_encode fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition chosen.1
  have hfactor := checkpoint.conditional_block_source_factorization
    (.copy publicGuard nextPlan) profile current execution hinitial horigins hroster
    howner reference
      disposition hbinding beforeRoster afterRoster hsplit
  have hfull : final ∈ (runtime.application.runPolicies players environment
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor]
    rw [FinDist.support_bind]
    simp only [Set.mem_iUnion]
    refine ⟨chosen, hchosen, ?_⟩
    rw [hencode]
    exact hbranch
  obtain ⟨result, sourceNext, _, hsource, _, hsteps, hnext, _⟩ :=
    checkpoint.conditionalCopy_block publicGuard nextPlan profile horigins current execution final
      hroster owner howner reference.policy hfull
  have hstored := checkpoint.conditional_fixed_branch_publication
    (.copy publicGuard nextPlan) current execution final hinitial horigins hroster howner reference
      beforeRoster afterRoster hsplit disposition hbinding chosen hchosen hbranch
  have hresult : result = spec.encoding chosen.1 :=
    fixed_result_eq chosen.1 result current sourceNext final hstored hsource hnext.refines
  rw [hresult, Equiv.symm_apply_apply] at hsource
  exact ⟨sourceNext, hsource, hsteps, hnext⟩

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_source_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_source_factorization

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_fixed_branch_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.conditional_fixed_branch_source_coupling

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditionalCopy_fixed_branch_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.conditionalCopy_fixed_branch_source_coupling

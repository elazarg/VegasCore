/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockLaw
import Vegas.Compile.WindowedConditionalLaw

/-! # Conditional block continuation laws -/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedSourcePrefix

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr} {α : Type}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal owner : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}

theorem reference_conditional_bind
    {unresolved : spec.source ∈ pending} {newName : name ∉ pending}
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
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
      replacement initial blockIndex (.conditional (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : trace.checkpoint.ReferenceOwner owner)
    (nativeAfter : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution →
      FinDist α)
    (sourceAfter : VEnv L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ) → FinDist α)
    (hafter : ∀ sourceNext final,
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
          sourceNext final →
      final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support →
      nativeAfter final = sourceAfter sourceNext.current.source) :
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).bind nativeAfter) =
      (profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
          sourceAfter ((current.current.source.cons chosen.1).cons chosen.1) := by
  have checkpoint := trace.checkpoint
  obtain ⟨disposition, hbinding, _⟩ := checkpoint.conditional_binding_disposition
    (.discharge publicGuard nextPlan) horigins
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp howner
  have hfactor := checkpoint.conditional_block_source_factorization
    (.discharge publicGuard nextPlan) profile current execution hinitial horigins hroster
      howner reference disposition hbinding beforeRoster afterRoster hsplit
  rw [hfactor, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  refine (FinDist.bind_congr (fun final hbranch => ?_)).trans (FinDist.bind_const _ _)
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
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let remaining :=
    (afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
      [Invocation.environment, .environment] ++
        roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hbranchPayload : final ∈
      ((runtime.application.runPolicies players environment before execution).bind fun middle =>
        (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
          (runtime.application.playerStep owner submitted .wait).bind fun waited =>
            runtime.application.runPolicies players environment remaining waited).support := by
    exact (congrArg (fun message => final ∈
      ((runtime.application.runPolicies players environment before execution).bind fun middle =>
        (runtime.application.playerStep owner middle (.submit message)).bind fun submitted =>
          (runtime.application.playerStep owner submitted .wait).bind fun waited =>
            runtime.application.runPolicies players environment remaining waited).support)
      hencode).mp hbranch
  obtain ⟨sourceNext, hsource, _, hnext⟩ :=
    checkpoint.conditional_fixed_branch_source_coupling publicGuard nextPlan profile current
      execution final hinitial horigins hroster howner reference beforeRoster afterRoster hsplit
      disposition hbinding chosen hchosen hbranchPayload
  have hfull : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor, FinDist.support_bind]
    exact Set.mem_iUnion.mpr ⟨chosen, Set.mem_iUnion.mpr ⟨hchosen, hbranch⟩⟩
  have hlegal : evalGuard guard chosen.1
      ((current.current.source.toView owner).eraseEnv) = true := chosen.2
  have hedge : BlockSourceStep binding final.native.application.base
      (.conditional (newName := newName) (unresolved := unresolved) publicGuard nextPlan)
      profile current nextPlan profile.afterCommit.afterReveal sourceNext :=
    .conditional (spec.encoding chosen.1) (spec.sound _ chosen.1 chosen.2)
      (by simpa only [Equiv.symm_apply_apply] using hsource)
      (by simpa only [Equiv.symm_apply_apply] using hlegal)
  have nextTrace := WindowedSourcePrefix.step trace hfull hedge hnext
  rw [hafter sourceNext final nextTrace hfull, hsource]

theorem reference_conditionalCopy_bind
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
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
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
      replacement initial blockIndex (.conditionalCopy (newName := newName)
        (unresolved := unresolved) spec publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : trace.checkpoint.ReferenceOwner owner)
    (nativeAfter : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution →
      FinDist α)
    (sourceAfter : VEnv L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ) → FinDist α)
    (hafter : ∀ sourceNext final,
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
          sourceNext final →
      final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support →
      nativeAfter final = sourceAfter sourceNext.current.source) :
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).bind nativeAfter) =
      (profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
          sourceAfter ((current.current.source.cons chosen.1).cons chosen.1) := by
  have checkpoint := trace.checkpoint
  obtain ⟨disposition, hbinding, _⟩ := checkpoint.conditional_binding_disposition
    (.copy publicGuard nextPlan) horigins
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp howner
  have hfactor := checkpoint.conditional_block_source_factorization
    (.copy publicGuard nextPlan) profile current execution hinitial horigins hroster
    howner reference
      disposition hbinding beforeRoster afterRoster hsplit
  rw [hfactor, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  refine (FinDist.bind_congr (fun final hbranch => ?_)).trans (FinDist.bind_const _ _)
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
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let remaining :=
    (afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
      [Invocation.environment, .environment] ++
        roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hbranchPayload : final ∈
      ((runtime.application.runPolicies players environment before execution).bind fun middle =>
        (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
          (runtime.application.playerStep owner submitted .wait).bind fun waited =>
            runtime.application.runPolicies players environment remaining waited).support := by
    exact (congrArg (fun message => final ∈
      ((runtime.application.runPolicies players environment before execution).bind fun middle =>
        (runtime.application.playerStep owner middle (.submit message)).bind fun submitted =>
          (runtime.application.playerStep owner submitted .wait).bind fun waited =>
            runtime.application.runPolicies players environment remaining waited).support)
      hencode).mp hbranch
  obtain ⟨sourceNext, hsource, _, hnext⟩ :=
    checkpoint.conditionalCopy_fixed_branch_source_coupling publicGuard nextPlan profile current
      execution final hinitial horigins hroster howner reference beforeRoster afterRoster hsplit
      disposition hbinding chosen hchosen hbranchPayload
  have hfull : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor, FinDist.support_bind]
    exact Set.mem_iUnion.mpr ⟨chosen, Set.mem_iUnion.mpr ⟨hchosen, hbranch⟩⟩
  have hlegal : evalGuard guard chosen.1
      ((current.current.source.toView owner).eraseEnv) = true := chosen.2
  have hedge : BlockSourceStep binding final.native.application.base
      (.conditionalCopy (newName := newName) (unresolved := unresolved) spec publicGuard nextPlan)
      profile current nextPlan profile.afterCommit.afterReveal sourceNext :=
    .conditionalCopy (spec.encoding chosen.1) (spec.sound _ chosen.1 chosen.2)
      (by simpa only [Equiv.symm_apply_apply] using hsource)
      (by simpa only [Equiv.symm_apply_apply] using hlegal)
  have nextTrace := WindowedSourcePrefix.step trace hfull hedge hnext
  rw [hafter sourceNext final nextTrace hfull, hsource]

end Vegas.ApplicationPlan.WindowedSourcePrefix

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.reference_conditional_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.reference_conditional_bind

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.reference_conditionalCopy_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.reference_conditionalCopy_bind

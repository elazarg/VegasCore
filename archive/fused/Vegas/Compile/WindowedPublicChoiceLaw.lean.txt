/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPublicChoiceInversion
import Vegas.Compile.WindowedPublicChoiceCheckpoint

/-! # Exact complete-block law for reference public-choice owners

The emitted block factors through the reference owner's source kernel.  The
sampled guarded value remains an explicit index of the concrete native
continuation; no supported branch is selected after the fact.
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
variable {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
variable {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}

/-- The complete emitted block for a reference public-choice owner is the
owner's exact source decision kernel bound to the concrete submit/wait branch
and every remaining native invocation.  Polls before the owner may randomize,
but are independent of the source draw and are therefore commuted inside its
continuation. -/
theorem publicChoice_block_source_factorization
    (publicGuard :
      (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
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
    let kernel := profile owner (.here guard (.reveal publicName owner name .here tail))
      ((current.current.source.toView owner).eraseEnv)
    runtime.application.runPolicies players environment
        (WindowedApplication.blockInvocations roster) execution =
      kernel.bind fun chosen =>
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.submit (.choice (state.nodes.length + 1) ⟨ty, chosen.1⟩))).bind fun submitted =>
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
  let kernel := profile owner (.here guard (.reveal publicName owner name .here tail))
    ((current.current.source.toView owner).eraseEnv)
  have hnotOwner : owner ∉ beforeRoster := by
    intro hmem
    have hparts := List.nodup_append.mp (hsplit ▸ hroster)
    exact hparts.2.2 owner hmem owner (by simp) rfl
  have hbeforeEnvironment : Invocation.environment ∉ before := by
    simp [before]
  have hbeforeOwner : Invocation.player owner ∉ before := by
    simp [before, hnotOwner]
  have hpolls := checkpoint.publicChoice_polls_source_law_after_others hinitial hroster
    howner reference environment before hbeforeEnvironment hbeforeOwner
  have hschedule : WindowedApplication.blockInvocations roster =
      (before ++ [Invocation.player owner, .player owner]) ++ remaining := by
    simp only [WindowedApplication.blockInvocations, before, remaining, hsplit,
      List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hschedule, MessageApplication.runPolicies_append, hpolls]
  simp only [FinDist.bind_bind]
  rw [FinDist.bind_comm]
  rfl

/-- A supported fixed draw and a supported continuation of the corresponding
native branch produce the canonical source successor for the public-choice
block.  The source value in the successor is the draw fixed before executing
the native continuation. -/
theorem publicChoice_fixed_branch_source_coupling
    (publicGuard :
      (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName owner guard tail).decision)
    (deadline : Nat)
    (hselect : choice ((PublicChoiceSite.atHead name publicName owner guard tail).code
      fresh state) = some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
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
       (runtime.application.runPolicies players environment before execution).bind fun middle =>
         (runtime.application.playerStep owner middle
           (.submit (.choice (state.nodes.length + 1) ⟨ty, chosen.1⟩))).bind fun submitted =>
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
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
          replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((PublicChoiceSite.atHead name publicName owner guard tail).code
              fresh state).endpoint.publicationNode := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let kernel := profile owner (.here guard (.reveal publicName owner name .here tail))
    ((current.current.source.toView owner).eraseEnv)
  have hfactor := checkpoint.publicChoice_block_source_factorization publicGuard nextPlan profile
    current execution hinitial hroster howner reference beforeRoster afterRoster hsplit
  have hfull : final ∈ (runtime.application.runPolicies players environment
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨chosen, hchosen, by
      simpa only [FinDist.support_bind, Set.mem_iUnion] using hbranch⟩
  obtain ⟨actual, sourceNext, hsource, hlegal, hsteps, hnext, hinactive⟩ :=
    checkpoint.publicChoice_block publicGuard nextPlan profile fallback deadline hselect current
      execution final hroster owner howner reference.policy hfull
  have hstored := checkpoint.publicChoice_fixed_branch_publication publicGuard nextPlan profile
    current execution final hinitial hroster howner reference beforeRoster afterRoster hsplit
    chosen hchosen hbranch
  have hrecorded : Store.getAs final.native.application.base.memory.store
      (state.nextField + 1) ty = some actual := by
    let added := ((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
      publicName owner .here fresh.2.1
    have hspec := compileCore_fieldOf_spec tail fresh.2.2 added.1 (VHasVar.here)
    obtain ⟨fieldSpec, hfield, hty, hownerField⟩ := hspec
    have hpublicField : (compileCore tail fresh.2.2 added.1).graph.fieldRefPublic
        ⟨added.1.fieldOf VHasVar.here, ty⟩ :=
      ⟨fieldSpec, hfield, hty, hownerField⟩
    have hrepresented := hnext.refines.memory.publicFields _ hpublicField
    have hagrees := sourceNext.current.agrees VHasVar.here
    rw [hagrees] at hrepresented
    have hsourceValue := congrArg (fun env => env.get VHasVar.here) hsource
    simp only [VEnv.get, VEnv.cons] at hsourceValue
    have hfieldEq : added.1.fieldOf VHasVar.here = state.nextField + 1 := by
      simp [added, BuildState.nextField, BuildState.nextNode]
      omega
    rw [hfieldEq] at hrepresented
    exact hrepresented.trans (congrArg some hsourceValue)
  have hactual : actual = chosen.1 := Option.some.inj (hrecorded.symm.trans hstored)
  subst actual
  exact ⟨sourceNext, hsource, hsteps, hnext, hinactive⟩

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_source_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_source_factorization

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_fixed_branch_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_fixed_branch_source_coupling

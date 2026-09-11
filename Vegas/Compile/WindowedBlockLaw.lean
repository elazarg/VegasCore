/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourcePrefix
import Vegas.Compile.WindowedBindingLaw
import Vegas.Compile.WindowedPublicChoiceLaw

/-! # Composing windowed blocks with source continuations

The continuation hypothesis applies only at actual initialized successor
prefixes. Exact block kernels and their fixed-draw source couplings then
transport this hypothesis through the block. No source evaluator is introduced.
-/

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
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}

section Binding

variable {owner : P}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}

/-- A reference binding owner's full block composes with any continuation
law valid at actual source successors. Opposing raw commands may be randomized. -/
theorem reference_binding_bind
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hfallbacks : root.BlockFallbacks binding choice)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : trace.checkpoint.ReferenceOwner owner)
    (nativeAfter : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution →
      FinDist α)
    (sourceAfter : VEnv L ((name, .sealed owner ty) :: Γ) → FinDist α)
    (hafter : ∀ sourceNext final,
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
        replacement initial (blockIndex + 1) nextPlan profile.afterCommit sourceNext final →
      final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support →
      nativeAfter final = sourceAfter sourceNext.current.source) :
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).bind nativeAfter) =
      (profile owner (.here guard tail)
        ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
          sourceAfter (current.current.source.cons chosen.1) := by
  have checkpoint := trace.checkpoint
  obtain ⟨fallback, deadline, hselect⟩ :=
    (checkpoint.continuation.blockFallbacks binding choice hfallbacks).1
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp howner
  have hfactor := checkpoint.binding_block_source_factorization unrestricted nextPlan profile
    current execution hinitial hroster howner reference beforeRoster afterRoster hsplit
  rw [hfactor, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  refine (FinDist.bind_congr (fun final hbranch => ?_)).trans (FinDist.bind_const _ _)
  obtain ⟨sourceNext, hsource, _, hnext, _, hresolved⟩ :=
    checkpoint.binding_fixed_branch_source_coupling unrestricted nextPlan profile fallback
      deadline hselect current execution final hinitial hroster howner reference beforeRoster
      afterRoster hsplit chosen hchosen hbranch
  have hfull : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor, FinDist.support_bind]
    exact Set.mem_iUnion.mpr ⟨chosen, Set.mem_iUnion.mpr ⟨hchosen, hbranch⟩⟩
  have nextTrace := WindowedSourcePrefix.step trace hfull
    (.binding fallback deadline hselect chosen.1 hsource hresolved) hnext
  rw [hafter sourceNext final nextTrace hfull, hsource]

end Binding

section PublicChoice

variable {owner : P} {publicName : VarId}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
variable {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}

/-- A reference public-choice block transports a continuation law through
the original source commit and its immediate reveal. -/
theorem reference_publicChoice_bind
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
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hfallbacks : root.BlockFallbacks binding choice)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : trace.checkpoint.ReferenceOwner owner)
    (nativeAfter : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution →
      FinDist α)
    (sourceAfter : VEnv L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ) → FinDist α)
    (hafter : ∀ sourceNext final,
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
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
  obtain ⟨fallback, deadline, hselect⟩ :=
    (checkpoint.continuation.blockFallbacks binding choice hfallbacks).1
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp howner
  have hfactor := checkpoint.publicChoice_block_source_factorization publicGuard nextPlan profile
    current execution hinitial hroster howner reference beforeRoster afterRoster hsplit
  rw [hfactor, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  refine (FinDist.bind_congr (fun final hbranch => ?_)).trans (FinDist.bind_const _ _)
  obtain ⟨sourceNext, hsource, _, hnext, _⟩ :=
    checkpoint.publicChoice_fixed_branch_source_coupling publicGuard nextPlan profile fallback
      deadline hselect current execution final hinitial hroster howner reference beforeRoster
      afterRoster hsplit chosen hchosen hbranch
  have hfull : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor, FinDist.support_bind]
    exact Set.mem_iUnion.mpr ⟨chosen, Set.mem_iUnion.mpr ⟨hchosen, hbranch⟩⟩
  have nextTrace := WindowedSourcePrefix.step trace hfull
    (.publicChoice chosen.1 hsource chosen.2) hnext
  rw [hafter sourceNext final nextTrace hfull, hsource]

end PublicChoice

section Sample

variable {dist : L.DistExpr (erasePubVCtx Γ) ty}
variable {tail : VegasCore P L ((name, .pub ty) :: Γ)}
variable {accounted : CommitmentAccounting pending tail}
variable {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}

/-- The exact chance block composes with a continuation law at its actual
initialized successors, without restrictions on the raw replacement policy. -/
theorem sample_bind
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex (.sample nextPlan) profile current execution)
    (hroster : roster.Nodup)
    (nativeAfter : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution →
      FinDist α)
    (sourceAfter : VEnv L ((name, .pub ty) :: Γ) → FinDist α)
    (hafter : ∀ sourceNext final,
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
        replacement initial (blockIndex + 1) nextPlan profile.afterSample sourceNext final →
      final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support →
      nativeAfter final = sourceAfter sourceNext.current.source) :
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).bind nativeAfter) =
      (L.evalDist dist current.current.source.eraseSampleEnv).bind fun value =>
        sourceAfter (current.current.source.cons value) := by
  have checkpoint := trace.checkpoint
  obtain ⟨hlaw, hcoupling⟩ := checkpoint.sample_block nextPlan profile current execution
  rw [hlaw]
  simp only [FinDist.bind_bind]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro value hvalue
  refine (FinDist.bind_congr (fun middle hmiddle => ?_)).trans (FinDist.bind_const _ _)
  obtain ⟨sourceNext, hsource, hnext⟩ := hcoupling middle hmiddle value hvalue
  refine (FinDist.bind_congr (fun final hsuffix => ?_)).trans (FinDist.bind_const _ _)
  obtain ⟨hrefines, hactivation⟩ := hnext final hsuffix
  have hfull : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hlaw]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨middle, hmiddle, value, hvalue, hsuffix⟩
  have successor := checkpoint.sample_successor nextPlan profile current execution hroster
    sourceNext final hfull hrefines hactivation
  have nextTrace := WindowedSourcePrefix.step trace hfull (.sample value hvalue hsource) successor
  rw [hafter sourceNext final nextTrace hfull, hsource]

end Sample

end Vegas.ApplicationPlan.WindowedSourcePrefix

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.reference_binding_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.reference_binding_bind

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.reference_publicChoice_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.reference_publicChoice_bind

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.sample_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.sample_bind

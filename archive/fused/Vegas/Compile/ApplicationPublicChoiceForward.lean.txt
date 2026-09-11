/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.ApplicationPhaseCaches
import Vegas.Compile.ApplicationOwnerPhase
import Vegas.Compile.ApplicationOrderCheckpoint

/-! # Composing a public-choice phase with its source continuation -/

noncomputable section

namespace Vegas.ApplicationPlan.ForwardCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

theorem publicChoice_bind
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    (publicGuard : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      (.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard nextPlan) profile current execution)
    (hinitial : ToEventGraph.BuildResult.InitialReadsPublic
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state) (eventGuardOf state who guard).choiceReads)
    {Ω : Type*} (after : (root.image deadlineOf).application.PolicyExecution → FinDist Ω)
    (sourceAfter : VEnv L
      ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ) → FinDist Ω)
    (hafter : ∀ next native,
      ForwardCheckpoint root rootProfile deadlineOf nextPlan
          profile.afterCommit.afterReveal next native →
        after native = sourceAfter next.current.source)
    (sourceOrdered : Bool := false) :
    ((if sourceOrdered then (root.image deadlineOf).orderedApplication.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      [.player who, .environment] execution else (root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      [.player who, .environment] execution).bind after) =
      (profile who (.here guard (.reveal publicName who name .here tail))
        ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
          sourceAfter ((current.current.source.cons chosen.1).cons chosen.1) := by
  let image := root.image deadlineOf
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let code := site.code fresh state
  have hhead : (ApplicationPlan.publicChoice (newName := newName)
      (unresolved := unresolved) (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
      .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  have hmem := checkpoint.instruction_mem (.publicChoice code)
    (hhead ▸ List.mem_cons_self)
  obtain ⟨previous, hprevious⟩ := checkpoint.reached
  have hunresolved : execution.native.application.memory.done (state.nodes.length + 1) =
      false := by
    apply Bool.eq_false_iff.mpr
    intro hdone
    have hdoneGraph := (checkpoint.refines.memory.completed
      (site.publicationNode fresh state)).mp hdone
    have hlt := (current.completedPrefix _).mp hdoneGraph
    change state.nodes.length + 1 < state.nodes.length at hlt
    omega
  have hfreshHead := (List.forall_cons _ _ _).mp checkpoint.caches |>.1
  have hcache : ChoiceEncoding.cachedValue image.application
      ((ApplicationImage.choiceEncoding code.endpoint.publicationNode ty).submission
        image.application) (execution.principalHistory who) = none := by
    exact hfreshHead
  have hphase := checkpoint.continuation.publicChoice_phase_of_unchanged_owner deadlineOf
    (root.liftProfile deadlineOf rootProfile) rfl image.serialService previous execution
    hprevious current checkpoint.refines hinitial hcache image.serialService (by
      intro chosen hchosen submitted hsubmitted
      exact image.serialService_after_submit execution submitted (.publicChoice code) who _
        (checkpoint.head_lookup (.publicChoice code) _ hhead) rfl
        (checkpoint.lookup_nextSerial_eq_none who) hsubmitted)
  have hselected : (if sourceOrdered then image.orderedApplication.runPolicies
      (root.liftProfile deadlineOf rootProfile) image.serialService
        [.player who, .environment] execution else
      image.application.runPolicies (root.liftProfile deadlineOf rootProfile)
        image.serialService [.player who, .environment] execution) =
      image.application.runPolicies (root.liftProfile deadlineOf rootProfile)
        image.serialService [.player who, .environment] execution := by
    split
    · exact hphase.2.2 (checkpoint.activeAddress?_head (.publicChoice code) _ hhead)
    · rfl
  rw [hselected]
  rw [hphase.1, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  rw [FinDist.bind_bind]
  let target := sourceAfter ((current.current.source.cons chosen.1).cons chosen.1)
  refine (FinDist.bind_congr (fun submitted hsubmitted => ?_)).trans
    (FinDist.bind_const _ target)
  refine (FinDist.bind_congr (fun included hincluded => ?_)).trans
    (FinDist.bind_const _ target)
  obtain ⟨next, hsource, hrefines⟩ := hphase.2.1 chosen hchosen submitted hsubmitted
    included hincluded
  have hnative : included ∈ (image.application.runPolicies
      (root.liftProfile deadlineOf rootProfile) image.serialService
      [.player who, .environment] execution).support := by
    rw [hphase.1]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨chosen, hchosen, submitted, hsubmitted, hincluded⟩
  have hnext : ForwardCheckpoint root rootProfile deadlineOf nextPlan
      profile.afterCommit.afterReveal next included := by
    refine ⟨.publicChoice checkpoint.continuation, hrefines,
      checkpoint.reached_after _ included hnative,
      checkpoint.aligned_after_phase (.publicChoice code) _ hhead included hnative, ?_, ?_⟩
    · exact ProfileContinuation.publicChoice_phase_preserves_nextCaches root rootProfile
        publicGuard nextPlan profile checkpoint.continuation deadlineOf image.serialService
        current execution included
        checkpoint.refines hunresolved ((List.forall_cons _ _ _).mp checkpoint.caches).2 hnative
    · have haccepted := ApplicationImage.AcceptedBindingPrefix.runPolicies image
          state.nodes.length (root.liftProfile deadlineOf rootProfile) image.serialService
          [.player who, .environment] execution included checkpoint.accepted hnative
      have hadvance := ApplicationImage.AcceptedBindingPrefix.advance_of_coveredNonbinding root
        deadlineOf state.nodes.length (state.nodes.length + 2) included.native.application
        (.publicChoice code) haccepted hmem
        (by intro binding hbinding; cases hbinding) (by
          intro node hlower hupper
          change node ∈ [state.nodes.length, state.nodes.length + 1]
          simp only [List.mem_cons]
          omega)
      simpa only [BuildState.addRevealEvent_nodes, BuildState.addCommitEvent_nodes,
        List.length_append, List.length_singleton, Nat.add_assoc] using hadvance
  rw [hafter next included hnext, hsource]

end Vegas.ApplicationPlan.ForwardCheckpoint

/--
info: 'Vegas.ApplicationPlan.ForwardCheckpoint.publicChoice_bind' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.publicChoice_bind

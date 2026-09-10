/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedContinuationReadout
import Vegas.Compile.WindowedReadoutProjection
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.PublicChoicePhaseExecution

/-! # Source public-choice kernels in the windowed policy runner -/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A ready unchanged public-choice owner samples its source policy exactly
once. The full following native execution retains the sample in its real cache. -/
theorem windowedPublicChoice_sample_of_unchanged_owner
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {build : BuildState P L Γ}
    {publicGuard : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build}
    {nextPlan : ApplicationPlan accounted fresh.2.2
      (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1}
    {profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail))}
    (continuation : ProfileContinuation root rootProfile
      (.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : P →
      (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (howner : players who =
      (root.windowed deadlineOf binding choice windowOf).blockPlayer who
        ((root.windowed deadlineOf binding choice windowOf).liftPlayerPolicy
          (root.liftProfile deadlineOf rootProfile who)))
    (priorEnvironment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (previous : List (@Invocation P))
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hreached : execution ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        players priorEnvironment previous
        (PolicyExecution.initial
          (root.windowed deadlineOf binding choice windowOf).application
          (MessageApplication.State.initial
            (root.windowed deadlineOf binding choice windowOf).application
            ((root.windowed deadlineOf binding choice windowOf).initial
              (ApplicationImage.State.initial
                (ApplicationImage.Memory.initial
                  (compileCore rootProg rootFresh rootState).graph)))))).support)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build) (eventGuardOf build who guard).choiceReads)
    (hcache : let runtime := root.windowed deadlineOf binding choice windowOf
      ((ApplicationImage.choiceEncoding (P := P) (build.nodes.length + 1) ty).submission
        runtime.application).cachedValue runtime.application
          (execution.principalHistory who) = none)
    (instruction : ApplicationInstruction P L)
    (hindex : getElem? (root.windowed deadlineOf binding choice windowOf).image.instructions
      ((execution.principalHistory who).length / 3) = some instruction)
    (hactive : (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hslot : (execution.principalHistory who).length % 3 < 2)
    (hsubmitter : instruction.submitter = some who) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let encoding := ApplicationImage.choiceEncoding (P := P) (build.nodes.length + 1) ty
    let choices := profile who (.here guard (.reveal publicName who name .here tail))
      ((current.current.source.toView who).eraseEnv)
    (players who (execution.principalHistory who)
        (State.observe runtime.application execution.native who) =
      choices.map fun chosen => .submit (encoding.encode chosen.1)) ∧
    ∀ environment schedule,
      (runtime.application.runPolicies players environment (.player who :: schedule)
        execution).map (fun next =>
          ((encoding.submission runtime.application).cachedValue runtime.application
            (next.principalHistory who), next)) =
        choices.bind fun chosen =>
          ((runtime.application.playerStep who execution
            (.submit (encoding.encode chosen.1))).bind
              (runtime.application.runPolicies players environment schedule)).map
                (fun next => (some chosen.1, next)) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let original := root.image deadlineOf
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let encoding := ApplicationImage.choiceEncoding (P := P) (build.nodes.length + 1) ty
  let choices := profile who site.decision ((current.current.source.toView who).eraseEnv)
  have hready := current.current.nextReady current.completedPrefix
    (site.choiceNode fresh build) rfl
  obtain ⟨reads, hreadout, hreads, _⟩ :=
    continuation.windowedBlock_ownerReadout?_of_ready_source_view deadlineOf binding choice
      windowOf who players howner priorEnvironment previous execution hreached site.decision
      current.current.graph.1 hrefines hready hinitial current.current.source
      (BuildState.Agrees.view current.current.agrees who)
  have hreadyNative := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    execution.native.application.base.memory.done hrefines.memory.completed
  have hunresolved : execution.native.application.base.memory.done (build.nodes.length + 1) =
      false := by
    have hparts := hreadyNative
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hparts
    exact hparts.1.2
  have hbase : root.liftProfile deadlineOf rootProfile who
      ((execution.principalHistory who).map fun entry =>
        show original.application.PlayerEntry from runtime.erasePlayerEntry entry)
      (runtime.eraseView (State.observe runtime.application execution.native who)) =
        choices.map fun chosen => .submit (encoding.encode chosen.1) := by
    unfold ApplicationPlan.liftProfile
    let projected : original.application.State :=
      ⟨execution.native.application.base, execution.native.pool, execution.native.receipts⟩
    change ApplicationPlan.liftProfileIn original deadlineOf root rootProfile who
      ((execution.principalHistory who).map fun entry =>
        show original.application.PlayerEntry from runtime.erasePlayerEntry entry)
      (State.observe original.application projected who) = _
    rw [continuation.liftProfileIn_eq_of_refines original deadlineOf current
      projected hrefines who
      ((execution.principalHistory who).map fun entry =>
        show original.application.PlayerEntry from runtime.erasePlayerEntry entry)]
    have hdone : (State.observe original.application projected who).application.done
        (build.nodes.length + 1) = false := hunresolved
    simp only [ApplicationPlan.liftProfileIn, hdone, Bool.false_eq_true, ↓reduceIte]
    apply site.controller_first_submission_source_law fresh build original.application encoding
      (fun view => view.application.done)
      (original.ownerReadout? who (eventGuardOf build who guard).choiceReads)
      (profile who site.decision) (fun _ _ => false) _
      (State.observe original.application projected who) current.current.graph.1.store
      current.current.source reads hunresolved
    · exact (runtime.cachedValue_erasePlayerEntry original encoding
        (execution.principalHistory who)).symm.trans hcache
    · exact hreadyNative
    · exact (runtime.ownerReadout?_erasePlayerEntry original who
        (eventGuardOf build who guard).choiceReads (execution.principalHistory who)
        (State.observe runtime.application execution.native who)).symm.trans hreadout
    · exact BuildState.Agrees.view current.current.agrees who
    · exact hreads
  have hcommand : players who (execution.principalHistory who)
      (State.observe runtime.application execution.native who) =
        choices.map fun chosen => .submit (encoding.encode chosen.1) := by
    rw [howner, runtime.blockPlayer_normal who _ _ _ instruction hindex hactive hslot hsubmitter]
    unfold WindowedApplication.liftPlayerPolicy
    rw [hbase]
    simp only [FinDist.map_comp, Function.comp_def, WindowedApplication.liftPlayerCommand]
  refine ⟨hcommand, ?_⟩
  intro environment schedule
  have hjoint := (encoding.submission runtime.application).runPolicies_sample_joint
    runtime.application who players environment schedule execution (choices.map Subtype.val)
    (by simpa only [FinDist.map_comp, Function.comp_def, ChoiceEncoding.submission] using hcommand)
    hcache
  rw [FinDist.bind_map] at hjoint
  exact hjoint

end Vegas.ApplicationPlan.ProfileContinuation

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.windowedPublicChoice_sample_of_unchanged_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.ProfileContinuation.windowedPublicChoice_sample_of_unchanged_owner

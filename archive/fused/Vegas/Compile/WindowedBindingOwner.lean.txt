/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedContinuationReadout
import Vegas.Compile.WindowedReadoutProjection
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.BindingSourceCoupling
import Interaction.ChoiceControllerHistory

/-! # Source binding kernels in the windowed policy runner

At the unchanged owner's first ordinary poll, a ready source binding samples
exactly its source policy. The sampled value remains jointly coupled to every
subsequent native execution. Prior expiry traffic is retained in the history;
other players and both the preceding and following service may be arbitrary.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The first ordinary binding poll draws once from the unchanged source
policy. The joint law retains that draw through the real private-command cache. -/
theorem windowedBinding_sample_of_unchanged_owner
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {name : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)} {build : BuildState P L Γ}
    {unrestricted : UnrestrictedBinding guard}
    {nextPlan : ApplicationPlan accounted fresh.2 (build.addCommitEvent name who guard fresh.1).1}
    {profile : SourceBehavioralProfile (.commit name who guard tail)}
    (continuation : ProfileContinuation root rootProfile
      (.binding (newName := newName) (fresh := fresh) unrestricted nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : P →
      (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (hcommands : ∀ history view command, command ∈ (players who history view).support →
      (root.windowed deadlineOf binding choice windowOf).erasePlayerCommand command ∈
          (root.liftProfile deadlineOf rootProfile who
            (history.map (root.windowed deadlineOf binding choice windowOf).erasePlayerEntry)
            ((root.windowed deadlineOf binding choice windowOf).eraseView view)).support ∨
        (root.windowed deadlineOf binding choice windowOf).image.IdleOrExpiryCommand
          ((root.windowed deadlineOf binding choice windowOf).erasePlayerCommand command))
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
    (current : CoupledAt (compileCore (.commit name who guard tail) fresh build).graph build)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic (compileCore (.commit name who guard tail)
      fresh build) (eventGuardOf build who guard).choiceReads)
    (hcache : (root.image deadlineOf).registrationCache build.nextField
      ((execution.principalHistory who).map
        (root.windowed deadlineOf binding choice windowOf).erasePlayerEntry) = none)
    (hordinary :
      let runtime := root.windowed deadlineOf binding choice windowOf
      players who (execution.principalHistory who)
          (State.observe runtime.application execution.native who) =
        runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile who)
          (execution.principalHistory who)
          (State.observe runtime.application execution.native who)) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let encoding := (ApplicationImage.registrationEncoding build.nextField).privateCommand
      runtime.application
    let choices := profile who (.here guard tail)
      ((current.current.source.toView who).eraseEnv)
    (players who (execution.principalHistory who)
        (State.observe runtime.application execution.native who) =
      choices.map fun chosen => .privateCommand (.register build.nextField ⟨ty, chosen.1⟩)) ∧
    ∀ environment schedule,
      (runtime.application.runPolicies players environment (.player who :: schedule)
        execution).map (fun next =>
          (encoding.cachedValue runtime.application (next.principalHistory who), next)) =
        choices.bind fun chosen =>
          ((runtime.application.playerStep who execution
            (.privateCommand (.register build.nextField ⟨ty, chosen.1⟩))).bind
              (runtime.application.runPolicies players environment schedule)).map
                (fun next => (some ⟨ty, chosen.1⟩, next)) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let original := root.image deadlineOf
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let choices := profile who site ((current.current.source.toView who).eraseEnv)
  have hready := SourceDecisionSite.binding_ready_at_source_prefix guard tail fresh build
    current execution.native.application.base.memory.done hrefines.memory.completed
  obtain ⟨reads, hreadout, _, hview⟩ :=
    continuation.windowed_ownerReadout?_of_ready_source_view deadlineOf binding choice
      windowOf who players hcommands priorEnvironment previous execution hreached site
      current.current.graph.1 hrefines hready.1 hinitial current.current.source
      (BuildState.Agrees.view current.current.agrees who)
  have hunbound : execution.native.application.base.memory.accepted
      (site.compiledField fresh build) = none := by
    rw [← site.bindingCode_sourceField fresh build (site.compiledField fresh build)]
    exact hrefines.accepted_eq_none_of_not_done (site.compiledNode fresh build) hready.1.1
  have hresolved : (site.bindingCode fresh build (site.compiledField fresh build)).resolved
      execution.native.application.base.memory = false := by
    rw [BindingCode.resolved, site.bindingCode_sourceField, hunbound]
    exact hready.2.1
  have hbase : root.liftProfile deadlineOf rootProfile who
      ((execution.principalHistory who).map fun entry =>
        show original.application.PlayerEntry from runtime.erasePlayerEntry entry)
      (runtime.eraseView (State.observe runtime.application execution.native who)) =
        choices.map fun chosen => .privateCommand (.register build.nextField ⟨ty, chosen.1⟩) := by
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
        build.nodes.length = false := hready.2.1
    simp only [ApplicationPlan.liftProfileIn, hdone, Bool.false_eq_true, ↓reduceIte]
    apply site.bindingPolicy_first_registration_source_law fresh build original
      (profile who site) _ (State.observe original.application projected who)
      current.current.source reads hresolved hready.2.2 hcache
    · exact (runtime.ownerReadout?_erasePlayerEntry original who
        (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads
        (execution.principalHistory who)
        (State.observe runtime.application execution.native who)).symm.trans hreadout
    · exact hview
  have hcommand : players who (execution.principalHistory who)
      (State.observe runtime.application execution.native who) =
        choices.map fun chosen => .privateCommand (.register build.nextField ⟨ty, chosen.1⟩) := by
    rw [hordinary]
    unfold WindowedApplication.liftPlayerPolicy
    rw [hbase]
    simp only [FinDist.map_comp, Function.comp_def, WindowedApplication.liftPlayerCommand]
  refine ⟨hcommand, ?_⟩
  intro environment schedule
  let encoding := (ApplicationImage.registrationEncoding build.nextField).privateCommand
    runtime.application
  have hjoint := encoding.runPolicies_sample_joint runtime.application who players environment
    schedule execution (choices.map fun chosen => (⟨ty, chosen.1⟩ : TypedValue L))
    (by simpa only [FinDist.map_comp, Function.comp_def, encoding,
      ChoiceEncoding.privateCommand, ApplicationImage.registrationEncoding] using hcommand)
    ((runtime.registrationCache_erasePlayerEntry original build.nextField
      (execution.principalHistory who)).trans hcache)
  simpa only [FinDist.bind_map, encoding, ChoiceEncoding.privateCommand,
    ApplicationImage.registrationEncoding] using hjoint

end Vegas.ApplicationPlan.ProfileContinuation

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.windowedBinding_sample_of_unchanged_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.windowedBinding_sample_of_unchanged_owner

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedContinuationReadout
import Vegas.Compile.ApplicationConditionalOwner
import Vegas.Compile.WindowedReadoutProjection
import Vegas.Compile.ConditionalHead

/-! # An unchanged conditional owner in the windowed block runtime

The proof operates directly on the activation-windowed interpreter. Prior
expiry traffic remains in the real history; no projection to an execution of
the undecorated application is assumed.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- At an ordinary owner slot, a fresh conditional choice has exactly its
source kernel and remains cached jointly with every subsequent actual windowed
continuation. Other players and the preceding environment are unrestricted. -/
theorem windowedConditional_sample_of_unchanged_owner
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
    (head : ConditionalHead spec headPlan)
    (continuation : ProfileContinuation root rootProfile headPlan profile)
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
    (execution :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
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
        fresh state).graph state)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state) (eventGuardOf state who guard).choiceReads)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle →
      handle = (who, (ConditionalPublicationSite.atHead name publicName who guard tail spec)
        |>.sourceField fresh state))
    (hcache : let runtime := root.windowed deadlineOf binding choice windowOf
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state)) disposition
        (ApplicationImage.conditionalTransport spec.secretTy)
      ChoiceEncoding.cachedValue runtime.application
        (encoding.submission runtime.application) (execution.principalHistory who) = none)
    (hordinary :
      let runtime := root.windowed deadlineOf binding choice windowOf
      players who (execution.principalHistory who)
          (State.observe runtime.application execution.native who) =
        runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile who)
          (execution.principalHistory who)
          (State.observe runtime.application execution.native who)) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
    let sourceSlot := site.sourceField fresh state
    let deadline := deadlineOf (site.choice.publicationNode fresh state)
    let encoding := site.choiceEncodingFor fresh state sourceSlot deadline disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    let choices := profile who site.choice.decision
      ((current.current.source.toView who).eraseEnv)
    (players who (execution.principalHistory who)
        (State.observe runtime.application execution.native who) =
      choices.map fun chosen => .submit (encoding.encode chosen.1)) ∧
    ∀ environment schedule,
      (runtime.application.runPolicies players environment (.player who :: schedule)
        execution).map
          (fun next => ((encoding.submission runtime.application).cachedValue
            runtime.application (next.principalHistory who), next)) =
        choices.bind fun chosen =>
          ((runtime.application.playerStep who execution
            (.submit (encoding.encode chosen.1))).bind
              (runtime.application.runPolicies players environment schedule)).map
                (fun next => (some chosen.1, next)) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
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
    continuation.windowed_ownerReadout?_of_ready_source_view deadlineOf binding choice
      windowOf who players hcommands priorEnvironment previous execution hreached
      site.choice.decision current.current.graph.1 hrefines hready hinitial
      current.current.source (BuildState.Agrees.view current.current.agrees who)
  have hreadyDisposition := ConditionalPublicationSite.readyDisposition_at_source_prefix
    guard tail spec fresh state sourceSlot deadline current execution.native.application.base
    hrefines disposition hbinding hcanonical
  have hreadyDisposition' : (site.runtimeSite fresh state sourceSlot deadline).readyDisposition
      (some disposition) execution.native.application.base.memory.done = true := by
    change (site.code fresh state sourceSlot deadline).binding?
      execution.native.application.base.memory = some disposition at hbinding
    change (site.runtimeSite fresh state sourceSlot deadline).readyDisposition
      ((site.code fresh state sourceSlot deadline).binding?
        execution.native.application.base.memory)
      execution.native.application.base.memory.done = true at hreadyDisposition
    rw [hbinding] at hreadyDisposition
    exact hreadyDisposition
  have hresolved : execution.native.application.base.memory.done
      (site.choice.publicationNode fresh state) = false := by
    have hr := PublicChoiceSite.ready_at_source_prefix guard tail fresh state current
      execution.native.application.base.memory.done hrefines.memory.completed
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hr
    exact hr.1.2
  have hbase : root.liftProfile deadlineOf rootProfile who
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (runtime.eraseView (State.observe runtime.application execution.native who)) =
        choices.map fun chosen => .submit (encoding.encode chosen.1) := by
    unfold ApplicationPlan.liftProfile
    change root.liftProfileIn (root.image deadlineOf) deadlineOf rootProfile who
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (State.observe (root.image deadlineOf).application
        (runtime.eraseState execution.native) who) = _
    rw [continuation.liftProfileIn_eq_of_refines (root.image deadlineOf) deadlineOf current
      (runtime.eraseState execution.native) hrefines who
      ((execution.principalHistory who).map runtime.erasePlayerEntry)]
    rw [head.liftProfileIn (root.image deadlineOf) deadlineOf profile
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (State.observe (root.image deadlineOf).application
        (runtime.eraseState execution.native) who) hresolved]
    have hreadoutRoot : (root.image deadlineOf).ownerReadout? who
        (site.choice.compiledGuard fresh state).choiceReads
        ((execution.principalHistory who).map runtime.erasePlayerEntry)
        (runtime.eraseView (State.observe runtime.application execution.native who)) =
          some reads := by
      rw [← runtime.ownerReadout?_erasePlayerEntry (root.image deadlineOf)]
      exact hreadout
    exact site.imagePolicy_first_submission_source_law fresh state sourceSlot deadline
      (root.image deadlineOf) disposition
      ((root.image deadlineOf).ownerReadout? who
        (site.choice.compiledGuard fresh state).choiceReads)
      (profile who site.choice.decision) (fun _ _ => false)
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (runtime.eraseView (State.observe runtime.application execution.native who))
      current.current.graph.1.store current.current.source reads hbinding hresolved
      (by
        have hfresh := hcache
        change (encoding.submission runtime.application).cachedValue runtime.application
          (execution.principalHistory who) = none at hfresh
        change (encoding.submission (root.image deadlineOf).application).cachedValue
          (root.image deadlineOf).application
          ((execution.principalHistory who).map fun entry =>
            show (root.image deadlineOf).application.PlayerEntry from
              runtime.erasePlayerEntry entry) = none
        exact (runtime.cachedValue_erasePlayerEntry (root.image deadlineOf) encoding
          (execution.principalHistory who)).symm.trans hfresh)
      hreadyDisposition' hreadoutRoot
      (BuildState.Agrees.view current.current.agrees who) hreads
  have hcommand : players who (execution.principalHistory who)
      (State.observe runtime.application execution.native who) =
        choices.map fun chosen => .submit (encoding.encode chosen.1) := by
    rw [hordinary]
    unfold WindowedApplication.liftPlayerPolicy
    rw [hbase]
    simp only [FinDist.map_comp, Function.comp_def, WindowedApplication.liftPlayerCommand]
  refine ⟨hcommand, ?_⟩
  intro environment schedule
  have hjoint := (encoding.submission runtime.application).runPolicies_sample_joint
    runtime.application who players environment schedule execution (choices.map Subtype.val)
    (by simpa only [FinDist.map_comp, Function.comp_def, ChoiceEncoding.submission]
      using hcommand) hcache
  rw [FinDist.bind_map] at hjoint
  exact hjoint

end Vegas.ApplicationPlan.ProfileContinuation

/-- info:
'Vegas.ApplicationPlan.ProfileContinuation.windowedConditional_sample_of_unchanged_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.ProfileContinuation.windowedConditional_sample_of_unchanged_owner

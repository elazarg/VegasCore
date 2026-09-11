/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedApplication
import Vegas.Compile.WindowedApplicationInvariants
import Vegas.Compile.ApplicationPlanDeadlines
import Vegas.Compile.ApplicationBindingTimeoutRefinement
import Vegas.Compile.ApplicationSourceOutcome

/-! # Source safety of activation-relative generated applications

At each actual handler call, the stable activation determines a retimed
generated image with the same source graph. Existing local refinement applies
to that image, including both optional fallback families. Arbitrary policy runs
therefore retain a reachable graph witness, and a finished run has a matching
written-order source outcome. These are support results, not progress or
outcome-law comparisons of source and target policies.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {build : BuildState P L Γ}

/-- Compile the optional fallback image under an explicit relative-window
policy. The supplied window policy supersedes every existing absolute deadline. -/
def windowed (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) : WindowedApplication P L :=
  ⟨((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts choice, windowOf⟩

/-- Every supported generated windowed-policy run retains the original graph's
reachability invariant. The optional fallback selectors are arbitrary; binding
legality follows from the backend's unrestricted-binding condition, while
public-choice guards are checked by the actual handler. -/
theorem windowed_runPolicies_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (initial : VEnv L Γ) (legal : Legal prog)
    (players : P → (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (state next : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      state.native.application.base.Refines cfg)
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule state).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph,
      next.native.application.base.Refines cfg := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  apply runtime.application.runPolicies_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.base.Refines cfg)
    _ _ _ players environment schedule state next hstate hnext
  · rintro native who command ⟨cfg, hrefines⟩
    cases command with
    | register slot value => exact ⟨cfg, hrefines.register who slot value⟩
  · rintro native message updated ⟨cfg, hrefines⟩ hupdated
    obtain ⟨activation, base, _, _, hbase, rfl⟩ :=
      runtime.handle_some native updated message hupdated
    have hraw := (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment native.base base message hbase
    change (ApplicationImage.withDeadlines
      (((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts choice)
      (fun address => activation.since + windowOf address)).handle
      native.base message = some base at hraw
    rw [plan.image_timeouts_withDeadlines deadlineOf
      (fun address => activation.since + windowOf address) binding choice] at hraw
    obtain ⟨original, horiginal⟩ :=
      ApplicationImage.handle_withChoiceTimeouts_source
        ((plan.image (fun address => activation.since + windowOf address)).withBindingTimeouts
          (retimedBindingSelector (fun address => activation.since + windowOf address) binding))
        (retimedChoiceSelector (fun address => activation.since + windowOf address) choice)
        native.base message base hraw
    exact plan.withBindingTimeouts_handle_refines
      (fun address => activation.since + windowOf address)
      (retimedBindingSelector (fun address => activation.since + windowOf address) binding)
      initial legal native.base base cfg hrefines original horiginal
  · rintro native command updated hnative hupdated
    cases command with
    | advance clock =>
        rw [WindowedApplication.application_advance, FinDist.mem_support_pure] at hupdated
        subst updated
        obtain ⟨cfg, hrefines⟩ := hnative
        exact ⟨cfg, hrefines.advance clock⟩
    | sample address =>
        change updated ∈ ((runtime.image.orderedApplication.environmentStep native.base
          (.sample address)).map (runtime.advanceTo native)).support at hupdated
        simp only [FinDist.support_map, Set.mem_image] at hupdated
        obtain ⟨base, hbase, rfl⟩ := hupdated
        rcases runtime.image.application.withAdmission_environment_support
          runtime.image.admitsMessage runtime.image.admitsEnvironment
          native.base base (.sample address) hbase with rfl | horiginal
        · exact hnative
        · change base ∈
            (ApplicationImage.sample
              (((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts choice)
              native.base address).support at horiginal
          rw [ApplicationImage.sample_withChoiceTimeouts,
            ApplicationImage.sample_withBindingTimeouts] at horiginal
          exact plan.environment_refines deadlineOf native.base (.sample address) base
            hnative horiginal

/-- From canonical generated initialization, arbitrary windowed policies retain
an instruction completion prefix, a resolved disposition for every completed
binding, and consistent activation metadata.  This is a safety statement; it
does not assert that the schedule or service completes the program. -/
theorem windowed_runPolicies_invariants (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : P → (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment : (plan.windowed deadlineOf binding choice
      windowOf).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (next : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
        ((plan.windowed deadlineOf binding choice windowOf).initial
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial (compile source.core).graph)))))).support) :
    (∃ bound ≤ (compile source.core).graph.nodeCount,
      ∀ node, next.native.application.base.memory.done node = true ↔ node < bound) ∧
    (plan.windowed deadlineOf binding choice windowOf).image.ResolvedBindings
      next.native.application.base ∧
    (plan.windowed deadlineOf binding choice windowOf).Consistent
      next.native.application := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  let initialBase := ApplicationImage.State.initial
    (ApplicationImage.Memory.initial (compile source.core).graph)
  let initial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (runtime.initial initialBase))
  have hcoverage : runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes =
      List.range (compile source.core).graph.nodeCount := by
    dsimp only [runtime, windowed, image]
    rw [ApplicationImage.coveredNodes_withChoiceTimeouts,
      ApplicationImage.coveredNodes_withBindingTimeouts]
    simpa only [BuildState.fromInitial, List.length_nil, List.range_zero,
      List.nil_append, compile, BuildResult.graph, Graph.nodeCount] using
        plan.coveredNodes_eq_range deadlineOf
  have hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup := by
    rw [hcoverage]
    exact List.nodup_range
  have hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt
        (initialState source.core.Γ source.core.env source.core.wctx).initialFields.length := by
    dsimp only [runtime, windowed, image]
    apply ApplicationImage.instructions_allocated_withChoiceTimeouts
    apply ApplicationImage.instructions_allocated_withBindingTimeouts
    exact plan.instructions_allocated deadlineOf
  have hnext' : next ∈
      (runtime.application.runPolicies players environment schedule initial).support := by
    exact hnext
  have hcompleted := runtime.runPolicies_completedPrefix hnodup players environment schedule
    initial next (ApplicationImage.CompletedPrefix.initial runtime.image
      (compile source.core).graph) hnext'
  refine ⟨hcompleted.done_iff_lt _ hcoverage, ?_, ?_⟩
  · exact runtime.runPolicies_resolvedBindings
      (initialState source.core.Γ source.core.env source.core.wctx).initialFields.length
      hnodup hallocated players environment schedule initial next
      (ApplicationImage.ResolvedBindings.initial runtime.image (compile source.core).graph) hnext'
  · exact runtime.runPolicies_consistent players environment schedule initial next
      (runtime.initial_consistent initialBase) hnext'

/-- From canonical public initialization, every finished supported windowed run
has the public outcome of an actual source small-step execution. This includes
arbitrary runtime players, public traffic, and both optional timeout families. -/
theorem windowed_runPolicies_source_public_outcome (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : P → (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (next : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (MessageApplication.State.initial _
        ((plan.windowed deadlineOf binding choice windowOf).initial
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial (compile source.core).graph)))))).support)
    (hfinished : next.native.application.base.memory.finished
      (compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      (compile source.core).readPublicTerminal? next.native.application.base.memory =
        some terminalEnv.erasePubEnv := by
  obtain ⟨cfg, hrefines⟩ := plan.windowed_runPolicies_refines deadlineOf binding choice windowOf
    source.core.env source.legal players environment schedule _ next
    ⟨_, ApplicationImage.State.initial_refines (compile source.core).graph⟩ hnext
  exact source_public_outcome_of_refines source.core next.native.application.base cfg
    hrefines hfinished

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.windowed_runPolicies_source_public_outcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_runPolicies_source_public_outcome

/-- info: 'Vegas.ApplicationPlan.windowed_runPolicies_invariants' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_runPolicies_invariants

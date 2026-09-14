/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateSourceLikelihood

/-! # Original source probabilities throughout a candidate replay cylinder

Normalized reference executions retain the original source inputs needed to
compare native draw probabilities. The queried policy need not give positive
mass to the reference realization or to the queried value.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (compilation.supported.resolvingRuntime
    nullValue window).candidateApplication.EnvironmentEntry →
  (compilation.supported.resolvingRuntime
    nullValue window).candidateApplication.EnvironmentObservation →
  (compilation.supported.resolvingRuntime
    nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- Every reference realization supplies the original policy's kernel at each
fresh honest preparation before timeout. The complete native prefix is fixed,
but unprepared source choices are still drawn from their original kernels. -/
theorem restrictedCandidateSourceRun_registration_kernel
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let tracePrefix := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∀ cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator environment
      schedule fallback ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        (fun handle => (tracePrefix.last.native.application.service.lookup handle).opening?)).apply
          profile)).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.candidateValuePlayers nullValue window reference focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who) (State.observe runtime.candidateApplication
            stopped.native who)).support →
      ∀ policy : SourceBehavioralPolicy source.core.prog who,
      ∃ (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
        (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = .fresh ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        compilation.compileCandidatePolicy nullValue window who policy
          (stopped.principalHistory who) (State.observe runtime.candidateApplication
            stopped.native who) =
          ((compileSourcePolicy source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
            rfl who policy) node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (compilation.supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro runtime tracePrefix cfg hcfg stopped hclear who hwho slot value hcommand policy
  have hreplay := compilation.restrictedCandidateSourceRun_replay_prefix nullValue window focal
    deviator environment schedule fallback reference
    (fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty) profile cfg hcfg
  have hkernel := compilation.extractedCandidateSourceRun_registration_kernel nullValue window
    focal deviator environment schedule fallback _ cfg hcfg release
  dsimp only at hkernel
  rw [hreplay] at hkernel
  rw [SealedFragment.candidateValuePlayers, Profile.update_of_ne _ _ hwho] at hcommand
  obtain ⟨node, guard, hsem, reads, hslot, _, _, hselected⟩ :=
    compilation.supported.selected_registration_kernel who
      stopped.native.application.visible.timeouts
      (compilation.supported.valuePolicy reference who)
      (runtime.eventHistory (runtime.registeredPlayerHistory (stopped.principalHistory who)))
      (runtime.eventView (runtime.registeredPlayerView
        (State.observe runtime.candidateApplication stopped.native who))) _ slot value hcommand
  have hlaw := hselected (compilation.supported.valuePolicy (cfg.1.nodeValues fallback) who)
  change runtime.candidatePlayerPolicy (compilation.supported.resolvingPolicy nullValue window
    who (compilation.supported.valuePolicy (cfg.1.nodeValues fallback) who))
      (stopped.principalHistory who) (State.observe runtime.candidateApplication stopped.native who)
        = _ at hlaw
  apply hkernel hclear who hwho slot (cfg.1.nodeValues fallback node) ?_ policy
  rw [SealedFragment.candidateValuePlayers, Profile.update_of_ne _ _ hwho, hlaw]
  simp only [SealedFragment.valuePolicy, FinDist.map_pure, cast_cast, cast_eq, hslot,
    FinDist.mem_support_pure]

/-- Native preparation probabilities equal the original written-source
decision probabilities at every reference realization's recorded view. -/
theorem restrictedCandidateSourceRun_registration_probability
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let tracePrefix := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∀ cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator environment
      schedule fallback ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        (fun handle => (tracePrefix.last.native.application.service.lookup handle).opening?)).apply
          profile)).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.candidateValuePlayers nullValue window reference focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who) (State.observe runtime.candidateApplication
            stopped.native who)).support →
    ∀ policy : SourceBehavioralPolicy source.core.prog who,
    ∃ final, observeSourceOutcome source.core cfg = some final ∧
      ∃ Δ name choiceTy guard, ∃ site :
        SourceDecisionSite who source.core.prog Δ name choiceTy guard,
        site.depth = slot ∧ ∀ chosen,
          (compilation.compileCandidatePolicy nullValue window who policy
            (stopped.principalHistory who)
            (State.observe runtime.candidateApplication stopped.native who)).prob
              (.privateCommand ⟨(slot, chosen)⟩) =
            ((policy site ((site.recorded final).tail.toView who).eraseEnv).map
              (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))).prob ⟨ty, chosen⟩ := by
  intro runtime tracePrefix cfg hcfg stopped hclear who hwho slot value hcommand policy
  obtain ⟨node, guard, hsem, reads, hslot, _, hreads, hkernel⟩ :=
    compilation.restrictedCandidateSourceRun_registration_kernel nullValue window focal deviator
      environment schedule fallback reference profile release cfg hcfg hclear who hwho
      slot value hcommand policy
  have hterminal := compilation.sourceRunOfDisclosures_terminal focal _ _ cfg hcfg
  obtain ⟨final, hobserve, Δ, name, choiceTy, sourceGuard, site, hdepth, hprob⟩ :=
    compilation.sourcePolicy_encoded_probability
      (fun chosen =>
        (.privateCommand ⟨(slot, chosen)⟩ : runtime.candidateApplication.PlayerCommand))
      (by
        intro left right h
        exact congrArg (fun request => request.down.2)
          (MessageInterface.PlayerCommand.privateCommand.inj h))
      who policy node guard hsem cfg hterminal reads hreads
  refine ⟨final, hobserve, Δ, name, choiceTy, sourceGuard, site, hdepth.trans hslot.symm, ?_⟩
  intro chosen
  rw [hkernel]
  simpa only [hslot] using hprob chosen

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.restrictedCandidateSourceRun_registration_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.restrictedCandidateSourceRun_registration_probability

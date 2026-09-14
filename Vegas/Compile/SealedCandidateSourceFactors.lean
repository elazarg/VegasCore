/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateReferenceKernel

/-! # Candidate source cylinders as native preparation products

Each fixed factor is the original honest policy's probability at a genuine
preparation checkpoint. The source restriction's likelihood is constant over
its normalized reference law, so summation yields their finite product. This
is the source side of the comparison with the native runner's trace mass.
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
variable (schedule : List (@Invocation Player))

/-- An honest recorded opening contributes its original policy probability
at the preparation checkpoint. Focal, fresh, and unopenable slots contribute one. -/
def candidateReplayRegistrationFactor
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player) (slot : Nat) : ℝ :=
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let trace := compilation.supported.candidateReplay nullValue window reference focal
    deviator environment schedule
  let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  if who = focal then 1 else
    match ((trace.prefixThrough stop).last.native.application.service.lookup (who, slot)).opening?
        with
    | none => 1
    | some value =>
        let selected := runtime.candidateApplication.commandCheckpoint
          (compilation.supported.candidateValuePlayers nullValue window reference focal
            (fun history view => FinDist.pure (deviator history view))) trace stop who
              (.privateCommand ⟨(slot, value)⟩)
        (compilation.compileCandidatePolicy nullValue window who (profile who)
          (selected.principalHistory who)
          (State.observe runtime.candidateApplication selected.native who)).prob
            (.privateCommand ⟨(slot, value)⟩)

variable (fallback : L.Val ty)

omit [Fintype Player] in
/-- Every normalized reference source realization has the same preparation
likelihood. Its factors are fixed native checkpoint probabilities, not draws
resampled after observing a source outcome. -/
theorem restrictedCandidateSourceRun_weight_eq_product [Finite Player]
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stopped := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    let recorded := fun handle => (stopped.last.native.application.service.lookup handle).opening?
    let restriction := compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
      recorded
    let original : SourceBehavioralProfile source.core.prog :=
      Profile.update (sig := sourceGameSignature source.core.prog) profile focal
        (compilation.extractedCandidateSourcePolicy nullValue window focal deviator environment
          schedule fallback)
    ∀ final ∈ (denoteSource source.core.prog (restriction.apply original) source.core.env).support,
      restriction.weight original source.core.env final =
        (source.core.prog.decisionPositions.map fun slot =>
          compilation.candidateReplayRegistrationFactor nullValue window focal deviator environment
            schedule reference profile slot.1 slot.2).prod := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  intro runtime stopped recorded restriction original final hfinal
  have hrealization := compilation.restrictedCandidateSourceRun_source nullValue window focal
    deviator environment schedule fallback recorded profile
  have hsome : some final ∈ ((denoteSource source.core.prog (restriction.apply original)
      source.core.env).map some).support := by
    rw [FinDist.support_map]
    exact ⟨final, hfinal, rfl⟩
  rw [← hrealization, FinDist.support_map] at hsome
  obtain ⟨cfg, hcfg, hobserve⟩ := hsome
  apply compilation.recordedChoiceRestriction_weight_eq_product
    (fun who => decide (who ≠ focal)) recorded original _ final hfinal
  · intro who slot hunit
    by_cases hwho : who = focal
    · simp only [candidateReplayRegistrationFactor, if_pos hwho]
    · have hlookup : recorded (who, slot) = none := by
        rcases hunit with hselected | hlookup
        · simp [hwho] at hselected
        · exact hlookup
      simp only [candidateReplayRegistrationFactor, if_neg hwho]
      dsimp only [recorded, stopped] at hlookup
      erw [hlookup]
  · intro who Δ name choiceTy guard site hselected value hlookup
    have hwho : who ≠ focal := by simpa using hselected
    let trace := compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let players := compilation.supported.candidateValuePlayers nullValue window reference focal
      (fun history view => FinDist.pure (deviator history view))
    let release := fun execution : runtime.candidateApplication.PolicyExecution =>
      !stop execution && decide (.privateCommand ⟨(site.depth, value)⟩ ∈
        (players who (execution.principalHistory who)
          (State.observe runtime.candidateApplication execution.native who)).support)
    have htrace : trace ∈ (runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support := by
      rw [compilation.supported.candidateReplay_law, FinDist.mem_support_pure]
    have hselected := runtime.candidateRegistrationCheckpoint_selected players
      (fun history view => FinDist.pure (environment history view)) schedule _ trace htrace stop
      who site.depth value (by intro h; cases h)
      (CommitmentCandidate.opening?_eq_some_iff _ _ |>.mp hlookup)
    have hclear : (stopped.firstRelease release).native.application.visible.timeouts = [] := by
      simpa only [MessageApplication.commandCheckpoint, stop, Bool.not_eq_eq_eq_not,
        Bool.not_false, List.isEmpty_iff] using hselected.1
    obtain ⟨outcome, houtcome, ctx, label, actionTy, sourceGuard, actual, hdepth, hprob⟩ :=
      compilation.restrictedCandidateSourceRun_registration_probability nullValue window focal
        deviator environment schedule fallback reference profile release cfg hcfg hclear who
        hwho site.depth value hselected.2 (profile who)
    have heq : outcome = final := Option.some.inj (houtcome.symm.trans hobserve)
    subst outcome
    obtain ⟨rfl, rfl, rfl, hguard, hsite⟩ := actual.indices_eq_of_depth_eq site hdepth
    cases eq_of_heq hguard
    cases eq_of_heq hsite
    simp only [candidateReplayRegistrationFactor, if_neg hwho, original,
      Profile.update_of_ne _ _ hwho]
    dsimp only [recorded, stopped] at hlookup
    erw [hlookup]
    exact hprob value

/-- Exact source probability of the candidate prefix through first timeout
as a product of original native preparation probabilities. Native trace-mass
equality requires the separate invocation-counting argument. -/
theorem extractedCandidateSourceRun_replay_prob_eq_product
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough stop
    ((compilation.extractedCandidateSourceRun nullValue window focal deviator environment schedule
      fallback profile).map fun cfg =>
        (compilation.supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop).prob stopped =
      (source.core.prog.decisionPositions.map fun slot =>
        compilation.candidateReplayRegistrationFactor nullValue window focal deviator environment
          schedule reference profile slot.1 slot.2).prod := by
  intro runtime stop stopped
  rw [compilation.extractedCandidateSourceRun_replay_likelihood]
  exact (FinDist.expect_congr (compilation.restrictedCandidateSourceRun_weight_eq_product
    nullValue window focal deviator environment schedule fallback reference profile)).trans
      (FinDist.expect_const _ _)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_replay_prob_eq_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_replay_prob_eq_product

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateCylinder
import Vegas.Compile.SealedCandidateSourceExtraction
import Vegas.Compile.SealedSourceChoices

/-! # Written-source likelihood of candidate replay

The source event fixes exactly the honest preparations recorded by a replay
prefix. Candidate identities used by the deviator remain unrestricted. The
source restriction calculation is shared with other hosts and retains the
original opponent kernels, including their dependence on earlier choices.
The native runner's probability law is a separate comparison.
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

/-- Fixing recorded honest choices leaves the extracted source deviator
unchanged. The reference law is normalized even for zero-mass cylinders. -/
theorem restrictedCandidateSourceRun_source
    (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedCandidateSourceRun nullValue window focal deviator environment schedule
      fallback ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        recorded).apply profile)).map (observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal)) recorded).apply
          (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
            (compilation.extractedCandidateSourcePolicy nullValue window focal deviator
              environment schedule fallback))) source.core.env).map some := by
  rw [compilation.extractedCandidateSourceRun_source,
    compilation.recordedChoiceRestriction_apply_update _ focal (by simp)]

/-- Every reference source realization reproduces the full candidate prefix.
Only recorded honest preparations are forced; no positive-probability premise
is imposed on the original profile. -/
theorem restrictedCandidateSourceRun_replay_prefix
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    let recorded := fun handle => (stopped.last.native.application.service.lookup handle).opening?
    ∀ cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator environment
      schedule fallback ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        recorded).apply profile)).support,
      (compilation.supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).prefixThrough release = stopped := by
  intro stopped recorded cfg hcfg
  let restriction := compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
    recorded
  let original : SourceBehavioralProfile source.core.prog :=
    Profile.update (sig := sourceGameSignature source.core.prog) profile focal
      (compilation.extractedCandidateSourcePolicy nullValue window focal deviator environment
        schedule fallback)
  have hterminal := compilation.sourceRunOfDisclosures_terminal focal _
    (restriction.apply profile) cfg hcfg
  let final := decodeSourceOutcome source.core.prog source.core.fresh
    (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
    cfg hterminal
  have hobserve : observeSourceOutcome source.core cfg = some final :=
    observeSourceOutcome_of_terminal source.core cfg hterminal
  have hfinal : final ∈
      (denoteSource source.core.prog (restriction.apply original) source.core.env).support := by
    have hmapped : some final ∈
        ((compilation.extractedCandidateSourceRun nullValue window focal deviator environment
          schedule fallback (restriction.apply profile)).map
            (observeSourceOutcome source.core)).support := by
      rw [FinDist.support_map]
      exact ⟨cfg, hcfg, hobserve⟩
    rw [compilation.restrictedCandidateSourceRun_source, FinDist.support_map] at hmapped
    obtain ⟨actual, hactual, heq⟩ := hmapped
    exact Option.some.inj heq ▸ hactual
  have hallowed := denoteSource_restriction_support source.core.prog original restriction
    source.core.env final hfinal
  have hvalues := (compilation.recordedChoiceRestriction_allows_iff_nodeValues
    (fun who => decide (who ≠ focal)) recorded (restriction.apply original) fallback cfg
      hterminal hfinal).mp hallowed
  apply Eq.symm
  apply (compilation.supported.candidateReplay_prefix_eq_iff_lookup nullValue window focal
    deviator environment schedule release reference (cfg.1.nodeValues fallback)).mpr
  intro who node guard hsem hwho value hlookup
  exact hvalues who node guard hsem (by simp [hwho]) value
    (CommitmentCandidate.opening?_eq_some_iff _ _ |>.mpr hlookup)

/-- Exact source probability of a stopped candidate replay, expressed as a
written-source recorded-choice event. This is not yet a native marginal law. -/
theorem extractedCandidateSourceRun_replay_probability
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    ((compilation.extractedCandidateSourceRun nullValue window focal deviator environment schedule
      fallback profile).map fun cfg =>
        (compilation.supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough release).prob stopped =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.extractedCandidateSourcePolicy nullValue window focal deviator environment
            schedule fallback)) source.core.env).probOf
        {final | (compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
          (fun handle => (stopped.last.native.application.service.lookup handle).opening?)).Allows
            source.core.env final} := by
  intro stopped
  apply compilation.replay_probability_of_recorded_choices _ _
    (compilation.extractedCandidateSourceRun_source nullValue window focal deviator environment
      schedule fallback profile)
    (compilation.sourceRunOfDisclosures_terminal focal _ profile) _ _ fallback
  intro cfg _hcfg
  rw [eq_comm, compilation.supported.candidateReplay_prefix_eq_iff_lookup]
  simp only [decide_eq_true_eq, CommitmentCandidate.opening?_eq_some_iff, stopped]

/-- Sum the candidate replay cylinder using the original source likelihood
under its normalized recorded-choice restriction. Correlation and zero
probability require no additional hypotheses. -/
theorem extractedCandidateSourceRun_replay_likelihood
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    let original : SourceBehavioralProfile source.core.prog :=
      Profile.update (sig := sourceGameSignature source.core.prog) profile focal
        (compilation.extractedCandidateSourcePolicy nullValue window focal deviator environment
          schedule fallback)
    let restriction := compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
      (fun handle => (stopped.last.native.application.service.lookup handle).opening?)
    ((compilation.extractedCandidateSourceRun nullValue window focal deviator environment schedule
      fallback profile).map fun cfg =>
        (compilation.supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough release).prob stopped =
      (denoteSource source.core.prog (restriction.apply original) source.core.env).expect
        (restriction.weight original source.core.env) := by
  intro stopped original restriction
  exact (compilation.extractedCandidateSourceRun_replay_probability nullValue window focal
    deviator environment schedule fallback reference release profile).trans
      (denoteSource_restriction_probability source.core.prog original restriction source.core.env)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.restrictedCandidateSourceRun_replay_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.restrictedCandidateSourceRun_replay_prefix

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_replay_likelihood'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_replay_likelihood

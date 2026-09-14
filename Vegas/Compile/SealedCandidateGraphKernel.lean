/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateRealization
import Vegas.Compile.SealedCandidateGraphLikelihood

/-! # Original graph kernels throughout a candidate replay cylinder

Normalized reference graph executions retain the declared inputs needed to
compare native draw probabilities. The queried graph policy need not give
positive mass to the reference realization or to the queried value.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- Restricting the honest preparations of a replay prefix reproduces that
prefix with the extracted graph deviator unchanged. -/
theorem restrictedCandidateGraphRun_replay_prefix
    (reference : Fin G.nodeCount → L.Val ty)
    (release : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution →
      Bool) (profile : CommitPolicyProfile G) :
    let stopped := (supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    let recorded := fun handle => (stopped.last.native.application.service.lookup handle).opening?
    ∀ cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment
      schedule fallback ((supported.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        recorded).apply profile)).support,
      (supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).prefixThrough release = stopped := by
  intro stopped recorded cfg hcfg
  apply supported.restrictedGraphRun_candidateReplay_prefix nullValue window focal
    deviator environment schedule hguards reference release fallback
    (Profile.update (sig := ⟨CommitPolicy G, ReachableConfig G⟩) profile focal
      (supported.extractedCandidateCommitPolicy hinfo nullValue window focal deviator
        environment schedule fallback)) cfg
  rw [recordedChoiceRestriction_apply_update _ _ focal (by simp)]
  exact hcfg

/-- Every reference realization supplies the original policy's kernel at each
fresh honest preparation before timeout. The complete native prefix is fixed,
but unprepared graph choices are still drawn from their original kernels. -/
theorem restrictedCandidateGraphRun_registration_kernel
    (reference : Fin G.nodeCount → L.Val ty)
    (profile : CommitPolicyProfile G)
    (release : (supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let runtime := supported.resolvingRuntime nullValue window
    let tracePrefix := (supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∀ cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment
      schedule fallback ((supported.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        (fun handle => (tracePrefix.last.native.application.service.lookup handle).opening?)).apply
          profile)).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (supported.candidateValuePlayers nullValue window reference focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who) (State.observe runtime.candidateApplication
            stopped.native who)).support →
      ∀ policy : CommitPolicy G who,
      ∃ (node : Fin G.nodeCount) (guard : EventGuard L)
        (hsem : (G.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = .fresh ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        runtime.candidatePlayerPolicy (supported.resolvingPolicy nullValue window who policy)
          (stopped.principalHistory who) (State.observe runtime.candidateApplication
            stopped.native who) =
          (policy node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro runtime tracePrefix cfg hcfg stopped hclear who hwho slot value hcommand policy
  have hreplay := supported.restrictedCandidateGraphRun_replay_prefix hinfo hguards nullValue
    window focal deviator environment schedule fallback reference
    (fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty) profile cfg hcfg
  have hkernel := supported.candidateGraphRun_registration_kernel hinfo hguards nullValue window
    focal deviator environment schedule fallback _ cfg hcfg release
  dsimp only at hkernel
  rw [hreplay] at hkernel
  rw [SealedFragment.candidateValuePlayers, Profile.update_of_ne _ _ hwho] at hcommand
  obtain ⟨node, guard, hsem, reads, hslot, _, _, hselected⟩ :=
    supported.selected_registration_kernel who
      stopped.native.application.visible.timeouts
      (supported.valuePolicy reference who)
      (runtime.eventHistory (runtime.registeredPlayerHistory (stopped.principalHistory who)))
      (runtime.eventView (runtime.registeredPlayerView
        (State.observe runtime.candidateApplication stopped.native who))) _ slot value hcommand
  have hlaw := hselected (supported.valuePolicy (cfg.1.nodeValues fallback) who)
  change runtime.candidatePlayerPolicy (supported.resolvingPolicy nullValue window
    who (supported.valuePolicy (cfg.1.nodeValues fallback) who))
      (stopped.principalHistory who) (State.observe runtime.candidateApplication stopped.native who)
        = _ at hlaw
  apply hkernel hclear who hwho slot (cfg.1.nodeValues fallback node) ?_ policy
  rw [SealedFragment.candidateValuePlayers, Profile.update_of_ne _ _ hwho, hlaw]
  simp only [SealedFragment.valuePolicy, FinDist.map_pure, cast_cast, cast_eq, hslot,
    FinDist.mem_support_pure]

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.restrictedCandidateGraphRun_registration_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.restrictedCandidateGraphRun_registration_kernel

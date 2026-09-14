/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateCylinder
import Vegas.Compile.SealedGraphRestriction
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Candidate replay probabilities under graph policies

An arbitrary graph profile supplies the assignment law. The probability of a
native replay prefix is its recorded-choice likelihood under the normalized
restricted graph profile. This is the graph side of the native-law comparison;
it does not yet identify replay with randomized native policy execution.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

/-- Every reference graph realization reproduces the same full native replay
prefix, even if that prefix has zero mass under the original graph profile. -/
theorem restrictedGraphRun_candidateReplay_prefix (hguards : GuardLive G)
    (reference : Fin G.nodeCount → L.Val ty)
    (release : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution →
      Bool) (fallback : L.Val ty) (profile : CommitPolicyProfile G) :
    let stopped := (supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    let restriction := supported.recordedChoiceRestriction (fun who => decide (who ≠ focal))
      (fun handle => (stopped.last.native.application.service.lookup handle).opening?)
    ∀ cfg ∈ (runPolicyNodes supported.graphWF hguards (restriction.apply profile)
      ⟨Config.initial G, .initial⟩ G.nodeOrder).support,
      (supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).prefixThrough release = stopped := by
  intro stopped restriction cfg hcfg
  have hterminal := runPolicyNodes_terminal supported.graphWF hguards (restriction.apply profile)
    ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) cfg hcfg
  have hallows := runPolicyNodes_restriction_support supported.graphWF hguards profile restriction
    ⟨Config.initial G, .initial⟩ (CommitValuesSupported.initial _) G.nodeOrder
    G.nodeOrder_readyOrder cfg hcfg
  have hvalues := (supported.recordedChoiceRestriction_allows_iff_nodeValues _ _ cfg hterminal
    fallback).mp hallows
  apply Eq.symm
  apply (supported.candidateReplay_prefix_eq_iff_lookup nullValue window focal deviator environment
    schedule release reference (cfg.1.nodeValues fallback)).mpr
  intro who node guard hsem hwho value hlookup
  exact hvalues who node guard hsem (by simp [hwho]) value
    (CommitmentCandidate.opening?_eq_some_iff _ _ |>.mpr hlookup)

/-- The graph's own restriction law computes the complete native replay
prefix mass, retaining dependent honest choices and zero-mass cylinders. The
graph profile is arbitrary; no source compilation premise is required. -/
theorem candidateReplay_graph_likelihood (hguards : GuardLive G)
    (reference : Fin G.nodeCount → L.Val ty)
    (release : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution →
      Bool) (fallback : L.Val ty) (profile : CommitPolicyProfile G) :
    let stopped := (supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    let restriction := supported.recordedChoiceRestriction (fun who => decide (who ≠ focal))
      (fun handle => (stopped.last.native.application.service.lookup handle).opening?)
    ((runPolicyNodes supported.graphWF hguards profile ⟨Config.initial G, .initial⟩
      G.nodeOrder).map fun cfg =>
        (supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough release).prob stopped =
      (runPolicyNodes supported.graphWF hguards (restriction.apply profile)
        ⟨Config.initial G, .initial⟩ G.nodeOrder).expect
          (fun cfg => restriction.weight profile G.nodeOrder cfg.1) := by
  classical
  intro stopped restriction
  rw [FinDist.prob_map_eq_probOf_preimage_singleton]
  calc
    _ = (runPolicyNodes supported.graphWF hguards profile ⟨Config.initial G, .initial⟩
        G.nodeOrder).probOf {cfg | restriction.Allows G.nodeOrder cfg.1} := by
      apply FinDist.probOf_congr
      intro cfg hcfg
      have hterminal := runPolicyNodes_terminal supported.graphWF hguards profile
        ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder
        (fun node => Or.inr (by simp)) cfg hcfg
      rw [Set.mem_preimage, Set.mem_singleton_iff, eq_comm,
        supported.candidateReplay_prefix_eq_iff_lookup nullValue window focal deviator
          environment schedule release reference (cfg.1.nodeValues fallback)]
      rw [Set.mem_ofPred_eq,
        supported.recordedChoiceRestriction_allows_iff_nodeValues _ _ cfg hterminal fallback]
      simp only [decide_eq_true_eq, CommitmentCandidate.opening?_eq_some_iff, stopped]
    _ = _ := runPolicyNodes_restriction_probability supported.graphWF hguards profile
      restriction ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateReplay_graph_likelihood'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateReplay_graph_likelihood

/-- info: 'Vegas.EventGraph.SealedFragment.restrictedGraphRun_candidateReplay_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.restrictedGraphRun_candidateReplay_prefix

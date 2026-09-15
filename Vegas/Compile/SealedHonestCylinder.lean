/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedGraphRestriction
import Vegas.Compile.SealedAssignedReplay
import Vegas.Compile.SealedSourceInputs
import GameTheoryExtensions.Math.Probability.FinDist

/-! # All-player graph cylinders for pending-message replay

Fixing the registered values selects exactly the graph realizations that replay
the same native prefix. All original graph kernels remain in the assignment law;
there is no focal replacement or source-image assumption.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hguards : GuardLive G)
variable (nullValue : L.Val ty) (window : Nat)
variable (environment :
  List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- Restricting every occupied graph site reproduces the full assigned replay
prefix, including histories, pending packets, and public clock state. -/
theorem restrictedGraphRun_assignedReplay_prefix
    (reference : Fin G.nodeCount → L.Val ty)
    (release : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
      Bool) (profile : CommitPolicyProfile G) :
    let stopped := (supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough release
    let restriction := supported.recordedChoiceRestriction (fun _ => true)
      stopped.last.native.application.service.lookup
    ∀ cfg ∈ (runPolicyNodes supported.graphWF hguards (restriction.apply profile)
      ⟨Config.initial G, .initial⟩ G.nodeOrder).support,
      (supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
        environment schedule).prefixThrough release = stopped := by
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
  apply (supported.resolvingAssignedReplay_prefix_eq_iff_lookup nullValue window environment
    schedule release reference (cfg.1.nodeValues fallback)).mpr
  exact fun who node guard hsem value hlookup => hvalues who node guard hsem rfl value hlookup

/-- The graph's restriction law computes the assigned replay prefix mass,
including prefixes having zero probability under the original profile. -/
theorem assignedReplay_graph_likelihood
    (reference : Fin G.nodeCount → L.Val ty)
    (release : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
      Bool) (profile : CommitPolicyProfile G) :
    let stopped := (supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough release
    let restriction := supported.recordedChoiceRestriction (fun _ => true)
      stopped.last.native.application.service.lookup
    ((runPolicyNodes supported.graphWF hguards profile ⟨Config.initial G, .initial⟩
      G.nodeOrder).map fun cfg =>
        (supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
          environment schedule).prefixThrough release).prob stopped =
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
        supported.resolvingAssignedReplay_prefix_eq_iff_lookup nullValue window environment
          schedule release reference (cfg.1.nodeValues fallback)]
      rw [Set.mem_ofPred_eq,
        supported.recordedChoiceRestriction_allows_iff_nodeValues _ _ cfg hterminal fallback]
      simp only [stopped, forall_const]
    _ = _ := runPolicyNodes_restriction_probability supported.graphWF hguards profile
      restriction ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder

/-- Every normalized reference realization supplies the original graph kernel
at an actual fresh preparation checkpoint. No source policy is involved. -/
theorem restrictedGraphRun_assigned_registration_kernel
    (reference : Fin G.nodeCount → L.Val ty) (profile : CommitPolicyProfile G)
    (release : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
      Bool) :
    let runtime := supported.resolvingRuntime nullValue window
    let tracePrefix := (supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough
        (fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    let restriction := supported.recordedChoiceRestriction (fun _ => true)
      tracePrefix.last.native.application.service.lookup
    ∀ cfg ∈ (runPolicyNodes supported.graphWF hguards (restriction.apply profile)
      ⟨Config.initial G, .initial⟩ G.nodeOrder).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (supported.resolvingAssignedPlayers nullValue window reference who
          (stopped.principalHistory who) (State.observe runtime.messageApplication
            stopped.native who)).support →
      ∀ policy : CommitPolicy G who,
      ∃ (node : Fin G.nodeCount) (guard : EventGuard L)
        (hsem : (G.nodeRow node).sem = .commit who guard) (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = none ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        supported.resolvingPolicy nullValue window who policy
          (stopped.principalHistory who) (State.observe runtime.messageApplication
            stopped.native who) =
          (policy node guard hsem reads).map (fun choice =>
            .privateCommand ⟨(node.val, cast (congrArg L.Val
              (supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro runtime tracePrefix restriction cfg hcfg stopped hclear who slot value hcommand policy
  let fallback := nullValue
  let players := supported.resolvingAssignedPlayers nullValue window reference
  let env := fun history view => FinDist.pure (environment history view)
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  let trace := supported.resolvingAssignedReplay nullValue window reference environment schedule
  have htrace : trace ∈
      (runtime.messageApplication.tracePolicies players env schedule initial).support := by
    rw [supported.resolvingAssignedReplay_law, FinDist.mem_support_pure]
  obtain ⟨front, _, _, hprefix⟩ :=
    runtime.messageApplication.tracePolicies_prefixThrough_support players env stop schedule
      initial trace htrace
  obtain ⟨before, after, _, hbefore, hafter⟩ :=
    runtime.messageApplication.tracePolicies_firstRelease_split players env release front initial
      tracePrefix hprefix
  have hterminal := runPolicyNodes_terminal supported.graphWF hguards (restriction.apply profile)
    ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) cfg hcfg
  have hallows := runPolicyNodes_restriction_support supported.graphWF hguards profile restriction
    ⟨Config.initial G, .initial⟩ (CommitValuesSupported.initial _) G.nodeOrder
    G.nodeOrder_readyOrder cfg hcfg
  have hrecorded := (supported.recordedChoiceRestriction_allows_iff_nodeValues _ _ cfg hterminal
    fallback).mp hallows
  have hmemory := SealedResolution.RegistrationMemory.runPolicies players env before initial stopped
    SealedResolution.RegistrationMemory.initial hbefore
  have hbinding := runtime.runPolicies_beforeTimeoutBinding players env before initial stopped
    SealedResolution.BeforeTimeoutBinding.initial hbefore hclear
  apply supported.resolving_registration_kernel cfg hterminal fallback nullValue window
    stopped hclear hmemory (hbinding.copy rfl rfl) ?_ who
    (supported.assignedProposals reference who) policy slot value hcommand
  intro owner node guard hsem registered hlookup
  exact hrecorded owner node guard hsem rfl registered
    (runtime.runPolicies_lookup_of_eq_some players env after stopped tracePrefix.last
      (owner, node.val) registered hlookup hafter)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.assignedReplay_graph_likelihood'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.assignedReplay_graph_likelihood

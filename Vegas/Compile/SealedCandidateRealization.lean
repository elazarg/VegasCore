/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateExtraction
import Vegas.Compile.SealedCandidateValues

/-! # Graph realizations of candidate acceptance replay

One extracted graph policy replaces the focal player, with arbitrary graph
opponents unchanged. Its complete realizations retain openable focal acceptances
and reconstruct each honest native preparation's declared graph inputs.
These are graph/backend facts; source policies and source decoding are absent.
The equality of whole native and graph execution laws is a further comparison.
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

/-- The ordinary graph executor with the extracted candidate policy replacing
one player. All other graph kernels are unchanged. -/
def candidateGraphRun (profile : CommitPolicyProfile G) : FinDist (ReachableConfig G) :=
  supported.runOfDisclosures hinfo hguards focal
    (fun decision visible => supported.extractedCandidateChoice nullValue window
      focal deviator environment schedule decision visible fallback) profile

theorem candidateGraphRun_terminal (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
      environment schedule fallback profile).support) : Terminal G cfg.1 :=
  supported.runOfDisclosures_terminal hinfo hguards focal _ profile cfg hcfg

/-- Every supported complete graph realization agrees with the candidate
selected by replay of its honest values. The graph-input agreement premise
of the local action law is discharged by the graph execution itself. This
does not yet identify the probability law of the replayed native executions. -/
theorem candidateGraphRun_consistent (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
      environment schedule fallback profile).support)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard) :
    cfg.1.nodeValues fallback decision = SealedShape.candidateValue
      (supported.candidateSelection nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule decision) fallback := by
  have hchoice := supported.runOfDisclosures_consistent hinfo hguards focal
    (fun index visible => supported.extractedCandidateChoice nullValue window
      focal deviator environment schedule index visible fallback)
    profile fallback cfg hcfg decision guard hdecision
  exact hchoice.trans (supported.extractedCandidateChoice_eq_selection nullValue
    window (cfg.1.nodeValues fallback) focal deviator environment schedule decision guard
      hdecision fallback)

/-- The complete legal graph realization retains every openable focal
candidate accepted by the common timeout checkpoint. Unaccepted preparations
do not constrain the graph choice. -/
private theorem candidateGraphRun_locked (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
      environment schedule fallback profile).support)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (slot : Nat) (value : L.Val ty)
    (haccepted : SealedProgram.accepted?
      (supported.candidateStop nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).native.application.visible.events decision.val =
          some (focal, slot))
    (hvalue : (supported.candidateStop nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule).native.application.service.lookup (focal, slot) =
        .openable value) : cfg.1.nodeValues fallback decision = value := by
  have hchoice := supported.candidateGraphRun_consistent hinfo hguards nullValue window focal
    deviator environment schedule fallback profile cfg hcfg decision guard hdecision
  rw [SealedShape.candidateSelection_eq_stop _ _ _ _ _ _ _ _ decision guard hdecision] at hchoice
  simpa only [SealedShape.selectedCandidate, haccepted, Option.bind_some, ↓reduceIte,
    hvalue, SealedShape.candidateValue] using hchoice

/-- Every focal acceptance at a checkpoint of the pre-timeout replay has its
complete graph value whenever that candidate is openable. Arbitrary other
preparations and permanently unopenable acceptances remain permitted. -/
private theorem candidateGraphRun_focal_accepted
    (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
      environment schedule fallback profile).support)
    (release : (supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let stopped := ((supported.candidateReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : (supported.resolvingRuntime
          nullValue window).candidateApplication.PolicyExecution =>
            !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    ∀ index slot value,
      SealedProgram.Event.accepted index (focal, slot) ∈
        stopped.native.application.visible.events →
      stopped.native.application.service.lookup (focal, slot) = .openable value →
      cfg.1.store (G.nodeTarget index) =
        some (⟨ty, value⟩ : TypedValue L) := by
  intro stopped index slot value haccepted hvalue
  let runtime := supported.resolvingRuntime nullValue window
  obtain ⟨before, after, hbefore, hafter⟩ := supported.candidateReplay_prefix_support
    nullValue window (cfg.1.nodeValues fallback) focal deviator environment schedule release
  have hacceptance := runtime.runPolicies_candidate_acceptance _ _ before _ stopped
    SealedResolution.CandidateAcceptanceInvariant.initial hbefore
  obtain ⟨hselected, requires, hrule⟩ := hacceptance index (focal, slot) haccepted
  obtain ⟨node, guard, rfl, hsem⟩ := supported.ruleAt_commit hrule rfl
  have hgraph := supported.candidateGraphRun_locked hinfo hguards nullValue window focal
    deviator environment schedule fallback profile cfg hcfg node guard hsem slot value
    (runtime.runPolicies_candidate_accepted? _ _ after stopped _ node.val (focal, slot)
      hselected hafter)
    ((runtime.runPolicies_candidate_lookup_of_not_fresh _ _ after stopped _ (focal, slot)
      (by rw [hvalue]; simp) hafter).trans hvalue)
  have hterminal := supported.candidateGraphRun_terminal hinfo hguards nullValue window focal
    deviator environment schedule fallback profile cfg hcfg
  rw [cfg.1.store_nodeValues (reachable_storeCoherent supported.graphWF cfg.2)
    fallback node (supported.rowType node) (hterminal node), hgraph]

/-- Every openable acceptance in a pre-timeout replay has its complete graph
value. Focal candidates use acceptance-time extraction; honest candidates use
the unchanged generated policies and their actual retained-message provenance. -/
theorem candidateGraphRun_accepted
    (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
      environment schedule fallback profile).support)
    (release : (supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let stopped := ((supported.candidateReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : (supported.resolvingRuntime
          nullValue window).candidateApplication.PolicyExecution =>
            !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    ∀ index handle value,
      SealedProgram.Event.accepted index handle ∈ stopped.native.application.visible.events →
      stopped.native.application.service.lookup handle = .openable value →
      cfg.1.store (G.nodeTarget index) =
        some (⟨ty, value⟩ : TypedValue L) := by
  intro stopped index handle value haccepted hvalue
  by_cases howner : handle.1 = focal
  · have hhandle : handle = (focal, handle.2) := Prod.ext howner rfl
    rw [hhandle] at haccepted hvalue
    exact supported.candidateGraphRun_focal_accepted hinfo hguards nullValue window focal
      deviator environment schedule fallback profile cfg hcfg release index handle.2 value
      haccepted hvalue
  · let runtime := supported.resolvingRuntime nullValue window
    obtain ⟨before, _after, hbefore, _hafter⟩ :=
      supported.candidateReplay_prefix_support nullValue window
        (cfg.1.nodeValues fallback) focal deviator environment schedule release
    have hacceptance := runtime.runPolicies_candidate_acceptance _ _ before _ stopped
      SealedResolution.CandidateAcceptanceInvariant.initial hbefore
    obtain ⟨_hselected, requires, hrule⟩ := hacceptance index handle haccepted
    obtain ⟨node, guard, rfl, _hsem⟩ := supported.ruleAt_commit hrule rfl
    have hhandle := supported.candidatePolicy_accepted_slot nullValue window handle.1
      (supported.assignedProposals (cfg.1.nodeValues fallback) handle.1) _ _
      (by rw [SealedShape.candidateValuePlayers, Profile.update_of_ne _ _ howner])
      before stopped hbefore node.val handle haccepted rfl
    rw [hhandle] at hvalue
    have hgraph := supported.runPolicies_candidateValues_lookup nullValue window
      (cfg.1.nodeValues fallback) focal _ _ before stopped hbefore handle.1 howner node value hvalue
    have hterminal := supported.candidateGraphRun_terminal hinfo hguards nullValue window focal
      deviator environment schedule fallback profile cfg hcfg
    rw [cfg.1.store_nodeValues (reachable_storeCoherent supported.graphWF cfg.2)
      fallback node (supported.rowType node) (hterminal node), ← hgraph]

/-- At every fresh honest preparation in pre-timeout replay, the original
graph policy is evaluated at its exact declared graph inputs. No agreement
of caches, accepted values, or local read environments is assumed by the caller. -/
theorem candidateGraphRun_registration_kernel
    (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
      environment schedule fallback profile).support)
    (release : (supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let runtime := supported.resolvingRuntime nullValue window
    let stopped := ((supported.candidateReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (supported.candidateValuePlayers nullValue window (cfg.1.nodeValues fallback)
          focal (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who) (State.observe _ stopped.native who)).support →
      ∀ policy : CommitPolicy G who,
      ∃ (node : Fin G.nodeCount) (guard : EventGuard L)
        (hsem : (G.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = .fresh ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        runtime.candidatePlayerPolicy (supported.resolvingPolicy nullValue window who policy)
          (stopped.principalHistory who) (State.observe _ stopped.native who) =
          (policy node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro runtime stopped hclear who hwho slot value hcommand policy
  obtain ⟨before, _after, hbefore, _hafter⟩ := supported.candidateReplay_prefix_support
    nullValue window (cfg.1.nodeValues fallback) focal deviator environment schedule release
  have hplayer := Profile.update_of_ne
    (sig := MessageApplication.policySignature Player runtime.candidateApplication)
    (fun owner => runtime.candidatePlayerPolicy (supported.resolvingProposalPolicy nullValue
      window owner (supported.assignedProposals (cfg.1.nodeValues fallback) owner)))
    (fun history view => FinDist.pure (deviator history view)) hwho
  rw [SealedShape.candidateValuePlayers, Profile.update_of_ne _ _ hwho] at hcommand
  have haccepted := supported.candidateGraphRun_accepted hinfo hguards nullValue window focal
    deviator environment schedule fallback profile cfg hcfg release
  have hopening := runtime.runPolicies_candidate_openings _ _ before _ stopped
    SealedResolution.CandidateOpeningInvariant.initial hbefore
  exact supported.candidate_registration_kernel cfg nullValue window
    _ _ before stopped hbefore hclear who _ _ hplayer
    (fun index handle value hrecord _ => haccepted index handle value hrecord)
    (supported.candidate_opened_graph_value cfg
      (supported.candidateGraphRun_terminal hinfo hguards nullValue window focal deviator
        environment schedule fallback profile cfg hcfg) nullValue window
      stopped.native.application hopening hclear haccepted) slot value hcommand

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateGraphRun_registration_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateGraphRun_registration_kernel

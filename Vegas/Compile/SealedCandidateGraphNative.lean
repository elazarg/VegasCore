/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphFactors
import Vegas.EventGraph.CommitPositions
import Interaction.SealedCandidateLikelihood

/-! # Exact graph/native prefixes for candidate pending messages

Actual preparation invocations and their replay checkpoints evaluate unchanged
graph policies at equal declared reads. Counting each fresh preparation once
identifies the entire native prefix law through first timeout, against arbitrary
graph opponents. Source syntax and source-policy backtranslation are not used.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
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
variable (schedule : List (@Invocation Player))

include hinfo hguards

/-- At an actual honest preparation invocation, the slot is a fresh graph
decision and the original policy probability equals its fixed replay factor.
The prefix and suffix premises are ordinary native executions, not assumed
graph/native couplings. -/
theorem candidateReplay_registration_factor
    (reference : Fin G.nodeCount → L.Val ty)
    (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := supported.candidateValuePlayers nullValue window reference focal
      (fun history view => FinDist.pure (deviator history view))
    let env := fun history view => FinDist.pure (environment history view)
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let trace := supported.candidateReplay nullValue window reference focal
      deviator environment schedule
    let stopped := trace.prefixThrough stop
    ∀ before initial who slot value next after,
      who ≠ focal →
      initial ∈ (runtime.candidateApplication.runPolicies players env before
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support →
      .privateCommand ⟨(slot, value)⟩ ∈ (players who (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).support →
      next ∈ (runtime.candidateApplication.playerStep who initial
        (.privateCommand ⟨(slot, value)⟩)).support →
      stopped.last ∈ (runtime.candidateApplication.runPolicies players env after next).support →
      stop initial = false →
      (who, slot) ∈ G.commitPositions ∧
      initial.native.application.service.lookup (who, slot) = .fresh ∧
      (runtime.candidatePlayerPolicy (supported.resolvingPolicy nullValue window who (profile who))
        (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).prob
          (.privateCommand ⟨(slot, value)⟩) =
        supported.candidateReplayRegistrationFactor nullValue window focal deviator environment
          schedule reference profile who slot := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  let fallback := nullValue
  intro runtime players env stop trace stopped before initial who slot value next after
    hwho hbefore hcommand hnext hafter hstop
  let restricted := (supported.recordedChoiceRestriction (fun who => decide (who ≠ focal))
    (fun handle => (stopped.last.native.application.service.lookup handle).opening?)).apply profile
  obtain ⟨cfg, hcfg⟩ := (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
    environment schedule fallback restricted).support_nonempty
  have hterminal := supported.candidateGraphRun_terminal hinfo hguards nullValue window focal
    deviator environment schedule fallback restricted cfg hcfg
  have hreplay := supported.restrictedCandidateGraphRun_replay_prefix hinfo hguards nullValue
    window focal deviator environment schedule fallback reference stop profile cfg hcfg
  have hclear : initial.native.application.visible.timeouts = [] := by
    simpa only [stop, Bool.not_eq_eq_eq_not, Bool.not_false, List.isEmpty_iff] using hstop
  have hrest : stopped.last ∈ (runtime.candidateApplication.runPolicies players env
      (.player who :: after) initial).support := by
    simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion]
    refine ⟨next, ?_, hafter⟩
    simp only [invoke, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨_, hcommand, hnext⟩
  have hacceptance := runtime.runPolicies_candidate_acceptance
    runtime.candidateHandle_sound players env before _ initial
    SealedResolution.CandidateAcceptanceInvariant.initial hbefore
  have hvalues : ∀ index handle stored,
      SealedProgram.Event.accepted index handle ∈ initial.native.application.visible.events →
      initial.native.application.service.lookup handle = .openable stored →
      cfg.1.store (G.nodeTarget index) =
        some (⟨ty, stored⟩ : TypedValue L) := by
    intro index handle stored haccepted hlookup
    have hselected := runtime.runPolicies_candidate_accepted?
      runtime.candidateHandle_sound players env (.player who :: after)
      initial stopped.last index handle (hacceptance index handle haccepted).1 hrest
    have hfixed := runtime.runPolicies_candidate_lookup_of_not_fresh
      runtime.candidateHandle_sound players env
      (.player who :: after) initial stopped.last handle (by simp [hlookup]) hrest
    have hgraph := supported.candidateGraphRun_accepted hinfo hguards
      nullValue window focal deviator environment schedule fallback _ cfg hcfg (fun _ => false)
    dsimp only at hgraph
    rw [hreplay, PolicyTrace.firstRelease_false_eq_last] at hgraph
    exact hgraph index handle stored
      (SealedProgram.accepted_mem_of_accepted?_eq_some hselected) (hfixed.trans hlookup)
  have hplayer : players who = runtime.candidatePlayerPolicy
      (supported.resolvingProposalPolicy nullValue window who
        (supported.assignedProposals reference who)) := by
    simp only [players, runtime, SealedShape.candidateValuePlayers,
      Profile.update_of_ne _ _ hwho]
  have hselected := hcommand
  rw [hplayer] at hselected
  have hopening := runtime.runPolicies_candidate_openings players env before _ initial
    SealedResolution.CandidateOpeningInvariant.initial hbefore
  obtain ⟨node, guard, hsem, reads, hslot, hempty, hreads, hkernel⟩ :=
    supported.candidate_registration_kernel cfg nullValue window
      players env before initial hbefore hclear who _
      (profile who) hplayer
      (fun index handle value hrecord _ => hvalues index handle value hrecord)
      (supported.candidate_opened_graph_value cfg hterminal nullValue window
        initial.native.application hopening hclear hvalues) slot value hselected
  have hfresh : initial.native.application.service.lookup (who, slot) = .fresh := hslot ▸ hempty
  have hnew : next.native.application.service.lookup (who, slot) = .openable value := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hnext
    subst next
    exact (initial.native.application.service.lookup_prepare_self who slot value).trans
      (by rw [hfresh])
  have hlookup : stopped.last.native.application.service.lookup (who, slot) =
      .openable value :=
    (runtime.runPolicies_candidate_lookup_of_not_fresh
      runtime.candidateHandle_sound players env after next stopped.last
      (who, slot) (by simp [hnew]) hafter).trans hnew
  have htrace : trace ∈ (runtime.candidateApplication.tracePolicies players env schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support := by
    rw [supported.candidateReplay_law, FinDist.mem_support_pure]
  have hcheckpoint := runtime.candidateRegistrationCheckpoint_selected players env schedule _
    trace htrace stop who slot value (by intro h; cases h) hlookup
  let release := fun execution : runtime.candidateApplication.PolicyExecution =>
    !stop execution && decide (.privateCommand ⟨(slot, value)⟩ ∈
      (players who (execution.principalHistory who)
        (State.observe runtime.candidateApplication execution.native who)).support)
  have hcheckpointClear :
      (stopped.firstRelease release).native.application.visible.timeouts = [] := by
    simpa only [MessageApplication.commandCheckpoint, stop, Bool.not_eq_eq_eq_not,
      Bool.not_false, List.isEmpty_iff] using hcheckpoint.1
  obtain ⟨otherNode, otherGuard, otherSem, otherReads, otherSlot, _, otherReadEq, otherKernel⟩ :=
    supported.restrictedCandidateGraphRun_registration_kernel hinfo hguards nullValue window focal
      deviator environment schedule fallback reference profile release cfg hcfg hcheckpointClear
      who hwho slot value hcheckpoint.2 (profile who)
  have hnode : otherNode = node := Fin.ext (otherSlot.symm.trans hslot)
  subst otherNode
  have hguard : otherGuard = guard := (NodeSem.commit.inj (otherSem.symm.trans hsem)).2
  subst otherGuard
  have hread : otherReads = reads := Option.some.inj (otherReadEq.symm.trans hreads)
  subst otherReads
  refine ⟨G.mem_commitPositions who slot |>.mpr ⟨node, guard, hsem, hslot.symm⟩,
    hfresh, ?_⟩
  simp only [candidateReplayRegistrationFactor, if_neg hwho]
  erw [hlookup]
  change (runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (profile who))
      (initial.principalHistory who)
      (State.observe runtime.candidateApplication initial.native who)).prob _ =
    (runtime.candidatePlayerPolicy (supported.resolvingPolicy nullValue window who (profile who))
      ((stopped.firstRelease release).principalHistory who)
      (State.observe runtime.candidateApplication
        (stopped.firstRelease release).native who)).prob _
  rw [otherKernel]
  rw [hkernel]

/-- The original native runner assigns the replay prefix exactly the product
of original honest preparation probabilities indexed by graph commitments.
Pending messages, retries, delivery, inclusion, and ticks are counted by the
native runner; none introduces an additional draw of a cached graph choice.
The cutoff is the first timeout, and native responses are fixed functions. -/
theorem candidateReplay_prefix_prob_eq_product
    (reference : Fin G.nodeCount → L.Val ty)
    (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => runtime.candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who (profile who))) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough stop
    ((runtime.candidateApplication.tracePolicies players
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
        (PolicyTrace.prefixThrough stop)).prob stopped =
      (G.commitPositions.map fun slot =>
        supported.candidateReplayRegistrationFactor nullValue window focal deviator environment
          schedule reference profile slot.1 slot.2).prod := by
  classical
  intro runtime players stop stopped
  let referencePlayers := supported.candidateValuePlayers nullValue window reference
    focal (fun history view => FinDist.pure (deviator history view))
  let handles := G.commitPositions.toFinset
  let factor := fun slot : CommitmentHandle Player Nat =>
    supported.candidateReplayRegistrationFactor nullValue window focal deviator environment
      schedule reference profile slot.1 slot.2
  have htrace : stopped ∈ ((runtime.candidateApplication.tracePolicies referencePlayers
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
        (PolicyTrace.prefixThrough stop)).support := by
    rw [supported.candidateReplay_law, FinDist.map_pure, FinDist.mem_support_pure]
  have hmass := runtime.tracePolicies_prefixThrough_prob_eq_preparationWeight players
    referencePlayers environment stop handles factor schedule stopped htrace
  have hlocal : ∀ before initial who command next after,
      initial ∈ (runtime.candidateApplication.runPolicies referencePlayers
        (fun history view => FinDist.pure (environment history view)) before
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support →
      command ∈ (referencePlayers who (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).support →
      next ∈ (runtime.candidateApplication.playerStep who initial command).support →
      stopped.last ∈ (runtime.candidateApplication.runPolicies referencePlayers
        (fun history view => FinDist.pure (environment history view)) after next).support →
      stop initial = false →
      (players who (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).prob command =
          runtime.candidatePreparationFactor handles factor initial who command := by
    intro before initial who command next after hbefore hcommand hnext hafter hstop
    by_cases hwho : who = focal
    · subst who
      simp only [referencePlayers, EventGraph.SealedShape.candidateValuePlayers,
        Profile.update_same, FinDist.mem_support_pure] at hcommand
      simp only [players, Profile.update_same, ← hcommand, FinDist.prob_pure_self]
      cases command <;>
        simp only [SealedResolution.candidatePreparationFactor, factor,
          candidateReplayRegistrationFactor, if_pos rfl, ite_self]
    · simp only [players, Profile.update_of_ne _ _ hwho]
      cases command with
      | privateCommand request =>
          rcases request with ⟨slot, value⟩
          obtain ⟨hmem, hfresh, hfactor⟩ :=
            supported.candidateReplay_registration_factor hinfo hguards nullValue window focal
              deviator environment schedule reference profile before initial who slot value
              next after
              hwho hbefore hcommand hnext hafter hstop
          rw [hfactor, SealedResolution.candidatePreparationFactor,
            if_pos ⟨List.mem_toFinset.mpr hmem, hfresh⟩]
      | submit payload | replay id | wait =>
          simp only [referencePlayers, EventGraph.SealedShape.candidateValuePlayers,
            Profile.update_of_ne _ _ hwho] at hcommand
          have hlaw := supported.selected_nonregistration_law who
            initial.native.application.visible.timeouts
            (supported.assignedProposals reference who)
            ((profile who)).proposals
            (runtime.eventHistory (runtime.registeredPlayerHistory (initial.principalHistory who)))
            (runtime.eventView (runtime.registeredPlayerView
              (State.observe runtime.candidateApplication initial.native who)))
            _ _ hcommand (fun _ h => by cases h)
          change runtime.candidatePlayerPolicy
            (supported.resolvingPolicy nullValue window who (profile who))
            (initial.principalHistory who)
            (State.observe runtime.candidateApplication initial.native who) = _ at hlaw
          rw [hlaw, FinDist.prob_pure_self]
          rfl
  rw [hmass hlocal]
  unfold CommitmentCandidates.preparationWeight
  have hweight : ∀ handle ∈ handles,
      (if (stopped.last.native.application.service.lookup handle).opening?.isSome
        then factor handle else 1) = factor handle := by
    intro handle _
    cases hlookup : (stopped.last.native.application.service.lookup handle).opening? with
    | some value => rfl
    | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        by_cases hwho : handle.1 = focal
        · simp only [factor, candidateReplayRegistrationFactor, if_pos hwho]
        · simp only [factor, candidateReplayRegistrationFactor, if_neg hwho]
          erw [hlookup]
  rw [Finset.prod_congr rfl hweight]
  exact List.prod_toFinset factor G.commitPositions_nodup

omit [Finite Player] in
/-- Exact native marginal of the graph realization under the
extracted focal policy, through the first timeout. Opponents retain their
original, potentially dependent graph kernels. Equality concerns complete
native prefixes, including private command records, pending messages, delivery,
inclusion, clock, and receipts; these proof records are not player views.

The focal and environment responses are fixed functions. This theorem neither
identifies the post-timeout continuation with a graph run nor removes the
utility condition needed for informed quitting. -/
theorem candidateGraphRun_native_prefix_law [Fintype Player] (fallback : L.Val ty)
    (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => runtime.candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who (profile who))) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment schedule
      fallback profile).map (fun cfg =>
        (supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop) =
      (runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
          (PolicyTrace.prefixThrough stop) := by
  intro runtime players stop
  apply FinDist.ext_of_prob_on_support
  intro trace htrace
  rw [FinDist.support_map] at htrace
  obtain ⟨cfg, _, rfl⟩ := htrace
  have hgraph := supported.candidateGraphRun_replay_prob_eq_product nullValue window focal
    deviator environment schedule hinfo hguards fallback (cfg.1.nodeValues fallback) profile
  exact (hgraph.trans (G.prod_commitPositions
    (supported.candidateReplayRegistrationFactor nullValue window focal deviator environment
      schedule (cfg.1.nodeValues fallback) profile)).symm).trans
    (supported.candidateReplay_prefix_prob_eq_product hinfo hguards nullValue window focal
      deviator environment schedule (cfg.1.nodeValues fallback) profile).symm

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateGraphRun_native_prefix_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateGraphRun_native_prefix_law

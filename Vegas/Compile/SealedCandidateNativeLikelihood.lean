/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateSourceFactors
import Interaction.SealedCandidateLikelihood

/-! # Exact source/native prefixes for candidate pending messages

An actual preparation invocation and its replay checkpoint share the declared
source inputs, although their native snapshots may differ. Accepted pointers
and fixed candidate meanings persist to their common endpoint; the normalized
source realization supplies the values needed at both snapshots. Counting each
fresh preparation once identifies the complete native prefix law through first
timeout. No positive probability premise is imposed on the original source policy.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
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

/-- At an actual honest preparation invocation, the slot is a fresh source
decision and the original policy probability equals its fixed replay factor.
The prefix and suffix premises are ordinary native executions, not assumed
source/native couplings. -/
theorem candidateReplay_registration_factor
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := compilation.supported.candidateValuePlayers nullValue window reference focal
      (fun history view => FinDist.pure (deviator history view))
    let env := fun history view => FinDist.pure (environment history view)
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let trace := compilation.supported.candidateReplay nullValue window reference focal
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
      (who, slot) ∈ source.core.prog.decisionPositions ∧
      initial.native.application.service.lookup (who, slot) = .fresh ∧
      (compilation.compileCandidatePolicy nullValue window who (profile who)
        (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).prob
          (.privateCommand ⟨(slot, value)⟩) =
        compilation.candidateReplayRegistrationFactor nullValue window focal deviator environment
          schedule reference profile who slot := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  let fallback := nullValue
  intro runtime players env stop trace stopped before initial who slot value next after
    hwho hbefore hcommand hnext hafter hstop
  let restricted := (compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
    (fun handle => (stopped.last.native.application.service.lookup handle).opening?)).apply profile
  obtain ⟨cfg, hcfg⟩ := (compilation.extractedCandidateSourceRun nullValue window focal deviator
    environment schedule fallback restricted).support_nonempty
  have hterminal := compilation.sourceRunOfDisclosures_terminal focal _ restricted cfg hcfg
  have hreplay := compilation.restrictedCandidateSourceRun_replay_prefix nullValue window focal
    deviator environment schedule fallback reference stop profile cfg hcfg
  have hclear : initial.native.application.visible.timeouts = [] := by
    simpa only [stop, Bool.not_eq_eq_eq_not, Bool.not_false, List.isEmpty_iff] using hstop
  have hrest : stopped.last ∈ (runtime.candidateApplication.runPolicies players env
      (.player who :: after) initial).support := by
    simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion]
    refine ⟨next, ?_, hafter⟩
    simp only [invoke, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨_, hcommand, hnext⟩
  have hacceptance := runtime.runPolicies_candidate_acceptance players env before _ initial
    SealedResolution.CandidateAcceptanceInvariant.initial hbefore
  have hvalues : ∀ index handle stored,
      SealedProgram.Event.accepted index handle ∈ initial.native.application.visible.events →
      initial.native.application.service.lookup handle = .openable stored →
      cfg.1.store ((compile source.core).graph.nodeTarget index) =
        some (⟨ty, stored⟩ : TypedValue L) := by
    intro index handle stored haccepted hlookup
    have hselected := runtime.runPolicies_candidate_accepted? players env (.player who :: after)
      initial stopped.last index handle (hacceptance index handle haccepted).1 hrest
    have hfixed := runtime.runPolicies_candidate_lookup_of_not_fresh players env
      (.player who :: after) initial stopped.last handle (by simp [hlookup]) hrest
    have hsource := compilation.extractedCandidateSourceRun_accepted nullValue window focal
      deviator environment schedule fallback restricted cfg hcfg (fun _ => false)
    dsimp only at hsource
    rw [hreplay, PolicyTrace.firstRelease_false_eq_last] at hsource
    exact hsource index handle stored
      (SealedProgram.accepted_mem_of_accepted?_eq_some hselected) (hfixed.trans hlookup)
  have hplayer : players who = runtime.candidatePlayerPolicy
      (compilation.supported.resolvingPolicy nullValue window who
        (compilation.supported.valuePolicy reference who)) := by
    simp only [players, runtime, SealedFragment.candidateValuePlayers,
      Profile.update_of_ne _ _ hwho]
  have hselected := hcommand
  rw [hplayer] at hselected
  obtain ⟨node, guard, hsem, reads, hslot, hempty, hreads, hkernel⟩ :=
    compilation.supported.candidate_registration_kernel cfg hterminal nullValue window
      players env before initial hbefore hclear who _
      (compileSourcePolicy source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        rfl who (profile who)) hplayer hvalues slot value hselected
  have hfresh : initial.native.application.service.lookup (who, slot) = .fresh := hslot ▸ hempty
  have hnew : next.native.application.service.lookup (who, slot) = .openable value := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hnext
    subst next
    exact (initial.native.application.service.lookup_prepare_self who slot value).trans
      (by rw [hfresh])
  have hlookup : stopped.last.native.application.service.lookup (who, slot) =
      .openable value :=
    (runtime.runPolicies_candidate_lookup_of_not_fresh players env after next stopped.last
      (who, slot) (by simp [hnew]) hafter).trans hnew
  have htrace : trace ∈ (runtime.candidateApplication.tracePolicies players env schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support := by
    rw [compilation.supported.candidateReplay_law, FinDist.mem_support_pure]
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
    compilation.restrictedCandidateSourceRun_registration_kernel nullValue window focal deviator
      environment schedule fallback reference profile release cfg hcfg hcheckpointClear who hwho
      slot value hcheckpoint.2 (profile who)
  have hnode : otherNode = node := Fin.ext (otherSlot.symm.trans hslot)
  subst otherNode
  have hguard : otherGuard = guard := (NodeSem.commit.inj (otherSem.symm.trans hsem)).2
  subst otherGuard
  have hread : otherReads = reads := Option.some.inj (otherReadEq.symm.trans hreads)
  subst otherReads
  obtain ⟨Δ, name, choiceTy, sourceGuard, site, hdepth, _⟩ :=
    compileSourcePolicy_recorded_law source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who (profile who) node guard hsem cfg hterminal reads hreads
  refine ⟨?_, hfresh, ?_⟩
  · rw [← hdepth.trans hslot.symm]
    exact site.decisionPositions_mem
  · simp only [candidateReplayRegistrationFactor, if_neg hwho]
    erw [hlookup]
    change (compilation.compileCandidatePolicy nullValue window who (profile who)
        (initial.principalHistory who)
        (State.observe runtime.candidateApplication initial.native who)).prob _ =
      (compilation.compileCandidatePolicy nullValue window who (profile who)
        ((stopped.firstRelease release).principalHistory who)
        (State.observe runtime.candidateApplication
          (stopped.firstRelease release).native who)).prob _
    rw [otherKernel]
    change (runtime.candidatePlayerPolicy
      (compilation.supported.resolvingPolicy nullValue window who _) _ _).prob _ = _
    rw [hkernel]

/-- The original native runner assigns the replay prefix exactly the product
of original honest preparation probabilities indexed by source decisions.
Pending messages, retries, delivery, inclusion, and ticks are counted by the
native runner; none introduces an additional draw of a cached source choice.
The cutoff is the first timeout, and native responses are fixed functions. -/
theorem candidateReplay_prefix_prob_eq_product
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (compilation.supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough stop
    ((runtime.candidateApplication.tracePolicies players
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
        (PolicyTrace.prefixThrough stop)).prob stopped =
      (source.core.prog.decisionPositions.map fun slot =>
        compilation.candidateReplayRegistrationFactor nullValue window focal deviator environment
          schedule reference profile slot.1 slot.2).prod := by
  classical
  intro runtime players stop stopped
  let referencePlayers := compilation.supported.candidateValuePlayers nullValue window reference
    focal (fun history view => FinDist.pure (deviator history view))
  let handles := source.core.prog.decisionPositions.toFinset
  let factor := fun slot : CommitmentHandle Player Nat =>
    compilation.candidateReplayRegistrationFactor nullValue window focal deviator environment
      schedule reference profile slot.1 slot.2
  have htrace : stopped ∈ ((runtime.candidateApplication.tracePolicies referencePlayers
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
        (PolicyTrace.prefixThrough stop)).support := by
    rw [compilation.supported.candidateReplay_law, FinDist.map_pure, FinDist.mem_support_pure]
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
      simp only [referencePlayers, EventGraph.SealedFragment.candidateValuePlayers,
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
            compilation.candidateReplay_registration_factor nullValue window focal deviator
              environment schedule reference profile before initial who slot value next after
              hwho hbefore hcommand hnext hafter hstop
          rw [hfactor, SealedResolution.candidatePreparationFactor,
            if_pos ⟨List.mem_toFinset.mpr hmem, hfresh⟩]
      | submit payload | replay id | wait =>
          simp only [referencePlayers, EventGraph.SealedFragment.candidateValuePlayers,
            Profile.update_of_ne _ _ hwho] at hcommand
          have hlaw := compilation.supported.selected_nonregistration_law who
            initial.native.application.visible.timeouts
            (compilation.supported.valuePolicy reference who)
            (compileSourcePolicy source.core.prog source.core.fresh
              (BuildState.fromInitial
                (initialState source.core.Γ source.core.env source.core.wctx))
              rfl who (profile who))
            (runtime.eventHistory (runtime.registeredPlayerHistory (initial.principalHistory who)))
            (runtime.eventView (runtime.registeredPlayerView
              (State.observe runtime.candidateApplication initial.native who)))
            _ _ hcommand (fun _ h => by cases h)
          change compilation.compileCandidatePolicy nullValue window who (profile who)
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
  exact List.prod_toFinset factor source.core.prog.decisionPositions_nodup

omit [Finite Player] in
/-- Exact native marginal of the written-source realization under the
extracted focal policy, through the first timeout. Opponents retain their
original, potentially dependent source kernels. Equality concerns complete
native prefixes, including private command records, pending messages, delivery,
inclusion, clock, and receipts; these proof records are not player views.

The focal and environment responses are fixed functions. This theorem neither
identifies the post-timeout continuation with a source run nor removes the
utility condition needed for informed quitting. -/
theorem extractedCandidateSourceRun_native_prefix_law [Fintype Player] (fallback : L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (compilation.extractedCandidateSourceRun nullValue window focal deviator environment schedule
      fallback profile).map (fun cfg =>
        (compilation.supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
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
  exact (compilation.extractedCandidateSourceRun_replay_prob_eq_product nullValue window focal
    deviator environment schedule fallback (cfg.1.nodeValues fallback) profile).trans
      (compilation.candidateReplay_prefix_prob_eq_product nullValue window focal deviator
        environment schedule (cfg.1.nodeValues fallback) profile).symm

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.candidateReplay_registration_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidateReplay_registration_factor

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_native_prefix_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_native_prefix_law

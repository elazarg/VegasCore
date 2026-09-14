/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceCylinder
import Interaction.SealedResolutionLikelihood

/-! # Exact source/native prefixes for sealed pending messages

The reference source realization supplies the declared inputs of both the
selected registration checkpoint and the actual invocation. The snapshots
need not be equal. Their kernels agree because the source occurrence and its
declared reads agree. Native command histories supply freshness independently.
Each fresh honest registration is counted once, giving the same probability
product as the source cylinder. Normalization then identifies the complete
native prefix law through first timeout, with original opponent kernels.
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
  List (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
variable (environment :
  List
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  (compilation.supported.resolvingRuntime nullValue
    window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

/-- A fresh honest registration at an actual invocation has exactly its
fixed replay factor. Its owner/slot is a source decision and is still empty.
Both prefix and suffix premises are ordinary native executions; the proof
does not identify the invocation with the selected registration checkpoint. -/
theorem replay_registration_factor
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := compilation.supported.resolvingValuePlayers nullValue window reference focal
      (fun history view => FinDist.pure (deviator history view))
    let env := fun history view => FinDist.pure (environment history view)
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let trace := compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule
    let stopped := trace.prefixThrough stop
    ∀ before initial who slot value next after,
      who ≠ focal →
      initial ∈ (runtime.messageApplication.runPolicies players env before
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).support →
      .privateCommand ⟨(slot, value)⟩ ∈ (players who (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).support →
      next ∈ (runtime.messageApplication.playerStep who initial
        (.privateCommand ⟨(slot, value)⟩)).support →
      stopped.last ∈ (runtime.messageApplication.runPolicies players env after next).support →
      stop initial = false →
      (who, slot) ∈ source.core.prog.decisionPositions ∧
      initial.native.application.service.lookup (who, slot) = none ∧
      (compilation.compileResolvingPolicy nullValue window who (profile who)
        (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).prob
          (.privateCommand ⟨(slot, value)⟩) =
        compilation.replayRegistrationFactor nullValue window focal deviator environment schedule
          reference profile who slot := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  let fallback := nullValue
  intro runtime players env stop trace stopped before initial who slot value next after
    hwho hbefore hcommand hnext hafter hstop
  let restricted := (compilation.registrationRestriction focal
    stopped.last.native.application.service).apply profile
  obtain ⟨cfg, hcfg⟩ := (compilation.extractedSourceRun nullValue window focal deviator environment
    schedule fallback restricted).support_nonempty
  have hterminal := compilation.extractedSourceRun_terminal nullValue window focal deviator
    environment schedule fallback restricted cfg hcfg
  have hreplay := compilation.restrictedSourceRun_replay_prefix nullValue window focal deviator
    environment schedule fallback reference stop profile cfg hcfg
  have hclear : initial.native.application.visible.timeouts = [] := by
    simpa only [stop, Bool.not_eq_eq_eq_not, Bool.not_false, List.isEmpty_iff] using hstop
  have hmemory := SealedResolution.RegistrationMemory.runPolicies players env before _ initial
    SealedResolution.RegistrationMemory.initial hbefore
  have hbinding := runtime.runPolicies_beforeTimeoutBinding players env before _ initial
    SealedResolution.BeforeTimeoutBinding.initial hbefore hclear
  have hrest : stopped.last ∈ (runtime.messageApplication.runPolicies players env
      (.player who :: after) initial).support := by
    simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion]
    refine ⟨next, ?_, hafter⟩
    simp only [invoke, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨_, hcommand, hnext⟩
  have hvalues : ∀ owner (node : Fin (compile source.core).graph.nodeCount) guard,
      ((compile source.core).graph.nodeRow node).sem = .commit owner guard → ∀ registered,
      initial.native.application.service.lookup (owner, node.val) = some registered →
        cfg.1.nodeValues fallback node = registered := by
    intro owner node guard hsem registered hlookup
    apply compilation.extractedSourceRun_registered nullValue window focal deviator environment
      schedule fallback restricted cfg hcfg owner node guard hsem registered
    rw [EventGraph.SealedFragment.resolvingStop, ← PolicyTrace.prefixThrough_last, hreplay]
    exact runtime.runPolicies_lookup_of_eq_some players env (.player who :: after) initial _
      (owner, node.val) registered hlookup hrest
  have hselected := hcommand
  simp only [players, EventGraph.SealedFragment.resolvingValuePlayers,
    Profile.update_of_ne _ _ hwho] at hselected
  obtain ⟨node, guard, hsem, reads, hslot, hempty, hreads, hkernel⟩ :=
    compilation.supported.resolving_registration_kernel cfg hterminal fallback nullValue window
      initial hclear hmemory (hbinding.copy rfl rfl) hvalues who _
      (compileSourcePolicy source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        rfl who (profile who)) slot value hselected
  have hfresh : initial.native.application.service.lookup (who, slot) = none := hslot ▸ hempty
  have hnew : next.native.application.service.lookup (who, slot) = some value := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hnext
    subst next
    exact (initial.native.application.service.seal_first who slot value hfresh).2
  have hlookup := runtime.runPolicies_lookup_of_eq_some players env after next stopped.last
    (who, slot) value hnew hafter
  have htrace : trace ∈ (runtime.messageApplication.tracePolicies players env schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
    rw [compilation.supported.resolvingReplay_law, FinDist.mem_support_pure]
  have hcheckpoint := runtime.registrationCheckpoint_selected players env schedule _ trace htrace
    stop who slot value (by intro h; cases h) hlookup
  let release := fun execution : runtime.messageApplication.PolicyExecution =>
    !stop execution && decide (.privateCommand ⟨(slot, value)⟩ ∈
      (players who (execution.principalHistory who)
        (State.observe runtime.messageApplication execution.native who)).support)
  have hcheckpointClear :
      (stopped.firstRelease release).native.application.visible.timeouts = [] := by
    simpa only [SealedResolution.registrationCheckpoint, stop, Bool.not_eq_eq_eq_not,
      Bool.not_false, List.isEmpty_iff] using hcheckpoint.1
  obtain ⟨otherNode, otherGuard, otherSem, otherReads, otherSlot, _, otherReadEq, otherKernel⟩ :=
    compilation.restrictedSourceRun_registration_kernel nullValue window focal deviator
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
  · simp only [replayRegistrationFactor, if_neg hwho]
    erw [hlookup]
    change (compilation.compileResolvingPolicy nullValue window who (profile who)
        (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).prob _ =
      (compilation.compileResolvingPolicy nullValue window who (profile who)
        ((stopped.firstRelease release).principalHistory who)
        (State.observe runtime.messageApplication (stopped.firstRelease release).native who)).prob _
    rw [otherKernel]
    change (compilation.supported.resolvingPolicy nullValue window who _ _ _).prob _ = _
    rw [hkernel]

/-- The original native runner assigns the replay prefix exactly the product
of original honest registration probabilities indexed by source decisions.
Pending messages, retries, delivery, inclusion, and ticks are counted by the
native runner; none introduces an additional draw of a cached source choice.
The cutoff is the first timeout, and native responses are fixed functions. -/
theorem replay_prefix_prob_eq_product
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.messageApplication)
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough stop
    ((runtime.messageApplication.tracePolicies players
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough stop)).prob stopped =
      (source.core.prog.decisionPositions.map fun slot =>
        compilation.replayRegistrationFactor nullValue window focal deviator environment schedule
          reference profile slot.1 slot.2).prod := by
  classical
  intro runtime players stop stopped
  let referencePlayers := compilation.supported.resolvingValuePlayers nullValue window reference
    focal (fun history view => FinDist.pure (deviator history view))
  let handles := source.core.prog.decisionPositions.toFinset
  let factor := fun slot : CommitmentHandle Player Nat =>
    compilation.replayRegistrationFactor nullValue window focal deviator environment schedule
      reference profile slot.1 slot.2
  have htrace : stopped ∈ ((runtime.messageApplication.tracePolicies referencePlayers
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough stop)).support := by
    rw [compilation.supported.resolvingReplay_law, FinDist.map_pure, FinDist.mem_support_pure]
  have hmass := runtime.tracePolicies_prefixThrough_prob_eq_registrationWeight players
    referencePlayers environment stop handles factor schedule stopped htrace
  have hlocal : ∀ before initial who command next after,
      initial ∈ (runtime.messageApplication.runPolicies referencePlayers
        (fun history view => FinDist.pure (environment history view)) before
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).support →
      command ∈ (referencePlayers who (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).support →
      next ∈ (runtime.messageApplication.playerStep who initial command).support →
      stopped.last ∈ (runtime.messageApplication.runPolicies referencePlayers
        (fun history view => FinDist.pure (environment history view)) after next).support →
      stop initial = false →
      (players who (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).prob command =
          runtime.registrationFactor handles factor initial who command := by
    intro before initial who command next after hbefore hcommand hnext hafter hstop
    by_cases hwho : who = focal
    · subst who
      simp only [referencePlayers, EventGraph.SealedFragment.resolvingValuePlayers,
        Profile.update_same, FinDist.mem_support_pure] at hcommand
      simp only [players, Profile.update_same, ← hcommand, FinDist.prob_pure_self]
      cases command <;>
        simp only [SealedResolution.registrationFactor, factor, replayRegistrationFactor,
          if_pos rfl, ite_self]
    · simp only [players, Profile.update_of_ne _ _ hwho]
      cases command with
      | privateCommand request =>
          rcases request with ⟨slot, value⟩
          obtain ⟨hmem, hfresh, hfactor⟩ := compilation.replay_registration_factor nullValue window
            focal deviator environment schedule reference profile before initial who slot value
            next after hwho hbefore hcommand hnext hafter hstop
          rw [hfactor, SealedResolution.registrationFactor,
            if_pos ⟨List.mem_toFinset.mpr hmem, hfresh⟩]
      | submit payload | replay id | wait =>
          simp only [referencePlayers, EventGraph.SealedFragment.resolvingValuePlayers,
            Profile.update_of_ne _ _ hwho] at hcommand
          have hlaw := compilation.supported.selected_nonregistration_law who
            initial.native.application.visible.timeouts
            (compilation.supported.valuePolicy reference who)
            (compileSourcePolicy source.core.prog source.core.fresh
              (BuildState.fromInitial
                (initialState source.core.Γ source.core.env source.core.wctx))
              rfl who (profile who))
            (runtime.eventHistory (initial.principalHistory who))
            (runtime.eventView (State.observe runtime.messageApplication initial.native who))
            _ _ hcommand (fun _ h => by cases h)
          change compilation.compileResolvingPolicy nullValue window who (profile who)
            (initial.principalHistory who)
            (State.observe runtime.messageApplication initial.native who) = _ at hlaw
          rw [hlaw, FinDist.prob_pure_self]
          rfl
  rw [hmass hlocal]
  unfold IdealCommitments.registrationWeight
  have hweight : ∀ handle ∈ handles,
      (if (stopped.last.native.application.service.lookup handle).isSome
        then factor handle else 1) = factor handle := by
    intro handle _
    cases hlookup : stopped.last.native.application.service.lookup handle with
    | some value => rfl
    | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        by_cases hwho : handle.1 = focal
        · simp only [factor, replayRegistrationFactor, if_pos hwho]
        · simp only [factor, replayRegistrationFactor, if_neg hwho]
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
theorem extractedSourceRun_native_prefix_law [Fintype Player] (fallback : L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.messageApplication)
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      profile).map (fun cfg =>
        (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop) =
      (runtime.messageApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
          (PolicyTrace.prefixThrough stop) := by
  intro runtime players stop
  apply FinDist.ext_of_prob_on_support
  intro trace htrace
  rw [FinDist.support_map] at htrace
  obtain ⟨cfg, _, rfl⟩ := htrace
  exact (compilation.extractedSourceRun_replay_prob_eq_product nullValue window focal deviator
    environment schedule fallback (cfg.1.nodeValues fallback) profile).trans
      (compilation.replay_prefix_prob_eq_product nullValue window focal deviator environment
        schedule (cfg.1.nodeValues fallback) profile).symm

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.replay_registration_factor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.replay_registration_factor

/-- info: 'Vegas.SealedCompilation.replay_prefix_prob_eq_product' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.replay_prefix_prob_eq_product

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_native_prefix_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_native_prefix_law

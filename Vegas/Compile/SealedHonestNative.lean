/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestLikelihood
import Vegas.Compile.SealedPolicyProgress
import Vegas.EventGraph.CommitPositions
import Interaction.SealedResolutionLikelihood
import Interaction.MessageApplicationPredraw
import Interaction.MessageApplicationContinuation

/-! # Original all-player graph law through first timeout

The graph restriction mass and native registration mass count the same
conditional probabilities. Every graph policy is unchanged; only the adaptive
environment is predrawn. There is no source syntax or source-image assumption.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hguards : GuardLive G)
variable (nullValue : L.Val ty) (window : Nat)
variable (environment :
  List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

include hguards

omit [Fintype Player] in
/-- A fresh native registration has the same original graph probability as
its replay checkpoint. The snapshots need not coincide. -/
theorem assigned_registration_factor [Finite Player]
    (reference : Fin G.nodeCount → L.Val ty) (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := supported.resolvingAssignedPlayers nullValue window reference
    let env := fun history view => FinDist.pure (environment history view)
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let trace := supported.resolvingAssignedReplay nullValue window reference environment schedule
    let stopped := trace.prefixThrough stop
    ∀ before initial who slot value next after,
      initial ∈ (runtime.messageApplication.runPolicies players env before
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).support →
      .privateCommand ⟨(slot, value)⟩ ∈ (players who (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).support →
      next ∈ (runtime.messageApplication.playerStep who initial
        (.privateCommand ⟨(slot, value)⟩)).support →
      stopped.last ∈ (runtime.messageApplication.runPolicies players env after next).support →
      stop initial = false →
      (who, slot) ∈ G.commitPositions ∧
      initial.native.application.service.lookup (who, slot) = none ∧
      (supported.resolvingPolicy nullValue window who (profile who)
        (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).prob
          (.privateCommand ⟨(slot, value)⟩) =
        supported.assignedRegistrationFactor nullValue window environment schedule
          reference profile who slot := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  let fallback := nullValue
  intro runtime players env stop trace stopped before initial who slot value next after
    hbefore hcommand hnext hafter hstop
  let restriction := supported.recordedChoiceRestriction (fun _ => true)
    stopped.last.native.application.service.lookup
  obtain ⟨cfg, hcfg⟩ := (runPolicyNodes supported.graphWF hguards (restriction.apply profile)
    ⟨Config.initial G, .initial⟩ G.nodeOrder).support_nonempty
  have hterminal := runPolicyNodes_terminal supported.graphWF hguards (restriction.apply profile)
    ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) cfg hcfg
  have hallows := runPolicyNodes_restriction_support supported.graphWF hguards profile restriction
    ⟨Config.initial G, .initial⟩ (CommitValuesSupported.initial _) G.nodeOrder
    G.nodeOrder_readyOrder cfg hcfg
  have hrecorded := (supported.recordedChoiceRestriction_allows_iff_nodeValues _ _ cfg hterminal
    fallback).mp hallows
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
  have hvalues : ∀ owner (node : Fin G.nodeCount) guard,
      (G.nodeRow node).sem = .commit owner guard → ∀ registered,
      initial.native.application.service.lookup (owner, node.val) = some registered →
        cfg.1.nodeValues fallback node = registered := by
    intro owner node guard hsem registered hlookup
    exact hrecorded owner node guard hsem rfl registered
      (runtime.runPolicies_lookup_of_eq_some players env (.player who :: after) initial _
        (owner, node.val) registered hlookup hrest)
  obtain ⟨node, guard, hsem, reads, hslot, hfresh, hreads, hkernel⟩ :=
    supported.resolving_registration_kernel cfg hterminal fallback nullValue window initial
      hclear hmemory (hbinding.copy rfl rfl) hvalues who
      (supported.valuePolicy reference who) (profile who) slot value hcommand
  have hfreshSlot : initial.native.application.service.lookup (who, slot) = none := hslot ▸ hfresh
  have hnew : next.native.application.service.lookup (who, slot) = some value := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hnext
    subst next
    exact (initial.native.application.service.seal_first who slot value hfreshSlot).2
  have hlookup := runtime.runPolicies_lookup_of_eq_some players env after next stopped.last
    (who, slot) value hnew hafter
  have htrace : trace ∈ (runtime.messageApplication.tracePolicies players env schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
    rw [supported.resolvingAssignedReplay_law, FinDist.mem_support_pure]
  have hcheckpoint := runtime.registrationCheckpoint_selected players env schedule _ trace htrace
    stop who slot value (by intro h; cases h) hlookup
  let release := fun execution : runtime.messageApplication.PolicyExecution =>
    !stop execution && decide (.privateCommand ⟨(slot, value)⟩ ∈
      (players who (execution.principalHistory who)
        (State.observe runtime.messageApplication execution.native who)).support)
  have hcheckpointClear :
      (stopped.firstRelease release).native.application.visible.timeouts = [] := by
    simpa only [MessageApplication.commandCheckpoint, stop, Bool.not_eq_eq_eq_not,
      Bool.not_false, List.isEmpty_iff] using hcheckpoint.1
  obtain ⟨actual, test, htest, inputs, hactualSlot, _, hinputs, hactualKernel⟩ :=
    supported.restrictedGraphRun_assigned_registration_kernel hguards nullValue window
      environment schedule reference profile release cfg hcfg hcheckpointClear who slot value
      hcheckpoint.2 (profile who)
  have hnode : actual = node := Fin.ext (hactualSlot.symm.trans hslot)
  subst actual
  have hguard : test = guard := (NodeSem.commit.inj (htest.symm.trans hsem)).2
  subst test
  have heq : inputs = reads := Option.some.inj (hinputs.symm.trans hreads)
  subst inputs
  refine ⟨(G.mem_commitPositions who slot).mpr ⟨node, guard, hsem, hslot.symm⟩, hfreshSlot, ?_⟩
  simp only [assignedRegistrationFactor]
  erw [hlookup]
  exact congrArg (fun law => law.prob (.privateCommand ⟨(slot, value)⟩))
    (hkernel.trans hactualKernel.symm)

omit [Fintype Player] in
/-- The native mass of each queried replay prefix is the product of all
original graph registration factors. Nonregistration commands add no draw. -/
theorem assignedReplay_prefix_prob_eq_product
    [Finite Player]
    (reference : Fin G.nodeCount → L.Val ty)
    (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := fun who => supported.resolvingPolicy nullValue window who (profile who)
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough stop
    ((runtime.messageApplication.tracePolicies players
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough stop)).prob stopped =
      (G.commitPositions.map fun slot =>
        supported.assignedRegistrationFactor nullValue window environment schedule
          reference profile slot.1 slot.2).prod := by
  classical
  intro runtime players stop stopped
  let referencePlayers := supported.resolvingAssignedPlayers nullValue window reference
  let handles := G.commitPositions.toFinset
  let factor := fun slot : CommitmentHandle Player Nat =>
    supported.assignedRegistrationFactor nullValue window environment schedule
      reference profile slot.1 slot.2
  have htrace : stopped ∈ ((runtime.messageApplication.tracePolicies referencePlayers
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough stop)).support := by
    rw [supported.resolvingAssignedReplay_law, FinDist.map_pure,
      FinDist.mem_support_pure]
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
    cases command with
    | privateCommand request =>
        rcases request with ⟨slot, value⟩
        obtain ⟨hmem, hfresh, hfactor⟩ := supported.assigned_registration_factor hguards nullValue
          window environment schedule reference profile before initial who slot value next after
          hbefore hcommand hnext hafter hstop
        rw [hfactor, SealedResolution.registrationFactor,
          if_pos ⟨List.mem_toFinset.mpr hmem, hfresh⟩]
    | submit payload | replay id | wait =>
        dsimp only [players]
        have hlaw := supported.selected_nonregistration_law who
          initial.native.application.visible.timeouts
          (supported.valuePolicy reference who)
          (profile who)
          (runtime.eventHistory (initial.principalHistory who))
          (runtime.eventView (State.observe runtime.messageApplication initial.native who))
          _ _ hcommand (fun _ h => by cases h)
        change supported.resolvingPolicy nullValue window who (profile who)
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
        simp only [factor, assignedRegistrationFactor]
        erw [hlookup]
  rw [Finset.prod_congr rfl hweight]
  exact List.prod_toFinset factor G.commitPositions_nodup

/-- Exact pending-message prefix law of the original graph profile. Every
player's graph kernel is retained, including all of its dependent choices.
This stops only the proof readout at first timeout, not the operational runner. -/
theorem graphRun_native_prefix_law (fallback : L.Val ty)
    (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := fun who => supported.resolvingPolicy nullValue window who (profile who)
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (runPolicyNodes supported.graphWF hguards profile
      ⟨Config.initial G, .initial⟩ G.nodeOrder).map (fun cfg =>
      (supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
        environment schedule).prefixThrough stop) =
      (runtime.messageApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
          (PolicyTrace.prefixThrough stop) := by
  intro runtime players stop
  apply FinDist.ext_of_prob_on_support
  intro trace htrace
  rw [FinDist.support_map] at htrace
  obtain ⟨cfg, _, rfl⟩ := htrace
  have hgraph := supported.graphRun_assignedReplay_prob_eq_product nullValue window environment
    schedule hguards fallback (cfg.1.nodeValues fallback) profile
  have hpositions := G.prod_commitPositions (fun who slot =>
    supported.assignedRegistrationFactor nullValue window environment schedule
      (cfg.1.nodeValues fallback) profile who slot)
  exact (hgraph.trans hpositions.symm).trans
    (supported.assignedReplay_prefix_prob_eq_product hguards nullValue window environment schedule
      (cfg.1.nodeValues fallback) profile).symm

/-- When actual all-compiled executions have no timeouts, their full native
trace law is obtained by replaying the original graph realization and a finite
mixture of environment responses. Only the environment is predrawn; the graph
profile and all its conditional choices are unchanged in every mixture term. -/
theorem exists_honest_replay_mixture
    (fallback : L.Val ty) (profile : CommitPolicyProfile G)
    (environment :
      (supported.resolvingRuntime nullValue
        window).messageApplication.EnvironmentPolicy)
    (hclear : ∀ trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (fun who => supported.resolvingPolicy nullValue window who (profile who))
        environment schedule (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).initial))).support,
      trace.last.native.application.visible.timeouts = []) :
    let runtime := supported.resolvingRuntime nullValue window
    ∃ responses : FinDist (List runtime.messageApplication.EnvironmentEntry →
        runtime.messageApplication.EnvironmentObservation →
        runtime.messageApplication.EnvironmentPolicyCommand),
      responses.bind (fun response => (runPolicyNodes supported.graphWF hguards profile
        ⟨Config.initial G, .initial⟩ G.nodeOrder).map fun cfg =>
        supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
          response schedule) =
        runtime.messageApplication.tracePolicies
          (fun who => supported.resolvingPolicy nullValue window who (profile who))
          environment schedule (PolicyExecution.initial _ (State.initial _ runtime.initial)) := by
  intro runtime
  let players := fun who => supported.resolvingPolicy nullValue window who (profile who)
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  obtain ⟨responses, hresponses⟩ :=
    runtime.messageApplication.exists_environment_response_mixture_tracePolicies
      players environment schedule initial
  refine ⟨responses, ?_⟩
  apply PolicyTrace.law_eq_of_prefixThrough_eq _ _ stop
  · rw [FinDist.map_bind]
    have hmapped := congrArg (FinDist.map (PolicyTrace.prefixThrough stop)) hresponses
    rw [FinDist.map_bind] at hmapped
    refine Eq.trans ?_ hmapped
    apply FinDist.bind_congr
    intro response _
    rw [FinDist.map_comp]
    exact supported.graphRun_native_prefix_law hguards nullValue window response schedule
      fallback profile
  · intro trace htrace
    obtain ⟨front, suffix, _, _, hsuffix⟩ :=
      runtime.messageApplication.tracePolicies_firstRelease_split players environment stop
        schedule initial trace htrace
    have hbefore := runtime.runPolicies_clear_before players environment suffix
      (trace.firstRelease stop) trace.last hsuffix (hclear trace htrace)
    simp only [PolicyTrace.prefixThrough_last, stop, hbefore, List.isEmpty_nil, Bool.not_true]

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.graphRun_native_prefix_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.graphRun_native_prefix_law

/-- info: 'Vegas.EventGraph.SealedFragment.exists_honest_replay_mixture' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.exists_honest_replay_mixture

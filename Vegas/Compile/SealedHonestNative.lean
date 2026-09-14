/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestLikelihood
import Vegas.Compile.SealedPolicyProgress
import Interaction.SealedResolutionLikelihood
import Interaction.MessageApplicationPredraw
import Interaction.MessageApplicationContinuation

/-! # Original all-player source law through first timeout

The source cylinder mass and the native registration mass count the same
conditional probabilities for every player. Their equality identifies the
complete native prefix law under the original source profile. The environment
is a fixed response function of its actual history and view, including pending
traffic. No service or termination premise is needed for the prefix law.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)
variable (nullValue : L.Val ty) (window : Nat)
variable (environment :
  List
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.EnvironmentEntry →
  (compilation.supported.resolvingRuntime nullValue
    window).messageApplication.EnvironmentObservation →
  (compilation.supported.resolvingRuntime nullValue
    window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

omit [Fintype Player] in
/-- An actual fresh registration has the same original source probability as
the recorded checkpoint for that slot. The two snapshots need not coincide. -/
theorem assigned_registration_factor
    [Finite Player]
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := compilation.supported.resolvingAssignedPlayers nullValue window reference
    let env := fun history view => FinDist.pure (environment history view)
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let trace := compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule
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
      (who, slot) ∈ source.core.prog.decisionPositions ∧
      initial.native.application.service.lookup (who, slot) = none ∧
      (compilation.compileResolvingPolicy nullValue window who (profile who)
        (initial.principalHistory who)
        (State.observe runtime.messageApplication initial.native who)).prob
          (.privateCommand ⟨(slot, value)⟩) =
        compilation.assignedRegistrationFactor nullValue window environment schedule
          reference profile who slot := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  let fallback := nullValue
  intro runtime players env stop trace stopped before initial who slot value next after
    hbefore hcommand hnext hafter hstop
  let restricted := (compilation.registrationRestriction (fun _ => true)
    stopped.last.native.application.service).apply profile
  obtain ⟨cfg, hcfg⟩ := (source.sourceRealization restricted).support_nonempty
  have hterminal := source.sourceRealization_terminal restricted cfg hcfg
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
    exact compilation.sourceRealization_registered (fun _ => true)
      stopped.last.native.application.service profile fallback cfg hcfg owner rfl
      node guard hsem registered
      (runtime.runPolicies_lookup_of_eq_some players env (.player who :: after) initial _
        (owner, node.val) registered hlookup hrest)
  obtain ⟨final, hfinal, Δ, name, choiceTy, sourceGuard, site, hdepth, hprob⟩ :=
    compilation.registration_source_probability nullValue window fallback cfg hterminal initial
      hclear hmemory (hbinding.copy rfl rfl) hvalues who
      (compilation.supported.valuePolicy reference who) (profile who) slot value hcommand
  have hfresh := compilation.supported.resolvingPolicy_registration_fresh nullValue window who
    (compilation.supported.valuePolicy reference who) initial hmemory slot value hcommand
  have hnew : next.native.application.service.lookup (who, slot) = some value := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hnext
    subst next
    exact (initial.native.application.service.seal_first who slot value hfresh).2
  have hlookup := runtime.runPolicies_lookup_of_eq_some players env after next stopped.last
    (who, slot) value hnew hafter
  have htrace : trace ∈ (runtime.messageApplication.tracePolicies players env schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
    rw [compilation.supported.resolvingAssignedReplay_law, FinDist.mem_support_pure]
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
  obtain ⟨otherFinal, hotherFinal, otherΔ, otherName, otherTy, otherGuard, otherSite,
      otherDepth, otherProb⟩ :=
    compilation.assignedReplay_registration_probability nullValue window environment schedule
      fallback reference profile release cfg hcfg hcheckpointClear who slot value
      hcheckpoint.2 (profile who)
  have hfinalEq : otherFinal = final := Option.some.inj (hotherFinal.symm.trans hfinal)
  subst otherFinal
  have hmem : (who, slot) ∈ source.core.prog.decisionPositions := by
    rw [← hdepth]
    exact site.decisionPositions_mem
  obtain ⟨rfl, rfl, rfl, hguard, hsite⟩ :=
    otherSite.indices_eq_of_depth_eq site (otherDepth.trans hdepth.symm)
  cases eq_of_heq hguard
  cases eq_of_heq hsite
  refine ⟨hmem, hfresh, ?_⟩
  simp only [assignedRegistrationFactor]
  erw [hlookup]
  exact (hprob value).trans (otherProb value).symm

omit [Fintype Player] in
/-- The native mass of each queried replay prefix is the product of all
original source registration factors. Nonregistration commands add no draw. -/
theorem assignedReplay_prefix_prob_eq_product
    [Finite Player]
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who => compilation.compileResolvingPolicy nullValue window who (profile who)
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough stop
    ((runtime.messageApplication.tracePolicies players
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough stop)).prob stopped =
      (source.core.prog.decisionPositions.map fun slot =>
        compilation.assignedRegistrationFactor nullValue window environment schedule
          reference profile slot.1 slot.2).prod := by
  classical
  intro runtime players stop stopped
  let referencePlayers := compilation.supported.resolvingAssignedPlayers nullValue window reference
  let handles := source.core.prog.decisionPositions.toFinset
  let factor := fun slot : CommitmentHandle Player Nat =>
    compilation.assignedRegistrationFactor nullValue window environment schedule
      reference profile slot.1 slot.2
  have htrace : stopped ∈ ((runtime.messageApplication.tracePolicies referencePlayers
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
        (PolicyTrace.prefixThrough stop)).support := by
    rw [compilation.supported.resolvingAssignedReplay_law, FinDist.map_pure,
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
        obtain ⟨hmem, hfresh, hfactor⟩ := compilation.assigned_registration_factor nullValue window
          environment schedule reference profile before initial who slot value next after
          hbefore hcommand hnext hafter hstop
        rw [hfactor, SealedResolution.registrationFactor,
          if_pos ⟨List.mem_toFinset.mpr hmem, hfresh⟩]
    | submit payload | replay id | wait =>
        dsimp only [players]
        have hlaw := compilation.supported.selected_nonregistration_law who
          initial.native.application.visible.timeouts
          (compilation.supported.valuePolicy reference who)
          (compileSourcePolicy source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
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
        simp only [factor, assignedRegistrationFactor]
        erw [hlookup]
  rw [Finset.prod_congr rfl hweight]
  exact List.prod_toFinset factor source.core.prog.decisionPositions_nodup

/-- Exact pending-message prefix law of the original source profile. Every
player's source kernel is retained, including all of its dependent choices.
This stops only the proof readout at first timeout, not the operational runner. -/
theorem sourceRealization_native_prefix_law (fallback : L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who => compilation.compileResolvingPolicy nullValue window who (profile who)
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (source.sourceRealization profile).map (fun cfg =>
      (compilation.supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
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
  exact (compilation.sourceRealization_replay_prob_eq_product nullValue window environment schedule
    fallback (cfg.1.nodeValues fallback) profile).trans
      (compilation.assignedReplay_prefix_prob_eq_product nullValue window environment schedule
        (cfg.1.nodeValues fallback) profile).symm

/-- When actual all-compiled executions have no timeouts, their full native
trace law is obtained by replaying the original source realization and a finite
mixture of environment responses. Only the environment is predrawn; the source
profile and all its conditional choices are unchanged in every mixture term. -/
theorem exists_honest_replay_mixture
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog)
    (environment :
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.EnvironmentPolicy)
    (hclear : ∀ trace ∈
      ((compilation.supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        (fun who => compilation.compileResolvingPolicy nullValue window who (profile who))
        environment schedule (PolicyExecution.initial _ (State.initial _
          (compilation.supported.resolvingRuntime nullValue window).initial))).support,
      trace.last.native.application.visible.timeouts = []) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    ∃ responses : FinDist (List runtime.messageApplication.EnvironmentEntry →
        runtime.messageApplication.EnvironmentObservation →
        runtime.messageApplication.EnvironmentPolicyCommand),
      responses.bind (fun response => (source.sourceRealization profile).map fun cfg =>
        compilation.supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
          response schedule) =
        runtime.messageApplication.tracePolicies
          (fun who => compilation.compileResolvingPolicy nullValue window who (profile who))
          environment schedule (PolicyExecution.initial _ (State.initial _ runtime.initial)) := by
  intro runtime
  let players := fun who => compilation.compileResolvingPolicy nullValue window who (profile who)
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
    exact compilation.sourceRealization_native_prefix_law nullValue window response schedule
      fallback profile
  · intro trace htrace
    obtain ⟨front, suffix, _, _, hsuffix⟩ :=
      runtime.messageApplication.tracePolicies_firstRelease_split players environment stop
        schedule initial trace htrace
    have hbefore := runtime.runPolicies_clear_before players environment suffix
      (trace.firstRelease stop) trace.last hsuffix (hclear trace htrace)
    simp only [PolicyTrace.prefixThrough_last, stop, hbefore, List.isEmpty_nil, Bool.not_true]

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.sourceRealization_native_prefix_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.sourceRealization_native_prefix_law

/-- info: 'Vegas.SealedCompilation.exists_honest_replay_mixture' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.exists_honest_replay_mixture

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceRestriction

/-! # Source events for exact native replay cylinders

The restriction event is defined on written-source terminal environments.
Compiler field agreement identifies it with the occupied honest slots of a
native prefix. The native replay characterization then identifies precisely
the executions whose probability is being calculated.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}
variable (compilation : SealedCompilation source ty)

variable [Fintype Player] [DecidableEq (L.Val ty)]
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
variable (environment :
  List
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  MessageApplication.EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  MessageApplication.EnvironmentPolicyCommand
    (compilation.supported.resolvingRuntime nullValue window).messageApplication)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- The original honest kernel's probability of an occupied replay slot,
evaluated at its pre-timeout registration checkpoint. Focal and unoccupied
slots contribute one. These factors depend on the fixed native replay and the
original policies, not on the reference source realization. -/
def replayRegistrationFactor
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player) (slot : Nat) : ℝ :=
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let trace := compilation.supported.resolvingReplay nullValue window reference focal
    deviator environment schedule
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  if who = focal then 1 else
    match (trace.prefixThrough stop).last.native.application.service.lookup (who, slot) with
    | none => 1
    | some value =>
        let selected := runtime.registrationCheckpoint
          (compilation.supported.resolvingValuePlayers nullValue window reference focal
            (fun history view => FinDist.pure (deviator history view))) trace stop who slot value
        (compilation.compileResolvingPolicy nullValue window who (profile who)
          (selected.principalHistory who)
          (State.observe runtime.messageApplication selected.native who)).prob
            (.privateCommand ⟨(slot, value)⟩)

omit [Fintype Player] in
/-- The forced-choice likelihood is constant on the entire reference source
law. Its factors are the original native registration probabilities at fixed
replay checkpoints, including factors of probability zero. -/
theorem restrictedSourceRun_weight_eq_product [Finite Player]
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    let restriction := compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
      stopped.last.native.application.service.lookup
    let original : SourceBehavioralProfile source.core.prog :=
      Profile.update (sig := sourceGameSignature source.core.prog) profile focal
        (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
          fallback)
    ∀ final ∈ (denoteSource source.core.prog (restriction.apply original) source.core.env).support,
      restriction.weight original source.core.env final =
        (source.core.prog.decisionPositions.map fun slot =>
          compilation.replayRegistrationFactor nullValue window focal deviator environment schedule
            reference profile slot.1 slot.2).prod := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  intro runtime stopped restriction original final hfinal
  have hrealization := compilation.restrictedSourceRun_source nullValue window focal deviator
    environment schedule fallback stopped.last.native.application.service profile
  have hsome : some final ∈ ((denoteSource source.core.prog (restriction.apply original)
      source.core.env).map some).support := by
    rw [FinDist.support_map]
    exact ⟨final, hfinal, rfl⟩
  rw [← hrealization, FinDist.support_map] at hsome
  obtain ⟨cfg, hcfg, hobserve⟩ := hsome
  apply SourceChoiceRestriction.weight_eq_decision_product source.core.prog original
    (restriction.apply original) restriction source.core.env final hfinal
  intro who Δ name choiceTy guard site
  dsimp only
  by_cases hwho : who = focal
  · subst who
    have hselected : decide (focal ≠ focal) = false := by simp
    constructor
    · intro _
      simp [replayRegistrationFactor]
    · intro fixed hfixed
      simp only [restriction, recordedChoiceRestriction, hselected, Bool.false_eq_true,
        ↓reduceIte] at hfixed
      cases hfixed
  · cases hlookup : stopped.last.native.application.service.lookup (who, site.depth) with
    | none =>
        have hselected : decide (who ≠ focal) = true := by simp [hwho]
        constructor
        · intro _
          simp only [replayRegistrationFactor, if_neg hwho]
          erw [hlookup]
        · intro fixed hfixed
          simp only [restriction, recordedChoiceRestriction, hselected, ↓reduceIte, hlookup,
            Option.map_none] at hfixed
          cases hfixed
    | some value =>
        have hselected : decide (who ≠ focal) = true := by simp [hwho]
        constructor
        · intro hnone
          simp only [restriction, recordedChoiceRestriction, hselected, ↓reduceIte, hlookup,
            Option.map_some] at hnone
          cases hnone
        · intro fixed hfixed
          have hvalue := compilation.recordedChoiceRestriction_fixed_value
            (fun owner => decide (owner ≠ focal)) stopped.last.native.application.service.lookup who
            (by simp [hwho]) site _ value hlookup fixed hfixed
          let trace := compilation.supported.resolvingReplay nullValue window reference focal
            deviator environment schedule
          let stop := fun execution : runtime.messageApplication.PolicyExecution =>
            !execution.native.application.visible.timeouts.isEmpty
          let players := compilation.supported.resolvingValuePlayers nullValue window reference
            focal (fun history view => FinDist.pure (deviator history view))
          let release := fun execution : runtime.messageApplication.PolicyExecution =>
            !stop execution && decide (.privateCommand ⟨(site.depth, value)⟩ ∈
              (players who (execution.principalHistory who)
                (State.observe runtime.messageApplication execution.native who)).support)
          have htrace : trace ∈ (runtime.messageApplication.tracePolicies players
              (fun history view => FinDist.pure (environment history view)) schedule
              (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
            rw [compilation.supported.resolvingReplay_law, FinDist.mem_support_pure]
          have hselected := runtime.registrationCheckpoint_selected players
            (fun history view => FinDist.pure (environment history view)) schedule _ trace
            htrace stop who site.depth value (by intro h; cases h) hlookup
          have hclear :
              (stopped.firstRelease release).native.application.visible.timeouts = [] := by
            have hstop := hselected.1
            simpa only [SealedResolution.registrationCheckpoint, stop,
              Bool.not_eq_eq_eq_not, Bool.not_false, List.isEmpty_iff] using hstop
          obtain ⟨outcome, houtcome, ctx, label, actionTy, sourceGuard, actual, hdepth, hprob⟩ :=
            compilation.restrictedSourceRun_registration_probability nullValue window focal
              deviator environment schedule fallback reference profile release cfg hcfg hclear who
              hwho site.depth value hselected.2 (profile who)
          have heq : outcome = final := Option.some.inj (houtcome.symm.trans hobserve)
          subst outcome
          obtain ⟨rfl, rfl, rfl, hguard, hsite⟩ := actual.indices_eq_of_depth_eq site hdepth
          cases eq_of_heq hguard
          cases eq_of_heq hsite
          have hmass : ((profile who actual ((actual.recorded final).tail.toView who).eraseEnv).map
                (fun choice => (⟨actionTy, choice.1⟩ : TypedValue L))).prob ⟨actionTy, fixed.1⟩ =
              ((profile who actual ((actual.recorded final).tail.toView who).eraseEnv).map
                Subtype.val).prob fixed.1 := by
            rw [FinDist.prob_map_eq_probOf_preimage_singleton,
              FinDist.prob_map_eq_probOf_preimage_singleton]
            apply FinDist.probOf_congr
            intro choice _
            simp only [Set.mem_preimage, Set.mem_singleton_iff, TypedValue.mk.injEq,
              heq_eq_eq, true_and]
          have hnative := hprob value
          rw [← hvalue] at hnative
          have hfactor := hnative.trans hmass
          simp only [replayRegistrationFactor, if_neg hwho, original,
            Profile.update_of_ne _ _ hwho]
          erw [hlookup]
          exact hfactor

/-- The native replay event and the written-source restriction event are
equivalent on the original source law, with opponents unchanged. This is an
event equivalence, not an equality with the original native probability law. -/
theorem extractedSourceRun_replay_iff_restriction
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support) :
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
      deviator environment schedule).prefixThrough release = stopped ↔
      ∃ final, observeSourceOutcome source.core cfg = some final ∧
        (compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
          stopped.last.native.application.service.lookup).Allows
          source.core.env final := by
  intro stopped
  have hterminal := compilation.extractedSourceRun_terminal nullValue window focal deviator
    environment schedule fallback profile cfg hcfg
  let final := decodeSourceOutcome source.core.prog source.core.fresh
    (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
    cfg hterminal
  have hobserve : observeSourceOutcome source.core cfg = some final :=
    observeSourceOutcome_of_terminal source.core cfg hterminal
  have hsource : final ∈ (denoteSource source.core.prog
      (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
        (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
          fallback)) source.core.env).support := by
    have hmapped : some final ∈ ((compilation.extractedSourceRun nullValue window focal deviator
        environment schedule fallback profile).map (observeSourceOutcome source.core)).support := by
      rw [FinDist.support_map]
      exact ⟨cfg, hcfg, hobserve⟩
    rw [compilation.extractedSourceRun_source, FinDist.support_map] at hmapped
    obtain ⟨actual, hactual, heq⟩ := hmapped
    exact Option.some.inj heq ▸ hactual
  have hallow :
      (∃ outcome, observeSourceOutcome source.core cfg = some outcome ∧
        (compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
          stopped.last.native.application.service.lookup).Allows
          source.core.env outcome) ↔
      (compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        stopped.last.native.application.service.lookup).Allows
        source.core.env final := by
    constructor
    · rintro ⟨outcome, houtcome, h⟩
      rw [hobserve] at houtcome
      cases Option.some.inj houtcome
      exact h
    · exact fun h => ⟨final, hobserve, h⟩
  have hfields := compilation.recordedChoiceRestriction_allows_iff_store
    (fun who => decide (who ≠ focal)) stopped.last.native.application.service.lookup _ cfg hterminal
    hsource
  have hreplay := compilation.supported.resolvingReplay_prefix_eq_iff_lookup nullValue window
    focal deviator environment schedule release reference (cfg.1.nodeValues fallback)
  refine (hfields.trans (Iff.trans ?_ (eq_comm.trans hreplay).symm)).symm.trans hallow.symm
  constructor
  · intro h who node guard hsem hwho value hlookup
    have hstored := h who node guard hsem (by simp [hwho]) value hlookup
    rw [cfg.1.store_nodeValues
      (reachable_storeCoherent compilation.supported.graphWF cfg.2) fallback node
      (compilation.supported.rowType node) (hterminal node)] at hstored
    exact eq_of_heq (TypedValue.mk.inj (Option.some.inj hstored)).2
  · intro h who node guard hsem hselected value hlookup
    have hwho : who ≠ focal := by simpa using hselected
    rw [cfg.1.store_nodeValues
      (reachable_storeCoherent compilation.supported.graphWF cfg.2) fallback node
      (compilation.supported.rowType node) (hterminal node),
      h who node guard hsem hwho value hlookup]

/-- Exact probability of a replay cylinder under the original written-source
law. Opponent kernels are unchanged; the native runner's own marginal is a
separate comparison. The event may have probability zero. -/
theorem extractedSourceRun_replay_probability
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    ((compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      profile).map fun cfg =>
        (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough release).prob stopped =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
            fallback)) source.core.env).probOf
        {final | (compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
          stopped.last.native.application.service.lookup).Allows source.core.env final} := by
  intro stopped
  apply compilation.replay_probability_of_recorded_choices _ _
    (compilation.extractedSourceRun_source nullValue window focal deviator environment schedule
      fallback profile)
    (compilation.extractedSourceRun_terminal nullValue window focal deviator environment schedule
      fallback profile) _ _ fallback
  intro cfg _hcfg
  rw [eq_comm, compilation.supported.resolvingReplay_prefix_eq_iff_lookup]
  simp only [decide_eq_true_eq, stopped]

/-- The actual source cylinder mass is the original forced-choice likelihood
averaged over the normalized reference source execution. This performs the
source-side summation, including dependent choices and zero-mass cylinders. -/
theorem extractedSourceRun_replay_likelihood
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    let original : SourceBehavioralProfile source.core.prog :=
      Profile.update (sig := sourceGameSignature source.core.prog) profile focal
        (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
          fallback)
    let restriction := compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
      stopped.last.native.application.service.lookup
    ((compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      profile).map fun cfg =>
        (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough release).prob stopped =
      (denoteSource source.core.prog (restriction.apply original) source.core.env).expect
        (restriction.weight original source.core.env) := by
  intro stopped original restriction
  exact (compilation.extractedSourceRun_replay_probability nullValue window focal deviator
    environment schedule fallback reference release profile).trans
      (denoteSource_restriction_probability source.core.prog original restriction source.core.env)

/-- Exact source probability of the native replay prefix through first timeout,
as a product of original native registration probabilities. The reference
expectation has been eliminated. `SealedCompilation.replay_prefix_prob_eq_product`
identifies the same product with the original native runner's prefix mass. -/
theorem extractedSourceRun_replay_prob_eq_product
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough stop
    ((compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      profile).map fun cfg =>
        (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop).prob stopped =
      (source.core.prog.decisionPositions.map fun slot =>
        compilation.replayRegistrationFactor nullValue window focal deviator environment schedule
          reference profile slot.1 slot.2).prod := by
  intro runtime stop stopped
  rw [compilation.extractedSourceRun_replay_likelihood]
  exact (FinDist.expect_congr (compilation.restrictedSourceRun_weight_eq_product nullValue window
    focal deviator environment schedule fallback reference profile)).trans
      (FinDist.expect_const _ _)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_replay_iff_restriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_replay_iff_restriction

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_replay_likelihood' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_replay_likelihood

/-- info: 'Vegas.SealedCompilation.restrictedSourceRun_weight_eq_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.restrictedSourceRun_weight_eq_product

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_replay_prob_eq_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_replay_prob_eq_product

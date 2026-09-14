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

/-- Source restriction acceptance is exactly equality at occupied honest
commitment fields of its decoded graph realization. The source support premise
ensures the queried terminal environment follows the source semantics. -/
theorem registrationRestriction_allows_iff_store (focal : Player)
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1) :
    let final := decodeSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal
    final ∈ (denoteSource source.core.prog profile source.core.env).support →
    ((compilation.registrationRestriction focal service).Allows source.core.env final ↔
      ∀ who (node : Fin (compile source.core).graph.nodeCount) guard,
        ((compile source.core).graph.nodeRow node).sem = .commit who guard → who ≠ focal →
        ∀ value, service.lookup (who, node.val) = some value →
          cfg.1.store ((compile source.core).graph.nodeTarget node) =
            some (⟨ty, value⟩ : TypedValue L)) := by
  intro final hfinal
  rw [compilation.registrationRestriction_allows_iff_recorded focal service profile final hfinal]
  let state := BuildState.fromInitial
    (initialState source.core.Γ source.core.env source.core.wctx)
  constructor
  · intro h who node guard hsem hwho value hlookup
    obtain ⟨actor, Δ, name, choiceTy, sourceGuard, site, hindex, hrow⟩ :=
      compileCore_commitNode_covered source.core.prog source.core.fresh state node (by simp [state])
        ⟨_, who, guard, (compile source.core).graph.nodes_get?_nodeRow node, hsem⟩
    have hrowEq := Option.some.inj
      (((compile source.core).graph.nodes_get?_nodeRow node).symm.trans hrow)
    have hactor := (NodeSem.commit.inj (hsem.symm.trans (congrArg EventNode.sem hrowEq))).1
    subst actor
    have hdepth : site.depth = node.val := by
      simpa only [decisionSiteState_nodes_length,
        show state.nodes.length = 0 from rfl, Nat.zero_add] using hindex.symm
    have hvalue := h who site hwho value (by rw [hdepth]; exact hlookup)
    have hrecord := decisionSite_recorded_value site source.core.fresh state cfg hterminal
    rw [← decisionSite_nodeTarget site source.core.fresh state node hindex] at hrecord
    exact hrecord.trans (congrArg some hvalue)
  · intro h who Δ name choiceTy guard site hwho value hlookup
    obtain ⟨node, hindex, hrow⟩ := decisionSite_compiledRow site source.core.fresh state
    have hsem := congrArg EventNode.sem (Option.some.inj
      (((compile source.core).graph.nodes_get?_nodeRow node).symm.trans hrow))
    have hdepth : site.depth = node.val := by
      simpa only [decisionSiteState_nodes_length,
        show state.nodes.length = 0 from rfl, Nat.zero_add] using hindex.symm
    have hstored := h who node _ hsem hwho value (by rwa [hdepth] at hlookup)
    have hrecord := decisionSite_recorded_value site source.core.fresh state cfg hterminal
    rw [← decisionSite_nodeTarget site source.core.fresh state node hindex] at hrecord
    exact Option.some.inj (hrecord.symm.trans hstored)

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
        (compilation.registrationRestriction focal stopped.last.native.application.service).Allows
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
        (compilation.registrationRestriction focal stopped.last.native.application.service).Allows
          source.core.env outcome) ↔
      (compilation.registrationRestriction focal stopped.last.native.application.service).Allows
        source.core.env final := by
    constructor
    · rintro ⟨outcome, houtcome, h⟩
      rw [hobserve] at houtcome
      cases Option.some.inj houtcome
      exact h
    · exact fun h => ⟨final, hobserve, h⟩
  have hfields := compilation.registrationRestriction_allows_iff_store focal
    stopped.last.native.application.service _ cfg hterminal hsource
  have hreplay := compilation.supported.resolvingReplay_prefix_eq_iff_lookup nullValue window
    focal deviator environment schedule release reference (cfg.1.nodeValues fallback)
  refine (hfields.trans (Iff.trans ?_ (eq_comm.trans hreplay).symm)).symm.trans hallow.symm
  constructor
  · intro h who node guard hsem hwho value hlookup
    have hstored := h who node guard hsem hwho value hlookup
    rw [cfg.1.store_nodeValues
      (reachable_storeCoherent compilation.supported.graphWF cfg.2) fallback node
      (compilation.supported.rowType node) (hterminal node)] at hstored
    exact eq_of_heq (TypedValue.mk.inj (Option.some.inj hstored)).2
  · intro h who node guard hsem hwho value hlookup
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
        {final | (compilation.registrationRestriction focal
          stopped.last.native.application.service).Allows source.core.env final} := by
  intro stopped
  let event : Set (Option (VEnv L (sourceTerminalCtx source.core.prog))) :=
    {outcome | ∃ final, outcome = some final ∧
      (compilation.registrationRestriction focal stopped.last.native.application.service).Allows
        source.core.env final}
  have hsource := congrArg (fun law => law.probOf event)
    (compilation.extractedSourceRun_source nullValue window focal deviator environment schedule
      fallback profile)
  rw [FinDist.probOf_map, FinDist.probOf_map] at hsource
  rw [FinDist.prob_map_eq_probOf_preimage_singleton]
  refine (FinDist.probOf_congr _ (second := observeSourceOutcome source.core ⁻¹' event)
    (fun cfg hcfg => compilation.extractedSourceRun_replay_iff_restriction nullValue window focal
      deviator environment schedule fallback reference release profile cfg hcfg)).trans
        (hsource.trans ?_)
  congr 1
  ext final
  simp only [event, Set.mem_preimage, Set.mem_ofPred_eq, Option.some.injEq]
  constructor
  · rintro ⟨outcome, rfl, h⟩
    exact h
  · exact fun h => ⟨final, rfl, h⟩

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
    let restriction := compilation.registrationRestriction focal
      stopped.last.native.application.service
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

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_replay_iff_restriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_replay_iff_restriction

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_replay_likelihood' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_replay_likelihood

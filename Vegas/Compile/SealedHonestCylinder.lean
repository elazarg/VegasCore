/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestSource
import Vegas.Compile.SealedSourceCylinder
import Vegas.Compile.SealedAssignedReplay

/-! # All-player source cylinders for pending-message replay

Every player's kernel belongs to the original source profile. Restricting all
occupied native slots selects exactly the source realizations that replay the
same native prefix. This accounts for all source randomness, including games
with a single player; no player is selected as a deterministic replacement.
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
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  MessageApplication.EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  MessageApplication.EnvironmentPolicyCommand
    (compilation.supported.resolvingRuntime nullValue window).messageApplication)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- Fixing the occupied slots of every player reproduces the entire native
prefix, including private histories, pending packets, and public clock state. -/
theorem sourceRealization_restricted_replay
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough release
    ∀ cfg ∈ (source.sourceRealization
      ((compilation.recordedChoiceRestriction (fun _ => true)
        stopped.last.native.application.service.lookup).apply profile)).support,
      (compilation.supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
        environment schedule).prefixThrough release = stopped := by
  intro stopped cfg hcfg
  apply Eq.symm
  apply (compilation.supported.resolvingAssignedReplay_prefix_eq_iff_lookup nullValue window
    environment schedule release reference (cfg.1.nodeValues fallback)).mpr
  intro owner node guard hsem value hlookup
  exact compilation.sourceRealization_registered (fun _ => true)
    stopped.last.native.application.service profile fallback cfg hcfg owner rfl
    node guard hsem value hlookup

/-- A replay cylinder is exactly the selected-registration event on the
original written-source law. The source marginal has no replaced policy. -/
theorem sourceRealization_replay_iff_restriction
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (source.sourceRealization profile).support) :
    let stopped := (compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough release
    (compilation.supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
      environment schedule).prefixThrough release = stopped ↔
      ∃ final, observeSourceOutcome source.core cfg = some final ∧
        (compilation.recordedChoiceRestriction (fun _ => true)
          stopped.last.native.application.service.lookup).Allows source.core.env final := by
  intro stopped
  have hterminal := source.sourceRealization_terminal profile cfg hcfg
  let final := decodeSourceOutcome source.core.prog source.core.fresh
    (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
    cfg hterminal
  have hobserve : observeSourceOutcome source.core cfg = some final :=
    observeSourceOutcome_of_terminal source.core cfg hterminal
  have hsource : final ∈ (denoteSource source.core.prog profile source.core.env).support := by
    have hmapped : some final ∈
        ((source.sourceRealization profile).map (observeSourceOutcome source.core)).support := by
      rw [FinDist.support_map]
      exact ⟨cfg, hcfg, hobserve⟩
    rw [source.sourceRealization_source, FinDist.support_map] at hmapped
    obtain ⟨actual, hactual, heq⟩ := hmapped
    exact Option.some.inj heq ▸ hactual
  have hfields := compilation.recordedChoiceRestriction_allows_iff_store (fun _ => true)
    stopped.last.native.application.service.lookup profile cfg hterminal hsource
  have hallow :
      (∃ outcome, observeSourceOutcome source.core cfg = some outcome ∧
        (compilation.recordedChoiceRestriction (fun _ => true)
          stopped.last.native.application.service.lookup).Allows source.core.env outcome) ↔
      (compilation.recordedChoiceRestriction (fun _ => true)
        stopped.last.native.application.service.lookup).Allows source.core.env final := by
    constructor
    · rintro ⟨outcome, houtcome, h⟩
      rw [hobserve] at houtcome
      cases Option.some.inj houtcome
      exact h
    · exact fun h => ⟨final, hobserve, h⟩
  rw [hallow, hfields, eq_comm,
    compilation.supported.resolvingAssignedReplay_prefix_eq_iff_lookup]
  constructor
  · intro h owner node guard hsem _ value hlookup
    rw [cfg.1.store_nodeValues (reachable_storeCoherent compilation.supported.graphWF cfg.2)
      fallback node (compilation.supported.rowType node) (hterminal node),
      h owner node guard hsem value hlookup]
  · intro h owner node guard hsem value hlookup
    have hstored := h owner node guard hsem rfl value hlookup
    rw [cfg.1.store_nodeValues (reachable_storeCoherent compilation.supported.graphWF cfg.2)
      fallback node (compilation.supported.rowType node) (hterminal node)] at hstored
    exact eq_of_heq (TypedValue.mk.inj (Option.some.inj hstored)).2

/-- The original source probability of a native replay prefix is the
probability of its occupied-slot restriction, including zero-mass prefixes. -/
theorem sourceRealization_replay_probability
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough release
    ((source.sourceRealization profile).map fun cfg =>
      (compilation.supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
        environment schedule).prefixThrough release).prob stopped =
      (denoteSource source.core.prog profile source.core.env).probOf
        {final | (compilation.recordedChoiceRestriction (fun _ => true)
          stopped.last.native.application.service.lookup).Allows source.core.env final} := by
  intro stopped
  let event : Set (Option (VEnv L (sourceTerminalCtx source.core.prog))) :=
    {outcome | ∃ final, outcome = some final ∧
      (compilation.recordedChoiceRestriction (fun _ => true)
        stopped.last.native.application.service.lookup).Allows source.core.env final}
  have hsource := congrArg (fun law => law.probOf event)
    (source.sourceRealization_source profile)
  rw [FinDist.probOf_map, FinDist.probOf_map] at hsource
  rw [FinDist.prob_map_eq_probOf_preimage_singleton]
  refine (FinDist.probOf_congr _ (second := observeSourceOutcome source.core ⁻¹' event)
    (fun cfg hcfg => compilation.sourceRealization_replay_iff_restriction nullValue window
      environment schedule fallback reference release profile cfg hcfg)).trans
        (hsource.trans ?_)
  congr 1
  ext final
  simp only [event, Set.mem_preimage, Set.mem_ofPred_eq, Option.some.injEq]
  constructor
  · rintro ⟨outcome, rfl, h⟩
    exact h
  · exact fun h => ⟨final, rfl, h⟩

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.sourceRealization_restricted_replay' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.sourceRealization_restricted_replay

/-- info: 'Vegas.SealedCompilation.sourceRealization_replay_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.sourceRealization_replay_probability

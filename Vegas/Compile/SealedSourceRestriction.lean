/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceAssignment
import Vegas.Compile.SealedSourceChoices

/-! # Source restrictions from occupied native commitment slots

The prefix's private service supplies the recorded honest choices. Its occupied
source slots are fixed in a normalized reference source execution; every other
honest kernel and the extracted focal policy remain unchanged. This reference
law is used to calculate cylinder probabilities, not as the source marginal
of the strategic simulation.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}
variable (compilation : SealedCompilation source ty)

variable [DecidableEq (L.Val ty)] [Fintype Player]
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

/-- The graph reference run has exactly the ordinary restricted source law,
with the same extracted focal policy on both sides. -/
theorem restrictedSourceRun_source
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        service.lookup).apply profile)).map
        (observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
          service.lookup).apply
          (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
            (compilation.extractedSourcePolicy nullValue window focal deviator environment
              schedule fallback))) source.core.env).map some := by
  rw [compilation.extractedSourceRun_source,
    compilation.recordedChoiceRestriction_apply_update _ focal (by simp)]

/-- Every reference source run retains all occupied honest source slots from
the specified native service. Unrecorded honest choices remain probabilistic. -/
theorem restrictedSourceRun_registered
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback
        ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
          service.lookup).apply profile)).support)
    (who : Player) (hwho : who ≠ focal)
    (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
    (value : L.Val ty) (hlookup : service.lookup (who, node.val) = some value) :
    cfg.1.nodeValues fallback node = value := by
  have hterminal := compilation.extractedSourceRun_terminal nullValue window focal deviator
    environment schedule fallback _ cfg hcfg
  have hchoices := runPolicyNodes_support_commitValues (compile source.core).graphWF
    (compile_guardLive source.core source.legal) _ _ (CommitValuesSupported.initial _)
    (compile source.core).graph.nodeOrder cfg hcfg
  obtain ⟨reads, _, choice, hchoice, hvalue⟩ := hchoices node (hterminal node) who guard hsem
  rw [Profile.update_of_ne _ _ hwho,
    compilation.compile_recordedChoiceRestriction (fun owner => decide (owner ≠ focal))
      service.lookup
      profile who node guard hsem reads] at hchoice
  have hselected : decide (who ≠ focal) = true := by simp [hwho]
  rw [hselected] at hchoice
  simp only [if_true, hlookup, SealedFragment.valuePolicy, FinDist.mem_support_pure] at hchoice
  subst choice
  change cfg.1.store ((compile source.core).graph.nodeTarget node) =
    some (⟨guard.ty, cast (congrArg L.Val
      (compilation.supported.commitType node who guard hsem).symm) value⟩ : TypedValue L) at hvalue
  rw [Config.nodeValues, Store.getAs, hvalue]
  simp only [TypedValue.as?, dif_pos (compilation.supported.commitType node who guard hsem),
    cast_cast, cast_eq, Option.getD_some]

/-- Every supported reference source realization reproduces the complete
recorded native prefix: histories, pending pool, clock, and receipts included.
Only the honest slots occupied by that prefix are fixed. -/
theorem restrictedSourceRun_replay_prefix
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    ∀ cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        stopped.last.native.application.service.lookup).apply profile)).support,
      (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).prefixThrough release = stopped := by
  intro stopped cfg hcfg
  apply Eq.symm
  apply (compilation.supported.resolvingReplay_prefix_eq_iff nullValue window focal deviator
    environment schedule release reference (cfg.1.nodeValues fallback)).mpr
  intro owner node value howner hrecord
  obtain ⟨hlookup, guard, hsem⟩ := compilation.supported.resolvingReplay_registration_lookup
    nullValue window focal deviator environment schedule release reference owner node value
    howner hrecord
  exact (compilation.restrictedSourceRun_registered nullValue window focal deviator environment
    schedule fallback stopped.last.native.application.service profile cfg hcfg owner howner
    node guard hsem (reference node) hlookup).symm

/-- Throughout the reference law, each fresh honest registration before first
timeout has the same original source kernel as at the recorded native input.
The reference run need not have positive mass under the compared profile. -/
theorem restrictedSourceRun_registration_kernel
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let tracePrefix := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∀ cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        tracePrefix.last.native.application.service.lookup).apply profile)).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.resolvingValuePlayers nullValue window reference focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who)
          (State.observe runtime.messageApplication stopped.native who)).support →
      ∀ policy : SourceBehavioralPolicy source.core.prog who,
      ∃ (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
        (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = none ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        compilation.compileResolvingPolicy nullValue window who policy
          (stopped.principalHistory who) (State.observe runtime.messageApplication stopped.native
            who) =
          ((compileSourcePolicy source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
            rfl who policy) node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (compilation.supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro runtime tracePrefix cfg hcfg stopped hclear who hwho slot value hcommand policy
  have hreplay := compilation.restrictedSourceRun_replay_prefix nullValue window focal deviator
    environment schedule fallback reference
    (fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty) profile cfg hcfg
  have hkernel := compilation.extractedSourceRun_registration_kernel nullValue window focal
    deviator environment schedule fallback _ cfg hcfg release
  dsimp only at hkernel
  rw [hreplay] at hkernel
  obtain ⟨assigned, hassigned⟩ :=
    compilation.supported.resolvingValuePlayers_registration_transfer nullValue window reference
      (cfg.1.nodeValues fallback) focal (fun history view => FinDist.pure (deviator history view))
      who hwho (stopped.principalHistory who)
      (State.observe runtime.messageApplication stopped.native who) slot value hcommand
  exact hkernel hclear who hwho slot assigned hassigned policy

/-- Every fresh registration factor before first timeout is the original
written-source decision probability at the reference run's recorded view.
The equality covers every queried value, including values of probability zero;
the compared policy is independent of the profile generating the reference. -/
theorem restrictedSourceRun_registration_probability
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let tracePrefix := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∀ cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback ((compilation.recordedChoiceRestriction (fun who => decide (who ≠ focal))
        tracePrefix.last.native.application.service.lookup).apply profile)).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.resolvingValuePlayers nullValue window reference focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who)
          (State.observe runtime.messageApplication stopped.native who)).support →
    ∀ policy : SourceBehavioralPolicy source.core.prog who,
    ∃ final, observeSourceOutcome source.core cfg = some final ∧
      ∃ Δ name choiceTy guard, ∃ site :
        SourceDecisionSite who source.core.prog Δ name choiceTy guard,
        site.depth = slot ∧ ∀ chosen,
          (compilation.compileResolvingPolicy nullValue window who policy
            (stopped.principalHistory who)
            (State.observe runtime.messageApplication stopped.native who)).prob
              (.privateCommand ⟨(slot, chosen)⟩) =
            ((policy site ((site.recorded final).tail.toView who).eraseEnv).map
              (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))).prob ⟨ty, chosen⟩ := by
  intro runtime tracePrefix cfg hcfg stopped hclear who hwho slot value hcommand policy
  obtain ⟨node, guard, hsem, reads, hslot, _, hreads, hkernel⟩ :=
    compilation.restrictedSourceRun_registration_kernel nullValue window focal deviator
      environment schedule fallback reference profile release cfg hcfg hclear who hwho
      slot value hcommand policy
  have hterminal := compilation.extractedSourceRun_terminal nullValue window focal deviator
    environment schedule fallback _ cfg hcfg
  obtain ⟨Δ, name, choiceTy, sourceGuard, site, hdepth, hlaw⟩ :=
    compileSourcePolicy_recorded_law source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who policy node guard hsem cfg hterminal reads hreads
  refine ⟨_, observeSourceOutcome_of_terminal source.core cfg hterminal,
    Δ, name, choiceTy, sourceGuard, site, hdepth.trans hslot.symm, ?_⟩
  intro chosen
  rw [hkernel, ← hlaw]
  rw [FinDist.prob_map_eq_probOf_preimage_singleton,
    FinDist.prob_map_eq_probOf_preimage_singleton]
  apply FinDist.probOf_congr
  intro choice _
  have htyped {left right : L.Ty} (heq : left = right)
      (selected : L.Val left) (queried : L.Val right) :
      (⟨left, selected⟩ : TypedValue L) = ⟨right, queried⟩ ↔
        cast (congrArg L.Val heq) selected = queried := by
    cases heq
    simp only [TypedValue.mk.injEq, heq_eq_eq, true_and, cast_eq]
  simp only [Set.mem_preimage, Set.mem_singleton_iff,
    MessageInterface.PlayerCommand.privateCommand.injEq, ← hslot,
    htyped (compilation.supported.commitType node who guard hsem)]
  constructor
  · exact fun h => congrArg (fun request => request.down.2) h
  · intro h
    rw [h]

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.restrictedSourceRun_registered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.restrictedSourceRun_registered

/-- info: 'Vegas.SealedCompilation.restrictedSourceRun_replay_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.restrictedSourceRun_replay_prefix

/-- info: 'Vegas.SealedCompilation.restrictedSourceRun_registration_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.restrictedSourceRun_registration_kernel

/-- info: 'Vegas.SealedCompilation.restrictedSourceRun_registration_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.restrictedSourceRun_registration_probability

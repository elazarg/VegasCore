/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceAssignment
import Vegas.Core.SourceRestriction

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

private theorem valueSourceProfile_pure (value : L.Val ty) (who : Player)
    {Δ name choiceTy guard}
    (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) :
    ∃ choice, compilation.valueSourceProfile (fun _ => value) who site visible =
      FinDist.pure choice := by
  simp only [valueSourceProfile, backtranslateCommitPolicy, backtranslateSourceDecision,
    SealedFragment.valuePolicy, FinDist.map_pure]
  exact ⟨_, rfl⟩

private def sourceChoice (value : L.Val ty) (who : Player)
    {Δ name choiceTy guard}
    (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) :
    {chosen : L.Val choiceTy // evalGuard guard chosen visible = true} :=
  Classical.choose (compilation.valueSourceProfile_pure value who site visible)

private theorem sourceChoice_law (value : L.Val ty) (who : Player)
    {Δ name choiceTy guard}
    (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) :
    FinDist.pure (compilation.sourceChoice value who site visible) =
      compilation.valueSourceProfile (fun _ => value) who site visible :=
  (Classical.choose_spec (compilation.valueSourceProfile_pure value who site visible)).symm

private theorem sourceChoice_value (value : L.Val ty) (who : Player)
    {Δ name choiceTy guard}
    (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) :
    (⟨choiceTy, (compilation.sourceChoice value who site visible).1⟩ : TypedValue L) =
      ⟨ty, value⟩ := by
  have hlaw := congrArg (FinDist.map fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))
    (compilation.sourceChoice_law value who site visible)
  simp only [valueSourceProfile, backtranslateCommitPolicy, backtranslateSourceDecision,
    SealedFragment.valuePolicy, FinDist.map_pure] at hlaw
  have heq := FinDist.mem_support_pure.mp (hlaw ▸ FinDist.mem_support_pure.mpr rfl)
  have hcast {left right : L.Ty} (hty : left = right) (chosen : L.Val right) :
      (⟨left, cast (congrArg L.Val hty.symm) chosen⟩ : TypedValue L) = ⟨right, chosen⟩ := by
    cases hty
    rfl
  let state := BuildState.fromInitial
    (initialState source.core.Γ source.core.env source.core.wctx)
  obtain ⟨node, _, hrow⟩ := decisionSite_compiledRow site source.core.fresh state
  have hsem := congrArg EventNode.sem (Option.some.inj
    (((compile source.core).graph.nodes_get?_nodeRow node).symm.trans hrow))
  exact heq.trans (hcast (compilation.supported.commitType node who
    (eventGuardOf (decisionSiteState site source.core.fresh state) who guard) hsem) value)

/-- Fix exactly the occupied honest source slots. Out-of-program slots and
slots owned by another principal cannot constrain a source decision. The
service is proof-facing snapshot data, not an observation supplied to a player. -/
def registrationRestriction (focal : Player)
    (service : IdealCommitments Player Nat (L.Val ty)) :
    SourceChoiceRestriction source.core.prog :=
  fun who _ _ _ _ site visible =>
    if who = focal then none else
      (service.lookup (who, site.depth)).map fun value =>
        compilation.sourceChoice value who site visible

/-- The legal source choice selected by an occupied honest slot retains that
slot's value and type, independently of the source view used to justify it. -/
theorem registrationRestriction_fixed_value (focal : Player)
    (service : IdealCommitments Player Nat (L.Val ty)) (who : Player) (hwho : who ≠ focal)
    {Δ name choiceTy guard}
    (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ)))
    (value : L.Val ty) (hlookup : service.lookup (who, site.depth) = some value)
    (fixed : {chosen : L.Val choiceTy // evalGuard guard chosen visible = true})
    (hfixed : compilation.registrationRestriction focal service who site visible = some fixed) :
    (⟨choiceTy, fixed.1⟩ : TypedValue L) = ⟨ty, value⟩ := by
  simp only [registrationRestriction, if_neg hwho, hlookup, Option.map_some,
    Option.some.injEq] at hfixed
  subst fixed
  exact compilation.sourceChoice_value value who site visible

/-- A source outcome satisfies the native registration restriction exactly
when its recorded honest source choices equal the occupied service values. -/
theorem registrationRestriction_allows_iff_recorded (focal : Player)
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (final : VEnv L (sourceTerminalCtx source.core.prog))
    (hfinal : final ∈ (denoteSource source.core.prog profile source.core.env).support) :
    (compilation.registrationRestriction focal service).Allows source.core.env final ↔
      ∀ who {Δ name choiceTy guard}
        (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard), who ≠ focal →
        ∀ value, service.lookup (who, site.depth) = some value →
          (⟨choiceTy, (site.recorded final).get .here⟩ : TypedValue L) = ⟨ty, value⟩ := by
  rw [SourceChoiceRestriction.allows_iff_recorded source.core.prog profile _ _ _ hfinal]
  constructor
  · intro h who Δ name choiceTy guard site hwho value hlookup
    have hchoice := h who site
      (compilation.sourceChoice value who site ((site.recorded final).tail.toView who).eraseEnv)
      (by simp only [registrationRestriction, if_neg hwho, hlookup, Option.map_some])
    exact (congrArg (fun chosen => (⟨choiceTy, chosen⟩ : TypedValue L)) hchoice).trans
      (compilation.sourceChoice_value value who site _)
  · intro h who Δ name choiceTy guard site fixed hfixed
    by_cases hwho : who = focal
    · simp only [registrationRestriction, if_pos hwho] at hfixed
      cases hfixed
    · cases hlookup : service.lookup (who, site.depth) with
      | none =>
          simp only [registrationRestriction, if_neg hwho, hlookup, Option.map_none] at hfixed
          cases hfixed
      | some value =>
          simp only [registrationRestriction, if_neg hwho, hlookup, Option.map_some,
            Option.some.injEq] at hfixed
          subst fixed
          have heq := (h who site hwho value hlookup).trans
            (compilation.sourceChoice_value value who site
              ((site.recorded final).tail.toView who).eraseEnv).symm
          exact eq_of_heq (TypedValue.mk.inj heq).2

/-- Applying the reference restriction commutes with replacing the focal
policy. In particular it never alters the extracted source deviator. -/
theorem registrationRestriction_apply_update (focal : Player)
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (replacement : SourceBehavioralPolicy source.core.prog focal) :
    (compilation.registrationRestriction focal service).apply
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal replacement) =
      Profile.update (sig := sourceGameSignature source.core.prog)
        ((compilation.registrationRestriction focal service).apply profile) focal replacement := by
  funext who Δ name choiceTy guard site visible
  by_cases hwho : who = focal
  · subst who
    simp only [SourceChoiceRestriction.apply, registrationRestriction, ↓reduceIte,
      Profile.update_same]
  · simp only [SourceChoiceRestriction.apply, registrationRestriction, if_neg hwho,
      Profile.update_of_ne _ _ hwho]

/-- The reference source profile recompiles to the original graph kernel at
unoccupied or focal slots, and to the recorded value at occupied honest slots. -/
theorem compile_registrationRestriction (focal : Player)
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads) :
    compileSourcePolicy source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        rfl who ((compilation.registrationRestriction focal service).apply profile who)
        node guard hsem reads =
      match (if who = focal then none else service.lookup (who, node.val)) with
      | none => compileSourcePolicy source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          rfl who (profile who) node guard hsem reads
      | some value =>
          compilation.supported.valuePolicy (fun _ => value) who node guard hsem reads := by
  by_cases hwho : who = focal
  · rw [if_pos hwho]
    apply compileSourcePolicy_congr_at_depth
    intro Δ name choiceTy sourceGuard site _
    funext visible
    simp only [SourceChoiceRestriction.apply, registrationRestriction, if_pos hwho]
  · rw [if_neg hwho]
    cases hlookup : service.lookup (who, node.val) with
    | none =>
        apply compileSourcePolicy_congr_at_depth
        intro Δ name choiceTy sourceGuard site hdepth
        funext visible
        simp only [SourceChoiceRestriction.apply, registrationRestriction, if_neg hwho,
          hdepth, hlookup, Option.map_none]
    | some value =>
        have hpolicy := compileSourcePolicy_congr_at_depth source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          rfl who ((compilation.registrationRestriction focal service).apply profile who)
          (compilation.valueSourceProfile (fun _ => value) who) node guard hsem reads
          (by
            intro Δ name choiceTy sourceGuard site hdepth
            funext visible
            simp only [SourceChoiceRestriction.apply, registrationRestriction, if_neg hwho,
              hdepth, hlookup, Option.map_some]
            exact compilation.sourceChoice_law value who site visible)
        exact hpolicy.trans (congrFun (congrFun (congrFun (congrFun
          (compile_backtranslateCommitPolicy source.core who
            (compilation.supported.valuePolicy (fun _ => value) who)) node) guard) hsem) reads)

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
      ((compilation.registrationRestriction focal service).apply profile)).map
        (observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        ((compilation.registrationRestriction focal service).apply
          (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
            (compilation.extractedSourcePolicy nullValue window focal deviator environment
              schedule fallback))) source.core.env).map some := by
  rw [compilation.extractedSourceRun_source, compilation.registrationRestriction_apply_update]

/-- Every reference source run retains all occupied honest source slots from
the specified native service. Unrecorded honest choices remain probabilistic. -/
theorem restrictedSourceRun_registered
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback
        ((compilation.registrationRestriction focal service).apply profile)).support)
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
    compilation.compile_registrationRestriction focal service profile who node guard hsem reads,
    if_neg hwho, hlookup] at hchoice
  simp only [SealedFragment.valuePolicy, FinDist.mem_support_pure] at hchoice
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
      fallback ((compilation.registrationRestriction focal
        stopped.last.native.application.service).apply profile)).support,
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
      fallback ((compilation.registrationRestriction focal
        tracePrefix.last.native.application.service).apply profile)).support,
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
      fallback ((compilation.registrationRestriction focal
        tracePrefix.last.native.application.service).apply profile)).support,
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

/-- info: 'Vegas.SealedCompilation.compile_registrationRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.compile_registrationRestriction

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

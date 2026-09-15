/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCompiler
import Vegas.Compile.SealedGraphRestriction
import Vegas.Compile.SealedReplay
import Vegas.Compile.SourceBacktranslation
import Vegas.Compile.SourceOutcome
import Vegas.Compile.SourceObservation
import Vegas.Core.SourceRestriction
import Vegas.EventGraph.KernelRealization

/-! # Written-source restrictions from recorded choices

A partial map of owner/site coordinates fixes selected source choices in a
normalized reference execution. Unrecorded choices keep their original kernels,
and unselected players are unchanged. The map has no commitment-host operations:
preparation and acceptance determine it in the native proof, not in this API.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}
variable (compilation : SealedCompilation source ty)

/-- Legal source policies that choose the specified value at each commitment.
The assignment is proof data, not an input to the compiled native adversary. -/
def valueSourceProfile (values : Fin (compile source.core).graph.nodeCount → L.Val ty) :
    SourceBehavioralProfile source.core.prog :=
  fun who => backtranslateCommitPolicy source.core who
    (compilation.supported.assignedCommitPolicy values who)

private theorem valueSourceProfile_pure (value : L.Val ty) (who : Player)
    {Δ name choiceTy guard}
    (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) :
    ∃ choice, compilation.valueSourceProfile (fun _ => value) who site visible =
      FinDist.pure choice := by
  simp only [valueSourceProfile, backtranslateCommitPolicy, backtranslateSourceDecision,
    SealedFragment.assignedCommitPolicy, FinDist.map_pure]
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
    SealedFragment.assignedCommitPolicy, FinDist.map_pure] at hlaw
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

/-- Fix exactly the recorded source choices belonging to selected owners.
Out-of-program slots and unselected owners cannot constrain a source decision.
The map is proof data, not an observation supplied to a player. -/
def recordedChoiceRestriction (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty)) :
    SourceChoiceRestriction source.core.prog :=
  fun who _ _ _ _ site visible =>
    if selected who then
      (recorded (who, site.depth)).map fun value =>
        compilation.sourceChoice value who site visible
    else none

/-- The legal source choice selected by an occupied honest slot retains that
slot's value and type, independently of the source view used to justify it. -/
theorem recordedChoiceRestriction_fixed_value (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty)) (who : Player)
    (hselected : selected who = true)
    {Δ name choiceTy guard}
    (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ)))
    (value : L.Val ty) (hlookup : recorded (who, site.depth) = some value)
    (fixed : {chosen : L.Val choiceTy // evalGuard guard chosen visible = true})
    (hfixed :
      compilation.recordedChoiceRestriction selected recorded who site visible = some fixed) :
    (⟨choiceTy, fixed.1⟩ : TypedValue L) = ⟨ty, value⟩ := by
  simp only [recordedChoiceRestriction, hselected, ↓reduceIte, hlookup, Option.map_some,
    Option.some.injEq] at hfixed
  subst fixed
  exact compilation.sourceChoice_value value who site visible

/-- A source outcome satisfies the recorded-choice restriction exactly
when its recorded honest source choices equal the recorded values. -/
theorem recordedChoiceRestriction_allows_iff_recorded (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (final : VEnv L (sourceTerminalCtx source.core.prog))
    (hfinal : final ∈ (denoteSource source.core.prog profile source.core.env).support) :
    (compilation.recordedChoiceRestriction selected recorded).Allows source.core.env final ↔
      ∀ who {Δ name choiceTy guard}
        (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard),
        selected who = true →
        ∀ value, recorded (who, site.depth) = some value →
          (⟨choiceTy, (site.recorded final).get .here⟩ : TypedValue L) = ⟨ty, value⟩ := by
  rw [SourceChoiceRestriction.allows_iff_recorded source.core.prog profile _ _ _ hfinal]
  constructor
  · intro h who Δ name choiceTy guard site hselected value hlookup
    have hchoice := h who site
      (compilation.sourceChoice value who site ((site.recorded final).tail.toView who).eraseEnv)
      (by simp only [recordedChoiceRestriction, hselected, ↓reduceIte, hlookup, Option.map_some])
    exact (congrArg (fun chosen => (⟨choiceTy, chosen⟩ : TypedValue L)) hchoice).trans
      (compilation.sourceChoice_value value who site _)
  · intro h who Δ name choiceTy guard site fixed hfixed
    cases hselected : selected who with
    | false =>
      simp only [recordedChoiceRestriction, hselected, Bool.false_eq_true, ↓reduceIte] at hfixed
      cases hfixed
    | true =>
      cases hlookup : recorded (who, site.depth) with
      | none =>
          simp only [recordedChoiceRestriction, hselected, ↓reduceIte, hlookup,
            Option.map_none] at hfixed
          cases hfixed
      | some value =>
          simp only [recordedChoiceRestriction, hselected, ↓reduceIte, hlookup, Option.map_some,
            Option.some.injEq] at hfixed
          subst fixed
          have heq := (h who site hselected value hlookup).trans
            (compilation.sourceChoice_value value who site
              ((site.recorded final).tail.toView who).eraseEnv).symm
          exact eq_of_heq (TypedValue.mk.inj heq).2

/-- Applying the reference restriction commutes with replacing the focal
policy. In particular it never alters the extracted source deviator. -/
theorem recordedChoiceRestriction_apply_update (selected : Player → Bool) (focal : Player)
    (hunselected : selected focal = false)
    (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (replacement : SourceBehavioralPolicy source.core.prog focal) :
    (compilation.recordedChoiceRestriction selected recorded).apply
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal replacement) =
      Profile.update (sig := sourceGameSignature source.core.prog)
        ((compilation.recordedChoiceRestriction selected recorded).apply profile) focal
        replacement := by
  funext who Δ name choiceTy guard site visible
  by_cases hwho : who = focal
  · subst who
    simp only [SourceChoiceRestriction.apply, recordedChoiceRestriction, hunselected,
      Bool.false_eq_true, ↓reduceIte, Profile.update_same]
  · simp only [SourceChoiceRestriction.apply, recordedChoiceRestriction,
      Profile.update_of_ne _ _ hwho]

/-- The reference source profile recompiles to the original graph kernel at
unoccupied or focal slots, and to the recorded value at occupied honest slots. -/
theorem compile_recordedChoiceRestriction (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads) :
    compileSourcePolicy source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        rfl who ((compilation.recordedChoiceRestriction selected recorded).apply profile who)
        node guard hsem reads =
      match (if selected who then recorded (who, node.val) else none) with
      | none => compileSourcePolicy source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          rfl who (profile who) node guard hsem reads
      | some value =>
          compilation.supported.assignedCommitPolicy (fun _ => value) who node guard hsem reads :=
            by
  cases hselected : selected who with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply compileSourcePolicy_congr_at_depth
    intro Δ name choiceTy sourceGuard site _
    funext visible
    simp only [SourceChoiceRestriction.apply, recordedChoiceRestriction, hselected,
      Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [↓reduceIte]
    cases hlookup : recorded (who, node.val) with
    | none =>
        apply compileSourcePolicy_congr_at_depth
        intro Δ name choiceTy sourceGuard site hdepth
        funext visible
        simp only [SourceChoiceRestriction.apply, recordedChoiceRestriction, hselected, ↓reduceIte,
          hdepth, hlookup, Option.map_none]
    | some value =>
        have hpolicy := compileSourcePolicy_congr_at_depth source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          rfl who ((compilation.recordedChoiceRestriction selected recorded).apply profile who)
          (compilation.valueSourceProfile (fun _ => value) who) node guard hsem reads
          (by
            intro Δ name choiceTy sourceGuard site hdepth
            funext visible
            simp only [SourceChoiceRestriction.apply, recordedChoiceRestriction, hselected,
              ↓reduceIte,
              hdepth, hlookup, Option.map_some]
            exact compilation.sourceChoice_law value who site visible)
        exact hpolicy.trans (congrFun (congrFun (congrFun (congrFun
          (compile_backtranslateCommitPolicy source.core who
            (compilation.supported.assignedCommitPolicy (fun _ => value) who)) node) guard) hsem)
              reads)

/-- Applying recorded-choice restrictions commutes with source-to-graph
policy compilation. This is an outer compiler certificate; the graph
restriction and its probability law do not invoke source semantics. -/
theorem compile_recordedChoiceRestriction_profile (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) :
    (fun who => compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who ((compilation.recordedChoiceRestriction selected recorded).apply profile who)) =
      (compilation.supported.recordedChoiceRestriction selected recorded).apply
        (fun who => compileSourcePolicy source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          rfl who (profile who)) := by
  funext who node guard hsem reads
  rw [compilation.compile_recordedChoiceRestriction selected recorded profile who node guard
    hsem reads]
  simp only [CommitRestriction.apply, SealedFragment.recordedChoiceRestriction]
  cases selected who <;> simp only [Bool.false_eq_true, ↓reduceIte]
  cases recorded (who, node.val) <;> rfl

/-- Source restriction acceptance is exactly equality at occupied honest
commitment fields of its decoded graph realization. The source support premise
ensures the queried terminal environment follows the source semantics. -/
theorem recordedChoiceRestriction_allows_iff_store (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1) :
    let final := decodeSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal
    final ∈ (denoteSource source.core.prog profile source.core.env).support →
    ((compilation.recordedChoiceRestriction selected recorded).Allows source.core.env final ↔
      ∀ who (node : Fin (compile source.core).graph.nodeCount) guard,
        ((compile source.core).graph.nodeRow node).sem = .commit who guard →
        selected who = true →
        ∀ value, recorded (who, node.val) = some value →
          cfg.1.store ((compile source.core).graph.nodeTarget node) =
            some (⟨ty, value⟩ : TypedValue L)) := by
  intro final hfinal
  rw [compilation.recordedChoiceRestriction_allows_iff_recorded
    selected recorded profile final hfinal]
  let state := BuildState.fromInitial
    (initialState source.core.Γ source.core.env source.core.wctx)
  constructor
  · intro h who node guard hsem hselected value hlookup
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
    have hvalue := h who site hselected value (by rw [hdepth]; exact hlookup)
    have hrecord := decisionSite_recorded_value site source.core.fresh state cfg hterminal
    rw [← decisionSite_nodeTarget site source.core.fresh state node hindex] at hrecord
    exact hrecord.trans (congrArg some hvalue)
  · intro h who Δ name choiceTy guard site hselected value hlookup
    obtain ⟨node, hindex, hrow⟩ := decisionSite_compiledRow site source.core.fresh state
    have hsem := congrArg EventNode.sem (Option.some.inj
      (((compile source.core).graph.nodes_get?_nodeRow node).symm.trans hrow))
    have hdepth : site.depth = node.val := by
      simpa only [decisionSiteState_nodes_length,
        show state.nodes.length = 0 from rfl, Nat.zero_add] using hindex.symm
    have hstored := h who node _ hsem hselected value (by rwa [hdepth] at hlookup)
    have hrecord := decisionSite_recorded_value site source.core.fresh state cfg hterminal
    rw [← decisionSite_nodeTarget site source.core.fresh state node hindex] at hrecord
    exact Option.some.inj (hrecord.symm.trans hstored)

/-- The same restriction expressed in the homogeneous node-value coordinates
used by replay. Store coherence comes from the compiled graph's reachability. -/
theorem recordedChoiceRestriction_allows_iff_nodeValues (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) (fallback : L.Val ty)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1) :
    let final := decodeSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal
    final ∈ (denoteSource source.core.prog profile source.core.env).support →
    ((compilation.recordedChoiceRestriction selected recorded).Allows source.core.env final ↔
      ∀ who (node : Fin (compile source.core).graph.nodeCount) guard,
        ((compile source.core).graph.nodeRow node).sem = .commit who guard →
        selected who = true → ∀ value, recorded (who, node.val) = some value →
          cfg.1.nodeValues fallback node = value) := by
  intro final hfinal
  rw [compilation.recordedChoiceRestriction_allows_iff_store
    selected recorded profile cfg hterminal hfinal]
  constructor
  · intro h who node guard hsem hselected value hlookup
    have hstored := h who node guard hsem hselected value hlookup
    rw [cfg.1.store_nodeValues
      (reachable_storeCoherent compilation.supported.graphWF cfg.2) fallback node
      (compilation.supported.rowType node) (hterminal node)] at hstored
    exact eq_of_heq (TypedValue.mk.inj (Option.some.inj hstored)).2
  · intro h who node guard hsem hselected value hlookup
    rw [cfg.1.store_nodeValues
      (reachable_storeCoherent compilation.supported.graphWF cfg.2) fallback node
      (compilation.supported.rowType node) (hterminal node),
      h who node guard hsem hselected value hlookup]

/-- Transfer an exact recorded-choice event through a proved source law.
The replay carrier may retain a complete native trace; only its event
characterization, not any runtime implementation, enters this source calculation. -/
theorem replay_probability_of_recorded_choices {Trace : Type*}
    (law : FinDist (ReachableConfig (compile source.core).graph))
    (profile : SourceBehavioralProfile source.core.prog)
    (hsource : law.map (observeSourceOutcome source.core) =
      (denoteSource source.core.prog profile source.core.env).map some)
    (hterminal : ∀ cfg ∈ law.support, Terminal (compile source.core).graph cfg.1)
    (selected : Player → Bool) (recorded : Player × Nat → Option (L.Val ty))
    (fallback : L.Val ty) (replay : ReachableConfig (compile source.core).graph → Trace)
    (reference : Trace)
    (hreplay : ∀ cfg ∈ law.support, replay cfg = reference ↔
      ∀ who (node : Fin (compile source.core).graph.nodeCount) guard,
        ((compile source.core).graph.nodeRow node).sem = .commit who guard →
        selected who = true → ∀ value, recorded (who, node.val) = some value →
          cfg.1.nodeValues fallback node = value) :
    (law.map replay).prob reference =
      (denoteSource source.core.prog profile source.core.env).probOf
        {final | (compilation.recordedChoiceRestriction selected recorded).Allows
          source.core.env final} := by
  let event : Set (Option (VEnv L (sourceTerminalCtx source.core.prog))) :=
    {outcome | ∃ final, outcome = some final ∧
      (compilation.recordedChoiceRestriction selected recorded).Allows source.core.env final}
  have hmass := congrArg (fun distribution => distribution.probOf event) hsource
  rw [FinDist.probOf_map, FinDist.probOf_map] at hmass
  rw [FinDist.prob_map_eq_probOf_preimage_singleton]
  refine (FinDist.probOf_congr _ (second := observeSourceOutcome source.core ⁻¹' event)
    ?_).trans (hmass.trans ?_)
  · intro cfg hcfg
    let final := decodeSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg (hterminal cfg hcfg)
    have hobserve : observeSourceOutcome source.core cfg = some final :=
      observeSourceOutcome_of_terminal source.core cfg (hterminal cfg hcfg)
    have hfinal : final ∈ (denoteSource source.core.prog profile source.core.env).support := by
      have hmapped : some final ∈ (law.map (observeSourceOutcome source.core)).support := by
        rw [FinDist.support_map]
        exact ⟨cfg, hcfg, hobserve⟩
      rw [hsource, FinDist.support_map] at hmapped
      obtain ⟨actual, hactual, heq⟩ := hmapped
      exact Option.some.inj heq ▸ hactual
    have hallow := compilation.recordedChoiceRestriction_allows_iff_nodeValues
      selected recorded profile fallback cfg (hterminal cfg hcfg) hfinal
    change (replay cfg = reference) ↔ ∃ outcome,
      observeSourceOutcome source.core cfg = some outcome ∧
        (compilation.recordedChoiceRestriction selected recorded).Allows source.core.env outcome
    rw [hreplay cfg hcfg, ← hallow, hobserve]
    simp only [Option.some.injEq, exists_eq_left', final]
  · congr 1
    ext final
    simp only [event, Set.mem_preimage, Set.mem_ofPred_eq, Option.some.injEq,
      exists_eq_left']

/-- Evaluate a recorded-choice likelihood from one fixed factor per source
decision. The local probability premise uses typed source values, leaving
native checkpoint selection and encoding entirely outside this calculation. -/
theorem recordedChoiceRestriction_weight_eq_product
    (selected : Player → Bool) (recorded : Player × Nat → Option (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) (factor : Player → Nat → ℝ)
    (final : VEnv L (sourceTerminalCtx source.core.prog))
    (hfinal : final ∈ (denoteSource source.core.prog
      ((compilation.recordedChoiceRestriction selected recorded).apply profile)
        source.core.env).support)
    (hunit : ∀ who slot, selected who = false ∨ recorded (who, slot) = none →
      factor who slot = 1)
    (hprob : ∀ who {Δ name choiceTy guard}
      (site : SourceDecisionSite who source.core.prog Δ name choiceTy guard),
      selected who = true → ∀ value, recorded (who, site.depth) = some value →
        factor who site.depth =
          ((profile who site ((site.recorded final).tail.toView who).eraseEnv).map
            (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))).prob ⟨ty, value⟩) :
    (compilation.recordedChoiceRestriction selected recorded).weight profile source.core.env final =
      (source.core.prog.decisionPositions.map fun slot => factor slot.1 slot.2).prod := by
  apply SourceChoiceRestriction.weight_eq_decision_product source.core.prog profile
    ((compilation.recordedChoiceRestriction selected recorded).apply profile) _
    source.core.env final hfinal
  intro who Δ name choiceTy guard site
  dsimp only
  cases hselected : selected who with
  | false =>
      constructor
      · intro _
        exact hunit who site.depth (Or.inl hselected)
      · intro fixed hfixed
        simp only [recordedChoiceRestriction, hselected, Bool.false_eq_true, ↓reduceIte] at hfixed
        cases hfixed
  | true =>
      cases hlookup : recorded (who, site.depth) with
      | none =>
          constructor
          · intro _
            exact hunit who site.depth (Or.inr hlookup)
          · intro fixed hfixed
            simp only [recordedChoiceRestriction, hselected, ↓reduceIte, hlookup,
              Option.map_none] at hfixed
            cases hfixed
      | some value =>
          constructor
          · intro hnone
            simp only [recordedChoiceRestriction, hselected, ↓reduceIte, hlookup,
              Option.map_some] at hnone
            cases hnone
          · intro fixed hfixed
            have hvalue := compilation.recordedChoiceRestriction_fixed_value selected recorded
              who hselected site _ value hlookup fixed hfixed
            have hmass := hprob who site hselected value hlookup
            rw [← hvalue] at hmass
            refine hmass.trans ?_
            rw [FinDist.prob_map_eq_probOf_preimage_singleton,
              FinDist.prob_map_eq_probOf_preimage_singleton]
            apply FinDist.probOf_congr
            intro choice _
            simp only [Set.mem_preimage, Set.mem_singleton_iff, TypedValue.mk.injEq,
              heq_eq_eq, true_and]

/-- An injectively encoded compiled choice has exactly the probability of
its written-source decision at the recorded declared view. This comparison is
independent of the native host and includes queried values of probability zero. -/
theorem sourcePolicy_encoded_probability {Command : Type*}
    (encode : L.Val ty → Command) (hinjective : Function.Injective encode)
    (who : Player) (policy : SourceBehavioralPolicy source.core.prog who)
    (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads) :
    ∃ final, observeSourceOutcome source.core cfg = some final ∧
      ∃ Δ name choiceTy sourceGuard, ∃ site :
        SourceDecisionSite who source.core.prog Δ name choiceTy sourceGuard,
        site.depth = node.val ∧ ∀ chosen,
          ((compileSourcePolicy source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
            rfl who policy node guard hsem reads).map (fun choice => encode
              (cast (congrArg L.Val (compilation.supported.commitType node who guard hsem))
                choice.1))).prob (encode chosen) =
            ((policy site ((site.recorded final).tail.toView who).eraseEnv).map
              (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))).prob ⟨ty, chosen⟩ := by
  obtain ⟨Δ, name, choiceTy, sourceGuard, site, hdepth, hlaw⟩ :=
    compileSourcePolicy_recorded_law source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who policy node guard hsem cfg hterminal reads hreads
  refine ⟨_, observeSourceOutcome_of_terminal source.core cfg hterminal,
    Δ, name, choiceTy, sourceGuard, site, hdepth, ?_⟩
  intro chosen
  rw [← hlaw, FinDist.prob_map_eq_probOf_preimage_singleton,
    FinDist.prob_map_eq_probOf_preimage_singleton]
  apply FinDist.probOf_congr
  intro choice _
  have htyped {left right : L.Ty} (heq : left = right)
      (selected : L.Val left) (queried : L.Val right) :
      (⟨left, selected⟩ : TypedValue L) = ⟨right, queried⟩ ↔
        cast (congrArg L.Val heq) selected = queried := by
    cases heq
    simp only [TypedValue.mk.injEq, heq_eq_eq, true_and, cast_eq]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hinjective.eq_iff,
    htyped (compilation.supported.commitType node who guard hsem)]

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.compile_recordedChoiceRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.compile_recordedChoiceRestriction

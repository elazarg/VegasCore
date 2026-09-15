/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourcePolicy
import Vegas.Core.SourceLikelihood

/-! # Terminal source outcomes of compiled programs -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The compiler's dependent terminal context is the context obtained by
following the source continuations. -/
theorem compileCore_terminalCtx_eq_sourceTerminalCtx :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
      (compileCore prog fresh state).terminalCtx = sourceTerminalCtx prog
  | _, .ret _, _, _ => rfl
  | _, .sample _ _ tail, fresh, state => by
      exact compileCore_terminalCtx_eq_sourceTerminalCtx tail fresh.2 _
  | _, .commit _ _ _ tail, fresh, state => by
      exact compileCore_terminalCtx_eq_sourceTerminalCtx tail fresh.2 _
  | _, .reveal _ _ _ _ tail, fresh, state => by
      exact compileCore_terminalCtx_eq_sourceTerminalCtx tail fresh.2 _

/-- The compiler retains the payoff expressions written at the source
program's terminal return, modulo its dependent terminal-context equality. -/
theorem compileCore_sourcePayoffs_heq :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
      HEq (compileCore prog fresh state).sourcePayoffs
        (sourceTerminalPayoffs prog)
  | _, .ret _, _, _ => HEq.rfl
  | _, .sample name dist tail, fresh, state =>
      compileCore_sourcePayoffs_heq tail fresh.2
        (state.addSampleEvent name dist fresh.1).1
  | _, .commit name who guard tail, fresh, state =>
      compileCore_sourcePayoffs_heq tail fresh.2
        (state.addCommitEvent name who guard fresh.1).1
  | _, .reveal name who _ source tail, fresh, state =>
      compileCore_sourcePayoffs_heq tail fresh.2
        (state.addRevealEvent name who source fresh.1).1

/-- Every binding in the compiler's terminal field map can be read from a
reachable terminal configuration. -/
theorem BuildResult.terminalBindingAvailable (result : BuildResult P L)
    (cfg : ReachableConfig result.graph) (hterminal : Terminal result.graph cfg.1) :
    ∀ {name bindTy} (h : VHasVar result.terminalCtx name bindTy),
      ∃ value, Store.getAs cfg.1.store
        (result.terminalState.fieldOf h) bindTy.base = some value := by
  intro name bindTy h
  rcases result.terminalState.fieldOf_spec h with ⟨spec, hget, hty, _⟩
  have hget' : result.graph.field? (result.terminalState.fieldOf h) = some spec := by
    rw [← result.terminal_graph_eq]
    exact hget
  have havailable : result.graph.fieldAvailableBefore result.graph.nodeCount
      (result.terminalState.fieldOf h) = true := by
    rw [← result.terminal_graph_eq]
    exact result.terminalState.fieldOf_available h
  rcases (reachable_storeCoherent result.graphWF cfg.2).hasFieldOfAvailable
      hterminal hget' havailable with ⟨value, hvalue⟩
  exact ⟨cast (congrArg L.Val hty) value,
    Store.getAs_cast cfg.1.store (result.terminalState.fieldOf h) hty hvalue⟩

/-- Decode the complete terminal source environment, including sealed fields,
from an actual terminal graph store. -/
def BuildResult.decodeTerminalSource (result : BuildResult P L)
    (cfg : ReachableConfig result.graph) (hterminal : Terminal result.graph cfg.1) :
    VEnv L result.terminalCtx :=
  sourceEnvOfStore result.terminalState cfg.1.store
    (result.terminalBindingAvailable cfg hterminal)

/-- Terminal decoding is inverse to compiler-store agreement. -/
theorem BuildResult.decodeTerminalSource_eq (result : BuildResult P L)
    (cfg : ReachableConfig result.graph) (hterminal : Terminal result.graph cfg.1)
    (env : VEnv L result.terminalCtx)
    (hagrees : result.terminalState.Agrees cfg.1.store env) :
    result.decodeTerminalSource cfg hterminal = env := by
  exact sourceEnvOfStore_eq_of_get result.terminalState cfg.1.store
    (result.terminalBindingAvailable cfg hterminal) env hagrees

/-- Decode a compiled terminal configuration directly into the source
semantics' independently defined outcome carrier. -/
def decodeSourceOutcome {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (cfg : ReachableConfig (compileCore prog fresh state).graph)
    (hterminal : Terminal (compileCore prog fresh state).graph cfg.1) :
    VEnv L (sourceTerminalCtx prog) := by
  rw [← compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state]
  exact (compileCore prog fresh state).decodeTerminalSource cfg hterminal

/-- A terminal compiled store evaluates the payout expressions written at the
source program's terminal return on its decoded source outcome. -/
theorem evalPayoffs?_eq_decodedSourceOutcome {Γ : VCtx P L}
    (prog : VegasCore P L Γ) (fresh : FreshBindings prog)
    (state : BuildState P L Γ)
    (cfg : ReachableConfig (compileCore prog fresh state).graph)
    (hterminal : Terminal (compileCore prog fresh state).graph cfg.1) :
    evalPayoffs? (compileCore prog fresh state).payoffs cfg.1.store =
      some (evalPayoffs (sourceTerminalPayoffs prog)
        (decodeSourceOutcome prog fresh state cfg hterminal)) := by
  induction prog with
  | ret payoffs =>
      exact CompiledProgram.evalPayoffs_eq_sourceEnvOfStore
        (compileCore (.ret payoffs) fresh state) cfg.1.store
        ((compileCore (.ret payoffs) fresh state).terminalBindingAvailable cfg hterminal)
  | sample name dist tail ih =>
      exact ih fresh.2 (state.addSampleEvent name dist fresh.1).1 cfg hterminal
  | commit name who guard tail ih =>
      exact ih fresh.2 (state.addCommitEvent name who guard fresh.1).1 cfg hterminal
  | reveal name who sourceName source tail ih =>
      exact ih fresh.2 (state.addRevealEvent name who source fresh.1).1 cfg hterminal

/-- Projecting a decoded terminal outcome to an earlier source context retains
exact agreement with that context's compiler field map. -/
theorem decodeSourceOutcome_initial_agrees :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
    (cfg : ReachableConfig (compileCore prog fresh state).graph) →
    (hterminal : Terminal (compileCore prog fresh state).graph cfg.1) →
    ∀ {name bindTy} (binding : VHasVar Γ name bindTy),
      Store.getAs cfg.1.store (state.fieldOf binding) bindTy.base =
        some ((sourceInitialProjection prog
          (decodeSourceOutcome prog fresh state cfg hterminal)).get binding)
  | _, .ret payoffs, fresh, state, cfg, hterminal => by
      intro binding
      exact sourceEnvOfStore_get state cfg.1.store
        ((compileCore (.ret payoffs) fresh state).terminalBindingAvailable cfg hterminal) binding
  | _, .sample name dist tail, fresh, state, cfg, hterminal => by
      intro binding
      exact decodeSourceOutcome_initial_agrees tail fresh.2
        (state.addSampleEvent name dist fresh.1).1 cfg hterminal (.there binding)
  | _, .commit name who guard tail, fresh, state, cfg, hterminal => by
      intro binding
      exact decodeSourceOutcome_initial_agrees tail fresh.2
        (state.addCommitEvent name who guard fresh.1).1 cfg hterminal (.there binding)
  | _, .reveal name who _ source tail, fresh, state, cfg, hterminal => by
      intro binding
      exact decodeSourceOutcome_initial_agrees tail fresh.2
        (state.addRevealEvent name who source fresh.1).1 cfg hterminal (.there binding)

/-- Every recorded decision binding, including its complete input context,
agrees with the corresponding compiler fields in the decoded terminal store. -/
theorem decisionSite_recorded_agrees {who : P} {Γ Δ : VCtx P L}
    {prog : VegasCore P L Γ} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (cfg : ReachableConfig (compileCore prog fresh state).graph)
    (hterminal : Terminal (compileCore prog fresh state).graph cfg.1) :
    ∀ {query bindTy} (binding : VHasVar ((name, .sealed who ty) :: Δ) query bindTy),
      Store.getAs cfg.1.store
        (((decisionSiteState site fresh state).addCommitEvent name who guard
          (site.decision_fresh fresh).1).1.fieldOf binding) bindTy.base =
        some ((site.recorded
          (decodeSourceOutcome prog fresh state cfg hterminal)).get binding) := by
  induction site with
  | here sourceGuard tail =>
      exact decodeSourceOutcome_initial_agrees tail fresh.2 _ cfg hterminal
  | sample site ih => exact ih fresh.2 _ cfg hterminal
  | commit site ih => exact ih fresh.2 _ cfg hterminal
  | reveal site ih => exact ih fresh.2 _ cfg hterminal

/-- Equality of the exact compiler fields for public bindings before a source
decision implies equality of the public source environments recorded before
that decision.  No agreement on the decision owner's private bindings is
required. -/
theorem _root_.Vegas.SourceDecisionSite.recorded_tail_erasePubEnv_eq_of_getAs_eq
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (left right : ReachableConfig (compileCore prog fresh state).graph)
    (hleft : Terminal (compileCore prog fresh state).graph left.1)
    (hright : Terminal (compileCore prog fresh state).graph right.1)
    (hpublic : ∀ {query queryTy}
      (binding : HasVar (erasePubVCtx Δ) query queryTy),
      Store.getAs left.1.store
          ((decisionSiteState site fresh state).fieldOf
            (VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding))) queryTy =
        Store.getAs right.1.store
          ((decisionSiteState site fresh state).fieldOf
            (VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding))) queryTy) :
    (site.recorded (decodeSourceOutcome prog fresh state left hleft)).tail.erasePubEnv =
      (site.recorded (decodeSourceOutcome prog fresh state right hright)).tail.erasePubEnv := by
  funext query queryTy binding
  rw [VEnv.erasePubEnv_get, VEnv.erasePubEnv_get]
  let publicBinding : VHasVar Δ query (.pub queryTy) :=
    VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding)
  have hleftValue :=
    decisionSite_recorded_agrees site fresh state left hleft (.there publicBinding)
  have hrightValue :=
    decisionSite_recorded_agrees site fresh state right hright (.there publicBinding)
  rw [BuildState.addCommitEvent_fieldOf_there] at hleftValue hrightValue
  exact Option.some.inj (hleftValue.symm.trans ((hpublic binding).trans hrightValue))

/-- A recorded source choice is the value stored at its compiler-allocated
field, including its type tag. -/
theorem decisionSite_recorded_value {who : P} {Γ Δ : VCtx P L}
    {prog : VegasCore P L Γ} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (cfg : ReachableConfig (compileCore prog fresh state).graph)
    (hterminal : Terminal (compileCore prog fresh state).graph cfg.1) :
    cfg.1.store (decisionSiteState site fresh state).nextField =
      some (⟨ty, (site.recorded
        (decodeSourceOutcome prog fresh state cfg hterminal)).get .here⟩ : TypedValue L) := by
  have hread := decisionSite_recorded_agrees site fresh state cfg hterminal .here
  rw [BuildState.addCommitEvent_fieldOf_here] at hread
  cases hstored : cfg.1.store (decisionSiteState site fresh state).nextField with
  | none =>
      simp only [Store.getAs, hstored] at hread
      cases hread
  | some stored =>
      simp only [Store.getAs, hstored] at hread
      exact congrArg some (stored.eq_mk_of_as?_eq_some _ _ hread)

/-- At a terminal realization, each compiled commitment kernel is its source
kernel evaluated at the recorded source view. The compared policy need not
give this realization positive probability. Type tags retain the statement
across the compiler's dependent source and graph value carriers. -/
theorem compileSourcePolicy_recorded_law {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) (hempty : state.nodes = [])
    (who : P) (policy : SourceBehavioralPolicy prog who)
    (node : Fin (compileCore prog fresh state).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compileCore prog fresh state).graph.nodeRow node).sem = .commit who guard)
    (cfg : ReachableConfig (compileCore prog fresh state).graph)
    (hterminal : Terminal (compileCore prog fresh state).graph cfg.1)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads) :
    ∃ Δ name choiceTy sourceGuard, ∃ site : SourceDecisionSite who prog Δ name choiceTy sourceGuard,
      site.depth = node.val ∧
      ((compileSourcePolicy prog fresh state hempty who policy node guard hsem reads).map
          (fun choice => (⟨guard.ty, choice.1⟩ : TypedValue L))) =
        (policy site ((site.recorded (decodeSourceOutcome prog fresh state cfg hterminal)).tail
          |>.toView who |>.eraseEnv)).map
            (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L)) := by
  obtain ⟨actor, Δ, name, choiceTy, sourceGuard, site, hindex, hrow⟩ :=
    compileCore_commitNode_covered prog fresh state node (by simp [hempty])
      ⟨_, who, guard, (compileCore prog fresh state).graph.nodes_get?_nodeRow node, hsem⟩
  have hrowEq := Option.some.inj
    (((compileCore prog fresh state).graph.nodes_get?_nodeRow node).symm.trans hrow)
  have hcommit := NodeSem.commit.inj (hsem.symm.trans (congrArg EventNode.sem hrowEq))
  obtain ⟨rfl, rfl⟩ := hcommit
  refine ⟨Δ, name, choiceTy, sourceGuard, site, ?_, ?_⟩
  · simpa only [decisionSiteState_nodes_length, hempty, List.length_nil, Nat.zero_add]
      using hindex.symm
  · rw [compileSourcePolicy_at prog fresh state hempty who policy sourceGuard site node
      hindex hrow]
    have hagrees : (decisionSiteState site fresh state).Agrees cfg.1.store
        (site.recorded (decodeSourceOutcome prog fresh state cfg hterminal)).tail := by
      intro query bindTy binding
      exact decisionSite_recorded_agrees site fresh state cfg hterminal (.there binding)
    have hlaw := congrArg (GameTheory.Math.Probability.FinDist.map
      (fun value => (⟨choiceTy, value⟩ : TypedValue L)))
      (compileSourceDecision_law (decisionSiteState site fresh state) who sourceGuard
        (policy site) cfg.1.store _ (hagrees.view who) reads hreads)
    simpa only [GameTheory.Math.Probability.FinDist.map_comp, Function.comp_def] using! hlaw

end Vegas.ToEventGraph

/-- info: 'Vegas.SourceDecisionSite.recorded_tail_erasePubEnv_eq_of_getAs_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.recorded_tail_erasePubEnv_eq_of_getAs_eq

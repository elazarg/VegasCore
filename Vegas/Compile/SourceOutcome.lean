/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceLaw
import Vegas.Compile.DecisionSite
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

end Vegas.ToEventGraph

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedGraphRestriction
import Vegas.Core.ExprSimple
import Mathlib.Tactic.IntervalCases

/-! # Graph likelihood regression without a source-program fixture

Forcing a legal value outside the original policy's support still yields a
normalized reference run, while the original event has probability zero.
-/

noncomputable section

namespace VegasTests.GraphRestriction

open Vegas Vegas.EventGraph GameTheory.Math.Probability

private def guard : EventGuard simpleExpr where
  ty := .bool
  code := {
    actionName := 0
    Context := []
    expr := Expr.constBool true
    fieldOf := by intro name ty binding; cases binding }
  choiceReads := ∅
  read_mem := by intro name ty binding; cases binding

private def graph : Graph Unit simpleExpr where
  initialFields := []
  nodes := [⟨.bool, some (), .commit () guard⟩]

private theorem graphWF : graph.WF := by
  intro index event hrow
  have hlt := (List.getElem?_eq_some_iff.mp hrow).1
  change index < 1 at hlt
  interval_cases index
  simp only [graph, List.getElem?_cons_zero, Option.some.injEq] at hrow
  subst event
  simp [graph, Graph.nodeWFAt, NodeSem.reads, guard, FieldRef.fields]

private theorem supported : SealedFragment graph .bool where
  graphWF := graphWF
  rowType node := by fin_cases node; rfl
  noSamples node dist := by fin_cases node; intro h; cases h
  commitType node who test hsem := by fin_cases node; cases hsem; rfl
  commitGuard node who test hsem value reads := by fin_cases node; cases hsem; rfl
  revealSource node source hsem := by fin_cases node; cases hsem

private theorem guards : GuardLive graph := by
  intro node row who test hrow hsem reads
  fin_cases node
  change some (⟨.bool, some (), .commit () guard⟩ : EventNode Unit simpleExpr) = some row at hrow
  have hrow := Option.some.inj hrow
  subst row
  cases hsem
  exact ⟨false, rfl⟩

private def profile (law : FinDist Bool) : CommitPolicyProfile graph := by
  intro who node test hsem reads
  have hnode : node = ⟨0, by decide⟩ := by
    apply Fin.ext
    have hlt := node.isLt
    change node.val < 1 at hlt
    change node.val = 0
    omega
  subst node
  cases hsem
  exact law.map fun value => ⟨value, rfl⟩

private def restriction (value : Bool) : CommitRestriction graph :=
  supported.recordedChoiceRestriction (fun _ => true) (fun _ => some value)

private def initial : ReachableConfig graph := ⟨Config.initial graph, .initial⟩

theorem choice_event_probability (law : FinDist Bool) (value : Bool) :
    (runPolicyNodes graphWF guards (profile law) initial graph.nodeOrder).probOf
      {cfg | (restriction value).Allows graph.nodeOrder cfg.1} = law.prob value := by
  classical
  apply runPolicyNodes_restriction_probability_of_constant _ _ _ _ _ _ graph.nodeOrder_readyOrder
  intro cfg hcfg
  have hterminal := runPolicyNodes_terminal graphWF guards ((restriction value).apply (profile law))
    initial graph.nodeOrder graph.nodeOrder_readyOrder (fun node => Or.inr (by simp)) cfg hcfg
  have hchoices := runPolicyNodes_support_commitValues graphWF guards
    ((restriction value).apply (profile law)) initial (CommitValuesSupported.initial _)
    graph.nodeOrder cfg hcfg
  obtain ⟨reads, hreads, _, _, _⟩ := hchoices ⟨0, by decide⟩ (hterminal _) () guard rfl
  change (restriction value).factor (profile law) cfg.1 ⟨0, by decide⟩ * 1 = law.prob value
  rw [mul_one, CommitRestriction.factor_commit _ _ _ _ () guard rfl reads hreads]
  simp only [restriction, SealedFragment.recordedChoiceRestriction, ↓reduceIte, Option.map_some]
  change (law.map fun v => (⟨v, rfl⟩ : {v : Bool // guard.eval v reads = true})).prob
    ⟨value, rfl⟩ = law.prob value
  exact FinDist.prob_map_of_injective _ (fun _ _ heq => congrArg Subtype.val heq) law value

theorem zero_probability_event :
    (runPolicyNodes graphWF guards (profile (FinDist.pure false)) initial graph.nodeOrder).probOf
      {cfg | (restriction true).Allows graph.nodeOrder cfg.1} = 0 := by
  rw [choice_event_probability]
  exact FinDist.prob_eq_zero_iff.mpr (by rw [FinDist.mem_support_pure]; decide)

theorem zero_probability_reference_exists :
    ∃ cfg ∈ (runPolicyNodes graphWF guards ((restriction true).apply (profile (FinDist.pure false)))
      initial graph.nodeOrder).support,
        (restriction true).Allows graph.nodeOrder cfg.1 := by
  obtain ⟨cfg, hcfg⟩ := (runPolicyNodes graphWF guards
    ((restriction true).apply (profile (FinDist.pure false))) initial
      graph.nodeOrder).support_nonempty
  exact ⟨cfg, hcfg, runPolicyNodes_restriction_support graphWF guards _ _ initial
    (CommitValuesSupported.initial _) graph.nodeOrder graph.nodeOrder_readyOrder cfg hcfg⟩

end VegasTests.GraphRestriction

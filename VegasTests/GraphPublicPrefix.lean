/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.PublicPrefix
import Vegas.Core.ExprSimple
import Mathlib.Tactic.IntervalCases

/-! # Public-prefix readability is a separate information condition

A well-formed commit/reveal graph may omit an earlier public output from a
later decision's declared reads. The backend's information premise therefore
cannot be inferred from ordinary graph well-formedness.
-/

namespace VegasTests.GraphPublicPrefix

open Vegas Vegas.EventGraph

private def guard : EventGuard simpleExpr where
  ty := .bool
  code := {
    actionName := 0
    Context := []
    expr := Expr.constBool true
    fieldOf := by intro name ty binding; cases binding }
  choiceReads := ∅
  read_mem := by intro name ty binding; cases binding

private def graph : Graph Bool simpleExpr where
  initialFields := []
  nodes := [⟨.bool, some false, .commit false guard⟩,
    ⟨.bool, none, .reveal 0⟩, ⟨.bool, some true, .commit true guard⟩]

theorem well_formed : graph.WF := by
  intro index event hrow
  have hlt := (List.getElem?_eq_some_iff.mp hrow).1
  change index < 3 at hlt
  interval_cases index <;>
    simp only [graph, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hrow <;>
    subst event <;>
    simp [graph, Graph.nodeWFAt, NodeSem.reads, guard, FieldRef.fields,
      Graph.fieldAvailableBefore, Graph.field?]

theorem public_prefix_not_readable : ¬graph.PublicPrefixReadable := by
  intro h
  have hread := h true ⟨2, by decide⟩ ⟨1, by decide⟩ guard rfl (by decide) rfl
  exact Finset.notMem_empty _ hread

end VegasTests.GraphPublicPrefix

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceOutcome

/-! # Source choices recorded by compiled commitment fields -/

noncomputable section

namespace Vegas.WFProgram

open ToEventGraph EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A value in a compiled commitment field is the choice at an actual source
decision owned by the same player. The decoded outcome uses the independently
defined written-source terminal context. -/
theorem source_chooses_of_commit_store (source : WFProgram P L)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1)
    (node : Fin (compile source.core).graph.nodeCount) (who : P) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
    {ty : L.Ty} (value : L.Val ty)
    (hvalue : cfg.1.store ((compile source.core).graph.nodeTarget node) =
      some (⟨ty, value⟩ : TypedValue L)) :
    source.core.prog.Chooses who value
      (decodeSourceOutcome source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        cfg hterminal) := by
  let state := BuildState.fromInitial
    (initialState source.core.Γ source.core.env source.core.wctx)
  obtain ⟨actor, Δ, name, choiceTy, sourceGuard, site, hindex, hrow⟩ :=
    compileCore_commitNode_covered source.core.prog source.core.fresh state node (by simp [state])
      ⟨_, who, guard, (compile source.core).graph.nodes_get?_nodeRow node, hsem⟩
  have hrowEq := Option.some.inj
    (((compile source.core).graph.nodes_get?_nodeRow node).symm.trans hrow)
  have hactor := (NodeSem.commit.inj (hsem.symm.trans (congrArg EventNode.sem hrowEq))).1
  subst actor
  have hrecord := decisionSite_recorded_value site source.core.fresh state cfg hterminal
  rw [← decisionSite_nodeTarget site source.core.fresh state node hindex] at hrecord
  have htyped := Option.some.inj (hrecord.symm.trans hvalue)
  have htype : choiceTy = ty := congrArg TypedValue.ty htyped
  subst ty
  refine ⟨Δ, name, sourceGuard, site, ?_⟩
  exact eq_of_heq (TypedValue.mk.inj htyped).2

end Vegas.WFProgram

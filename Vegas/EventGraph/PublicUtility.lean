/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Execution

/-! # Utilities of public graph outcomes

A utility evaluates a store and depends only on the graph's declared public
fields. It need not be a payout or a valuation in any particular currency.
The quitting condition below is a uniform sufficient incentive condition over
legal terminal graph realizations, stronger than ex-ante dominance of quitting.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- An interpretation of public graph outcomes as player utilities. -/
structure Graph.PublicUtility (G : Graph Player L) where
  eval : Store L → Player → ℝ
  congr : ∀ left right,
    (∀ ref, G.fieldRefPublic ref →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) →
    ∀ who, eval left who = eval right who

namespace Graph.PublicUtility

variable {G : Graph Player L}

/-- Every legal terminal realization has utility at least the bound; a
realization recording the player's designated default has utility at most the
same bound. The condition quantifies over executions, not just equilibrium
support, and does not depend on a message runtime or an opponent profile. -/
structure QuitBound (utility : G.PublicUtility) {ty : L.Ty}
    (nullValue : L.Val ty) (bound : Player → ℝ) : Prop where
  lower : ∀ cfg : ReachableConfig G, Terminal G cfg.1 →
    ∀ who, bound who ≤ utility.eval cfg.1.store who
  quitting : ∀ cfg : ReachableConfig G, Terminal G cfg.1 →
    ∀ (who : Player) (producer : Fin G.nodeCount) (guard : EventGuard L),
      (G.nodeRow producer).sem = .commit who guard →
      cfg.1.store (G.nodeTarget producer) = some (⟨ty, nullValue⟩ : TypedValue L) →
      utility.eval cfg.1.store who ≤ bound who

end Graph.PublicUtility

end Vegas.EventGraph

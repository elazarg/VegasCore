/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedGraphSettlement
import Vegas.EventGraph.PublicUtility

/-! # Graph utility bounds for attributed public settlement

Public settlement supplies a legal graph witness recording the timed-out
owner's default. A graph-only quitting cap bounds its utility. A deviation proof
can compare this cap to a floor on its graph marginal, which retains the
opponents' policies; the settlement witness itself need not retain them.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

/-- Attributed failure satisfies the graph's source-independent quitting cap.
The comparison realization and its lower bound belong to the deviation proof,
which may restrict that floor to the fixed opponents' supported outcomes. -/
theorem timeout_utility_le_cap
    (supported : SealedFragment G ty) (hguards : GuardLive G) (hunique : G.UniqueReveals)
    (nullValue : L.Val ty) (window : Nat) (utility : G.PublicUtility)
    (bound : Player → ℝ) (hcap : utility.QuitCap nullValue bound)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hsettlement : SealedResolution.SettlementInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete state = true)
    (node : Fin G.nodeCount) (who : Player) (htimeout : node.val ∈ state.timeouts)
    (howned : (∃ guard, (G.nodeRow node).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
          (G.nodeRow producer).sem = .commit who guard) :
    utility.eval (G.publicSealedStore ty state.events) who ≤ bound who := by
  obtain ⟨settled, hsettled, hagrees, producer, guard, hcommit, hvalue⟩ :=
    supported.public_store_graph_choice_of_timeout hguards hunique nullValue window state
      hinvariant hsettlement hcomplete node who htimeout howned
  rw [utility.congr _ _ hagrees]
  exact hcap settled hsettled who producer guard hcommit hvalue

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.timeout_utility_le_cap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.timeout_utility_le_cap

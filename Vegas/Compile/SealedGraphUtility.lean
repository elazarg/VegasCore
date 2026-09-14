/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedGraphSettlement
import Vegas.EventGraph.PublicUtility

/-! # Graph utility bounds for attributed public settlement

Public settlement supplies a legal graph witness recording the timed-out
owner's default. A graph-only quitting condition compares that witness to any
other legal terminal graph realization. The latter may be the graph marginal
of a deviation coupling, retaining the opponents' policies; the settlement
witness itself does not promise to retain those policies.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

/-- Attributed failure cannot exceed a terminal graph utility under the uniform
graph quitting bound. Service and coupling proofs supply attribution and the
comparison realization separately; no source syntax occurs in this theorem. -/
theorem timeout_utility_le_graph
    (supported : SealedFragment G ty) (hguards : GuardLive G) (hunique : G.UniqueReveals)
    (nullValue : L.Val ty) (window : Nat) (utility : G.PublicUtility)
    (bound : Player → ℝ) (hbound : utility.QuitBound nullValue bound)
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
        (G.nodeRow producer).sem = .commit who guard)
    (cfg : ReachableConfig G) (hterminal : Terminal G cfg.1) :
    utility.eval (G.publicSealedStore ty state.events) who ≤ utility.eval cfg.1.store who := by
  obtain ⟨settled, hsettled, hagrees, producer, guard, hcommit, hvalue⟩ :=
    supported.public_store_graph_choice_of_timeout hguards hunique nullValue window state
      hinvariant hsettlement hcomplete node who htimeout howned
  rw [utility.congr _ _ hagrees]
  exact (hbound.quitting settled hsettled who producer guard hcommit hvalue).trans
    (hbound.lower cfg hterminal who)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.timeout_utility_le_graph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.timeout_utility_le_graph

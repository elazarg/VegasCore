import Vegas.EventGraph.Round
import Vegas.Machine.RoundView

/-!
# Native round views for event graphs

This module packages event-graph frontiers as native machine
`RoundView`s. The FOSG bridge reuses the same frontier-round definitions but
is not needed here.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Native round-view presentation of a protocol-graph machine by local explicit
frontier rounds. -/
noncomputable def toRoundView
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds) :
    (G.toMachine iface).RoundView where
  Act := PlayerRoundAction G
  active := roundActive G
  availableActions := roundAvailable G
  transition := fun cfg action => frontierRealizationTransition G cfg action
  eventBatch := fun cfg joint dst => realizedEventBatch G iface cfg joint dst
  terminal_active_eq_empty := by
    intro cfg hterminal
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who hmem
    rcases (mem_roundActive_iff G cfg who).mp hmem with
      ⟨node, hfrontier, _hactor⟩
    exact (cfg.not_terminal_of_mem_frontier hfrontier) hterminal
  nonterminal_exists_legal := by
    intro cfg hterminal
    classical
    let mkPatch (who : Player) (node : G.Node) : G.FieldPatch :=
      if h : node ∈ cfg.frontier ∧ (G.sem node).actor = some who then
        Classical.choose (hsound.availablePlayerActions cfg h.1 h.2)
      else
        fun _ => none
    let joint : JointAction (PlayerRoundAction G) := fun who =>
      if who ∈ roundActive G cfg then
        some { patch := mkPatch who }
      else
        none
    refine ⟨joint, hterminal, ?_⟩
    intro who
    by_cases hactive : who ∈ roundActive G cfg
    · have hjoint : joint who = some { patch := mkPatch who } := by
        simp [joint, hactive]
      rw [hjoint]
      refine ⟨hactive, ?_⟩
      intro node hfrontier hactor
      have hnode : node ∈ cfg.frontier ∧ (G.sem node).actor = some who :=
        ⟨hfrontier, hactor⟩
      change
        G.patchLegal node (mkPatch who node) ∧
          G.actionLegal cfg.result node (mkPatch who node)
      unfold mkPatch
      split
      · rename_i h
        exact Classical.choose_spec
          (hsound.availablePlayerActions cfg h.1 h.2)
      · rename_i h
        exact False.elim (h hnode)
    · have hjoint : joint who = none := by
        simp [joint, hactive]
      rw [hjoint]
      exact hactive

end EventGraph

end Vegas

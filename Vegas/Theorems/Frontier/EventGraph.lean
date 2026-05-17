import Vegas.EventGraph.Basic

/-!
# Event-Graph Frontier Execution

Facts about executing enabled frontier nodes that hold for every `EventGraph`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Executing one frontier node preserves every other current frontier node. -/
theorem eventGraph_frontier_preserved_after_other
    {G : EventGraph P L} (cfg : G.Configuration)
    {first second : G.Node} {patch : G.FieldPatch}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hlegal : G.patchLegal first patch) :
    second ∈ (cfg.withPatch patch hfirst hlegal).frontier :=
  cfg.withPatch_mem_frontier_of_ne hfirst hsecond hne hlegal

/-- Two distinct frontier executions commute extensionally. -/
theorem eventGraph_frontier_diamond
    {G : EventGraph P L} (cfg : G.Configuration)
    {left right : G.Node} {leftPatch rightPatch : G.FieldPatch}
    (hleft : left ∈ cfg.frontier)
    (hright : right ∈ cfg.frontier)
    (hne : left ≠ right)
    (hleftLegal : G.patchLegal left leftPatch)
    (hrightLegal : G.patchLegal right rightPatch) :
    let hrightAfterLeft :=
      cfg.withPatch_mem_frontier_of_ne
        hleft hright (Ne.symm hne) hleftLegal
    let hleftAfterRight :=
      cfg.withPatch_mem_frontier_of_ne
        hright hleft hne hrightLegal
    (cfg.withPatch leftPatch hleft hleftLegal).withPatch
        rightPatch hrightAfterLeft hrightLegal =
      (cfg.withPatch rightPatch hright hrightLegal).withPatch
        leftPatch hleftAfterRight hleftLegal :=
  cfg.withPatch_comm hleft hright hne hleftLegal hrightLegal

/-- A whole-frontier endpoint is extensionally determined by the current
frontier, the patch chosen for each frontier node, and unchanged non-frontier
results. -/
theorem eventGraph_frontier_extension_extensional
    {G : EventGraph P L}
    (cfg dst : G.Configuration)
    (patch : ∀ node, node ∈ cfg.frontier → G.FieldPatch)
    (hlegal : ∀ node hfrontier, G.patchLegal node (patch node hfrontier))
    (honFrontier :
      ∀ node (hfrontier : node ∈ cfg.frontier),
        dst.result node = some (patch node hfrontier))
    (hoffFrontier :
      ∀ node, node ∉ cfg.frontier → dst.result node = cfg.result node) :
    dst = cfg.withFrontierPatches patch hlegal :=
  EventGraph.Configuration.eq_withFrontierPatches_of_result_eq
    cfg dst patch hlegal honFrontier hoffFrontier

end Vegas

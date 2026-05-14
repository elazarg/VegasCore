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
    {first second : G.Node} {slice : G.WriteSlice}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hlegal : G.sliceLegal first slice) :
    second ∈ (cfg.withResult slice hfirst hlegal).frontier :=
  cfg.withResult_mem_frontier_of_ne hfirst hsecond hne hlegal

/-- Two distinct frontier executions commute extensionally. -/
theorem eventGraph_frontier_diamond
    {G : EventGraph P L} (cfg : G.Configuration)
    {left right : G.Node} {leftSlice rightSlice : G.WriteSlice}
    (hleft : left ∈ cfg.frontier)
    (hright : right ∈ cfg.frontier)
    (hne : left ≠ right)
    (hleftLegal : G.sliceLegal left leftSlice)
    (hrightLegal : G.sliceLegal right rightSlice) :
    let hrightAfterLeft :=
      cfg.withResult_mem_frontier_of_ne
        hleft hright (Ne.symm hne) hleftLegal
    let hleftAfterRight :=
      cfg.withResult_mem_frontier_of_ne
        hright hleft hne hrightLegal
    (cfg.withResult leftSlice hleft hleftLegal).withResult
        rightSlice hrightAfterLeft hrightLegal =
      (cfg.withResult rightSlice hright hrightLegal).withResult
        leftSlice hleftAfterRight hleftLegal :=
  cfg.withResult_comm hleft hright hne hleftLegal hrightLegal

/-- A whole-frontier endpoint is extensionally determined by the current
frontier, the slice chosen for each frontier node, and unchanged non-frontier
results. -/
theorem eventGraph_frontier_extension_extensional
    {G : EventGraph P L}
    (cfg dst : G.Configuration)
    (slice : ∀ node, node ∈ cfg.frontier → G.WriteSlice)
    (hlegal : ∀ node hfrontier, G.sliceLegal node (slice node hfrontier))
    (honFrontier :
      ∀ node (hfrontier : node ∈ cfg.frontier),
        dst.result node = some (slice node hfrontier))
    (hoffFrontier :
      ∀ node, node ∉ cfg.frontier → dst.result node = cfg.result node) :
    dst = cfg.withFrontierResults slice hlegal :=
  EventGraph.Configuration.eq_withFrontierResults_of_result_eq
    cfg dst slice hlegal honFrontier hoffFrontier

end Vegas

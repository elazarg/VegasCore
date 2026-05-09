import Vegas.GameBridge.FOSG.FrontierStability

/-!
# Frontier Theorems

Project-facing names for the scheduler/linearization facts attached to
frontier execution.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Two distinct frontier executions commute extensionally. -/
theorem frontier_execution_commutes
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration)
    {left right : ProgramNode g.prog}
    {leftSlice rightSlice : ProgramField.WriteSlice g.prog}
    (hleft : left ∈ cfg.frontier)
    (hright : right ∈ cfg.frontier)
    (hne : left ≠ right)
    (hleftLegal : (programEventGraph g).sliceLegal left leftSlice)
    (hrightLegal : (programEventGraph g).sliceLegal right rightSlice) :
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

/-- A complete frontier round is extensionally determined by the source
frontier and the result slice chosen for each source-frontier node.  Any
linearization that records exactly those slices and leaves non-frontier nodes
unchanged reaches the canonical whole-frontier endpoint. -/
theorem frontier_round_linearization_invariant
    (g : WFProgram P L)
    (cfg dst : (programEventGraph g).Configuration)
    (slice :
      ∀ node, node ∈ cfg.frontier →
        ProgramField.WriteSlice g.prog)
    (hlegal :
      ∀ node hfrontier,
        (programEventGraph g).sliceLegal node (slice node hfrontier))
    (honFrontier :
      ∀ node (hfrontier : node ∈ cfg.frontier),
        dst.result node = some (slice node hfrontier))
    (hoffFrontier :
      ∀ node, node ∉ cfg.frontier → dst.result node = cfg.result node) :
    dst = cfg.withFrontierResults slice hlegal :=
  EventGraph.Configuration.eq_withFrontierResults_of_result_eq
    cfg dst slice hlegal honFrontier hoffFrontier

/-- Two complete linearizations of the same source frontier and same per-node
result slices end in the same extensional configuration. -/
theorem frontier_round_linearizations_agree
    (g : WFProgram P L)
    (cfg leftDst rightDst : (programEventGraph g).Configuration)
    (slice :
      ∀ node, node ∈ cfg.frontier →
        ProgramField.WriteSlice g.prog)
    (hlegal :
      ∀ node hfrontier,
        (programEventGraph g).sliceLegal node (slice node hfrontier))
    (hleftOn :
      ∀ node (hfrontier : node ∈ cfg.frontier),
        leftDst.result node = some (slice node hfrontier))
    (hleftOff :
      ∀ node, node ∉ cfg.frontier → leftDst.result node = cfg.result node)
    (hrightOn :
      ∀ node (hfrontier : node ∈ cfg.frontier),
        rightDst.result node = some (slice node hfrontier))
    (hrightOff :
      ∀ node, node ∉ cfg.frontier → rightDst.result node = cfg.result node) :
    leftDst = rightDst := by
  rw [frontier_round_linearization_invariant
    g cfg leftDst slice hlegal hleftOn hleftOff]
  rw [frontier_round_linearization_invariant
    g cfg rightDst slice hlegal hrightOn hrightOff]

/-- Pairwise scheduler order is irrelevant for distinct nodes already in the
same source frontier, at the public outcome level. -/
theorem scheduler_order_irrelevant_for_independent_nodes
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration)
    {left right : ProgramNode g.prog}
    {leftSlice rightSlice : ProgramField.WriteSlice g.prog}
    (hleft : left ∈ cfg.frontier)
    (hright : right ∈ cfg.frontier)
    (hne : left ≠ right)
    (hleftLegal : (programEventGraph g).sliceLegal left leftSlice)
    (hrightLegal : (programEventGraph g).sliceLegal right rightSlice) :
    let hrightAfterLeft :=
      cfg.withResult_mem_frontier_of_ne
        hleft hright (Ne.symm hne) hleftLegal
    let hleftAfterRight :=
      cfg.withResult_mem_frontier_of_ne
        hright hleft hne hrightLegal
    (eventGraphMachine g).outcome
        ((cfg.withResult leftSlice hleft hleftLegal).withResult
          rightSlice hrightAfterLeft hrightLegal) =
      (eventGraphMachine g).outcome
        ((cfg.withResult rightSlice hright hrightLegal).withResult
          leftSlice hleftAfterRight hleftLegal) := by
  dsimp
  rw [frontier_execution_commutes
    g cfg hleft hright hne hleftLegal hrightLegal]

end Vegas

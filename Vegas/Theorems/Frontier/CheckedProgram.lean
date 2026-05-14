import Vegas.GameBridge.FOSG.FrontierStability

/-!
# Checked-Program Frontier Stability

Scheduler, linearization, and same-frontier stability facts that rely on the
graph having been generated from checked `VegasCore` syntax.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- A generated frontier node cannot share the frontier with a node that reads
one of the fields it writes. -/
theorem programEventGraph_no_frontier_read_write_race
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {writer reader : ProgramNode g.prog} {field : ProgramField g.prog}
    (hwriterFrontier : writer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread : field ∈ (ProgramNode.sem g.obligations reader).reads)
    (hwrite : field ∈ (ProgramNode.sem g.obligations writer).writeFields) :
    False :=
  eventGraph_writer_not_frontier_with_reader_of_read_write
    g hwriterFrontier hreaderFrontier hread hwrite

/-- A generated reveal cannot share the frontier with a later node that reads
the reveal target. -/
theorem programEventGraph_no_frontier_reveal_target_reader_race
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {revealer reader : ProgramNode g.prog}
    {source target : ProgramField g.prog}
    {hty : source.ty = target.ty}
    (hrevealFrontier : revealer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hsem :
      ProgramNode.sem g.obligations revealer =
        EventGraph.NodeSem.reveal source target hty)
    (hread : target ∈ (ProgramNode.sem g.obligations reader).reads) :
    False :=
  eventGraph_reveal_not_frontier_with_reader_of_target
    g hrevealFrontier hreaderFrontier hsem hread

/-- A generated reveal cannot be frontier-simultaneous with an earlier commit. -/
theorem programEventGraph_no_frontier_prior_commit_reveal_race
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {commit reveal : ProgramNode g.prog}
    {owner : P} {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (ProgramField.ty (p := g.prog)) field}
    {source target : ProgramField g.prog}
    {hty : source.ty = target.ty}
    (hcommitFrontier : commit ∈ cfg.frontier)
    (hrevealFrontier : reveal ∈ cfg.frontier)
    (hcommit :
      ProgramNode.sem g.obligations commit =
        EventGraph.NodeSem.commit owner field guard)
    (hreveal :
      ProgramNode.sem g.obligations reveal =
        EventGraph.NodeSem.reveal source target hty)
    (hrank : commit.rank < reveal.rank) :
    False :=
  eventGraph_priorCommit_not_frontier_with_reveal
    g hcommitFrontier hrevealFrontier hcommit hreveal hrank

/-- Executing one generated frontier node leaves every declared read of another
current frontier node unchanged. -/
theorem programEventGraph_frontier_read_value_stable
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {writer reader : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    {hwriterFrontier : writer ∈ cfg.frontier}
    {hwriterLegal : (programEventGraph g).sliceLegal writer slice}
    {field : ProgramField g.prog}
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread : field ∈ (ProgramNode.sem g.obligations reader).reads) :
    ProgramField.value? g.env
        ((cfg.withResult slice hwriterFrontier hwriterLegal).result) field =
      ProgramField.value? g.env cfg.result field :=
  eventGraph_value?_withResult_eq_of_frontier_read
    g hreaderFrontier hread

/-- Dynamic commit legality for one generated frontier node is stable after
executing a different frontier node. -/
theorem programEventGraph_actionLegal_stable_after_other_frontier
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {first second : ProgramNode g.prog}
    {firstSlice secondSlice : ProgramField.WriteSlice g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (programEventGraph g).sliceLegal first firstSlice)
    (hsecondAction :
      (programEventGraph g).actionLegal cfg.result second secondSlice) :
    (programEventGraph g).actionLegal
      ((cfg.withResult firstSlice hfirst hfirstLegal).result)
      second secondSlice :=
  eventGraph_actionLegal_after_frontier_withResult_of_ne
    g hfirst hsecond hne hfirstLegal hsecondAction

/-- Internal kernels for generated frontier nodes are stable after executing a
different current frontier node. -/
theorem programEventGraph_internalKernel_stable_after_other_frontier
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {first second : ProgramNode g.prog}
    {firstSlice : ProgramField.WriteSlice g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (programEventGraph g).sliceLegal first firstSlice) :
    (programEventGraph g).internalKernel second
        ((cfg.withResult firstSlice hfirst hfirstLegal).result) =
      (programEventGraph g).internalKernel second cfg.result :=
  eventGraph_internalKernel_after_frontier_withResult_of_ne
    g hfirst hsecond hne hfirstLegal

/-- Checked program event graphs admit stable frontier rounds: executing one
frontier node preserves source-legal frontier actions for the remaining
frontier. -/
theorem checkedProgram_hasStableFrontierRounds
    (g : WFProgram P L) :
    (programEventGraph g).HasStableFrontierRounds :=
  programEventGraph_hasStableFrontierRounds g

/-- Two distinct generated frontier executions commute extensionally. -/
theorem checkedProgram_frontier_execution_commutes
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
frontier and the result slice chosen for each source-frontier node. Any
linearization that records exactly those slices and leaves non-frontier nodes
unchanged reaches the canonical whole-frontier endpoint. -/
theorem checkedProgram_frontier_round_linearization_invariant
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
theorem checkedProgram_frontier_round_linearizations_agree
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
  rw [checkedProgram_frontier_round_linearization_invariant
    g cfg leftDst slice hlegal hleftOn hleftOff]
  rw [checkedProgram_frontier_round_linearization_invariant
    g cfg rightDst slice hlegal hrightOn hrightOff]

/-- Pairwise scheduler order is irrelevant for distinct nodes already in the
same source frontier, at the public outcome level. -/
theorem checkedProgram_scheduler_order_irrelevant_for_independent_nodes
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
  rw [checkedProgram_frontier_execution_commutes
    g cfg hleft hright hne hleftLegal hrightLegal]

end Vegas

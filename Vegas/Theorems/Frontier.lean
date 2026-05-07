import Vegas.Protocol.FrontierStability

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
    (cfg : (syntaxProtocolGraph g).Configuration)
    {left right : ProgramNode g.prog}
    {leftSlice rightSlice : ProgramField.WriteSlice g.prog}
    (hleft : left ∈ cfg.frontier)
    (hright : right ∈ cfg.frontier)
    (hne : left ≠ right)
    (hleftLegal : (syntaxProtocolGraph g).sliceLegal left leftSlice)
    (hrightLegal : (syntaxProtocolGraph g).sliceLegal right rightSlice) :
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

/- TODO:
theorem frontier_round_linearization_invariant ...

Any legal linearization of one frontier round yields the same extensional
configuration distribution. This needs a concrete type for frontier-round
linearizations and their induced PMF.
-/

/- TODO:
theorem scheduler_order_irrelevant_for_independent_nodes ...

Scheduler order is irrelevant for independent frontier nodes at the level of
payoff-outcome distributions. This should be stated once the scheduler/order
object is separated from `Machine.BlockLaw`.
-/

end Vegas

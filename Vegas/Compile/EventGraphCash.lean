/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Settlement
import Vegas.Compile.EventGraphReadout
import Vegas.EventGraph.Sequential

/-! # Executable integer cash from compiled terminal payoff instructions

The compiled reader evaluates Config.terminalPayoffs in the actual native
store, then applies the declared exit override using the actual excluded set.
Its correspondence with source cash holds for every structural configuration,
in every dependency mode, without execution or strategy hypotheses.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Native terminal payoff expressions evaluate to the original source
instructions in every dependency mode; mode changes only dependencies. -/
theorem terminalPayoffs_withMode_eq_source {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (mode : EventGraph.ExecutionMode)
    (config : ((toEventGraph program).withMode mode).Config) (terminal : config.cut.Terminal)
    (state : State L program.terminalCtx)
    (agree : (terminalRefs program).Agrees state config.store) :
    config.terminalPayoffs terminal = program.terminalPayoffs.map fun payoff =>
      (payoff.1, L.eval payoff.2 (sourcePublicEnv state)) := by
  unfold EventGraph.Config.terminalPayoffs
  change (payoffs program).map _ = _
  rw [payoffs, List.map_map]
  apply List.map_congr_left
  intro payoff _
  obtain ⟨who, expression⟩ := payoff
  simp only [Function.comp_apply]
  have evaluated := compilePublicExpr_eval? (terminalRefs program) state config.store
    agree expression
  simp [evaluated]

/-- The graph's executable cash reader, with the setup's declared exit override. -/
def compiledCash (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (excluded : Finset Player) (config : ((toEventGraph setup.program).withMode mode).Config)
    (who : Player) : Int :=
  if who ∈ excluded then setup.exitTransfers who else
    if terminal : config.cut.Terminal then
      transferAmount ((config.terminalPayoffs terminal).map fun payoff =>
        (payoff.1, L.toInt payoff.2)) who else 0

/-- Full typed decoding makes the actual compiled cash exactly the source cash.
Every configuration is allowed, including ones outside all execution supports. -/
theorem compiledCash_eq_source (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (excluded : Finset Player)
    (config : ((toEventGraph setup.program).withMode mode).Config) (who : Player) :
    compiledCash setup mode excluded config who =
      setup.cash excluded
        (if config.cut.Terminal then decodeState? (terminalRefs setup.program) config.store
          else none) who := by
  classical
  by_cases exited : who ∈ excluded
  · simp only [compiledCash, Setup.cash, exited, ite_true]
  · by_cases terminal : config.cut.Terminal
    · obtain ⟨state, decoded, agree⟩ := exists_decodeState_agrees
        (terminalRefs setup.program) config.store (config.store_available_of_terminal terminal)
      rw [compiledCash, Setup.cash, ite_eq_right exited, ite_eq_right exited,
        dite_eq_left terminal, ite_eq_left terminal, decoded]
      rw [terminalPayoffs_withMode_eq_source setup.program mode config terminal state agree]
      simp only [Option.elim_some, SourceProgram.evaluatePayoffs, List.map_map,
        Function.comp_def]
    · simp only [compiledCash, Setup.cash, exited, ite_false, terminal, dite_false,
        Option.elim_none]

end Vegas

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.SequentialPhaseService
import Vegas.Game.PhaseCash

/-! # Declared exit cash overrides the same compiled terminal payment

This structural native configuration has a successful true publication and an
ordinary executable payment of two. Changing only its actual excluded snapshot
selects the declared zero exit payment. No execution-support claim is made for
the excluded snapshot.
-/

namespace VegasTests.DeclaredExitCash

open Vegas Vegas.SourceProgram Vegas.Examples.SequentialPhaseService GameTheory

noncomputable def terminalConfig : compiled.Config :=
  (EventGraph.Config.initial (graph := compiled)
    (setup.eventInputs (sourceInitial true))).complete event (by decide) true (.success true)

theorem terminalConfig_terminal : terminalConfig.cut.Terminal := by
  change ({event} : Finset (Fin 1)) = Finset.univ
  decide

theorem compiled_ret_payment :
    transferAmount ((terminalConfig.terminalPayoffs terminalConfig_terminal).map
      (fun entry => (entry.1, simpleExpr.toInt entry.2))) owner = 2 := by decide

theorem compiled_cash_active : compiledCash setup .sequential ∅ terminalConfig owner = 2 := by
  rw [compiledCash, ite_eq_right (Finset.notMem_empty _), dite_eq_left terminalConfig_terminal]
  exact compiled_ret_payment

theorem compiled_cash_exited :
    compiledCash setup .sequential {owner} terminalConfig owner = setup.exitTransfers owner ∧
      setup.exitTransfers owner = 0 := by decide

theorem declared_exit_overrides_ret :
    compiledCash setup .sequential {owner} terminalConfig owner ≠
      compiledCash setup .sequential ∅ terminalConfig owner := by
  rw [compiled_cash_exited.1, compiled_cash_exited.2, compiled_cash_active]
  decide

end VegasTests.DeclaredExitCash

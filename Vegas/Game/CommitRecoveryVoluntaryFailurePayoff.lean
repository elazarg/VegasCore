/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryDebtPayoff

/-! # Fixed exclusion value for voluntary source recovery failure -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem commitRecovery_terminal_payoff_lower
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (who : Player) (final : setup.commitRecoveryProtocol.History)
    (terminal : setup.commitRecoveryProtocol.terminal final.state) :
    excludedPayoff who ≤ setup.commitRecoveryPayoff utility excludedPayoff who final := by
  cases state : final.state with
  | none => rw [state] at terminal; exact terminal.elim
  | some current =>
      rw [state] at terminal
      obtain ⟨value, read⟩ := ProtocolState.exists_readout_of_terminal setup.program current.point
        terminal
      unfold commitRecoveryPayoff
      split
      · exact le_rfl
      · simpa only [state, commitRecoverySourceState, Option.map_some, protocolReadout,
          Option.bind_some, read, Option.elim_some] using below value who

end Vegas.SourceProgram.Setup

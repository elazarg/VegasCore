/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryPayoff
import Vegas.Source.CommitRecoveryFailureCoverage

/-! # Checkpointed own debt forces the actual exclusion payoff under every continuation -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Once current-block debt is checkpointed, even arbitrary foreign policies at
new information and all later resets lead to the actual permanent-exclusion floor. -/
theorem commitRecovery_terminal_payoff_of_checkpointed_debt
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (profile : ∀ owner, setup.commitRecoveryModel.BehavioralPolicy owner)
    (history : setup.commitRecoveryProtocol.History)
    (current : CommitRecoveryState setup.program) (equality : history.state = some current)
    (owed : who ∈ current.excluded ∨
      (ProtocolState.OwesFailure who setup.program current.saved ∧
        ProtocolState.OwesFailure who setup.program current.point))
    (last : setup.commitRecoveryProtocol.History)
    (supported : last ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile history).support) :
    setup.commitRecoveryPayoff utility excludedPayoff who last = excludedPayoff who := by
  let closed : setup.commitRecoveryProtocol.State → Prop := fun state =>
    ∃ current, state = some current ∧ (who ∈ current.excluded ∨
      (ProtocolState.OwesFailure who setup.program current.saved ∧
        ProtocolState.OwesFailure who setup.program current.point))
  have retained := setup.commitRecoveryModel.runBehavioralTerminalFrom_support_closed
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile closed
    (fun state joint legal next holds reached => by
      obtain ⟨before, rfl, debt⟩ := holds
      obtain ⟨after, raw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact ⟨after, rfl, before.step_preserves_excluded_or_owesFailure who debt joint after raw⟩)
    history ⟨current, equality, owed⟩ last supported
  obtain ⟨after, afterEquality, debt⟩ := retained
  have stopped := setup.commitRecoveryModel.runBehavioralTerminalFrom_support_terminal
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile history last supported
  have excluded : who ∈ after.excluded := by
    rcases debt with excluded | debt
    · exact excluded
    · exact setup.commitRecovery_terminal_excluded_of_owesFailure last.trace after afterEquality
        who debt.2 (by
          simpa only [afterEquality, commitRecoveryProtocol, Option.elim_some] using stopped)
  apply setup.commitRecoveryPayoff_of_excluded
  simpa only [afterEquality, commitRecoveryPublic, Option.elim_some] using excluded

end Vegas.SourceProgram.Setup

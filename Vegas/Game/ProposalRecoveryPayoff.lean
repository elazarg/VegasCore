/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPayoff
import Vegas.Source.ProposalRecoveryEvolution

/-! # Original exclusion utilities in the proposal-labeled source game -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Labeled actions change public evidence, not utility or semantic recovery. -/
def proposalRecoveryPayoff
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (history : setup.proposalRecoveryProtocol.History) : ℝ :=
  setup.commitRecoveryPayoff utility excludedPayoff who
    ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩

def proposalRecoveryImagePayoff
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (image : setup.ProposalRecoveryHistoryImage) : ℝ :=
  if who ∈ (setup.commitRecoveryPublic image.1.1).1 then excludedPayoff who else
    (setup.protocolReadout (setup.commitRecoverySourceState image.1.1)).elim 0
      (fun terminal => utility terminal who)

/-- Erasing remembered private words retains every typed terminal field and
permanent exclusion. In particular no hidden failed binding is discarded. -/
theorem proposalRecoveryPayoff_eq_image
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (history : setup.proposalRecoveryProtocol.History) :
    setup.proposalRecoveryPayoff utility excludedPayoff who history =
      setup.proposalRecoveryImagePayoff utility excludedPayoff who
        (setup.proposalRecoveryErasedHistory history) := by
  unfold proposalRecoveryPayoff proposalRecoveryImagePayoff commitRecoveryPayoff
  change (if who ∈ (setup.commitRecoveryPublic history.state).1 then excludedPayoff who else
    (setup.protocolReadout (setup.commitRecoverySourceState history.state)).elim 0
      (fun terminal => utility terminal who)) =
    if who ∈ (setup.commitRecoveryPublic
      (history.state.map CommitRecoveryState.eraseHistory)).1 then excludedPayoff who else
        (setup.protocolReadout (setup.commitRecoverySourceState
          (history.state.map CommitRecoveryState.eraseHistory))).elim 0
            (fun terminal => utility terminal who)
  cases state : history.state with
  | none => rfl
  | some current =>
      change (if who ∈ current.excluded then excludedPayoff who else
        (ProtocolState.readout setup.program current.point).elim 0
          (fun terminal => utility terminal who)) =
        if who ∈ current.excluded then excludedPayoff who else
          (ProtocolState.readout setup.program
            (ProtocolState.withHistory setup.program current.point (fun _ => []))).elim 0
              (fun terminal => utility terminal who)
      rw [ProtocolState.readout_withHistory]

theorem proposalRecoveryPayoff_mem_Icc
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (lower upper : Player → ℝ)
    (bounds : ∀ terminal who, utility terminal who ∈ Set.Icc (lower who) (upper who))
    (who : Player) (history : setup.proposalRecoveryProtocol.History) :
    setup.proposalRecoveryPayoff utility excludedPayoff who history ∈
      Set.Icc (min 0 (min (excludedPayoff who) (lower who)))
        (max 0 (max (excludedPayoff who) (upper who))) :=
  setup.commitRecoveryPayoff_mem_Icc utility excludedPayoff lower upper bounds who
    ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩

end Vegas.SourceProgram.Setup

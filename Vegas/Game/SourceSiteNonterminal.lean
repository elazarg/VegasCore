/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceInformation

/-! # Source decision fibers are nonterminal

The source view identifies its instruction position, so every history in a
decision information fiber has the same length, hence the same number of
remaining instructions, and the fiber's decision witness shows that number is
positive: no history of a decision fiber has stopped.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The source protocol stops exactly when no instruction remains. -/
theorem protocol_terminal_iff (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (state : setup.ProtocolState) :
    (setup.executionProtocol admission).terminal state ↔ setup.protocolRemaining state = 0 := by
  cases state with
  | none => simp [executionProtocol, protocolRemaining]
  | some state =>
      change SourceProgram.ProtocolState.terminal setup.program state ↔
        SourceProgram.ProtocolState.remaining setup.program state = 0
      exact (SourceProgram.ProtocolState.remaining_zero_iff_terminal setup.program state).symm

/-- **Decision fibers are nonterminal.** Every history in a decision
information fiber of the source model has the decision witness's length
(`Vegas.SourceProgram.Setup.common_decision_depth`), hence its number of
remaining instructions, which is positive. -/
theorem decision_allNonterminal (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player)
    (site : (setup.informationModel admission).InformationSite who) :
    InformationModel.InformationSite.AllNonterminal (setup.informationModel admission) site := by
  intro history
  obtain ⟨witness, running, _⟩ := site.2
  rw [setup.protocol_terminal_iff admission]
  rw [setup.protocol_terminal_iff admission] at running
  have first := setup.protocol_history_length admission witness.1.trace
  have second := setup.protocol_history_length admission history.1.trace
  have depth := (setup.common_decision_depth admission who site witness).trans
    (setup.common_decision_depth admission who site history).symm
  omega

end Vegas.SourceProgram.Setup

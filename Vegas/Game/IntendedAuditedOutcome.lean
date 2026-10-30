/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.RevealServicePayoffs
import GameTheoryExtensions.Protocol.ContinuationHorizon
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # The audited outcome shared by the intended game and the runtime

Comparing the intended game with an audited runtime needs one outcome type and
one utility on it. The audited outcome is the typed terminal store, if any,
together with every player's collection probability
(`Vegas.SourceProgram.Setup.AuditedOutcome`). Its utility is the forfeited
utility of the store minus each player's collection probability times its
deposit (`Vegas.SourceProgram.Setup.auditedUtility`).

The intended game has finitely many histories when the commitment payload types
and the initial law are finite
(`Vegas.SourceProgram.Setup.intended_finite_history`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The audited outcome: the typed terminal store, if any, and every player's
collection probability. -/
abbrev AuditedOutcome := Option (Config Player L setup.program.terminalCtx) × (Player → ℝ)

/-- The utility of an audited outcome: the forfeited utility of the store, or
zero without one, minus each player's collection probability times its
deposit. -/
def auditedUtility {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (deposit : Player → ℝ) (outcome : setup.AuditedOutcome) (who : Player) : ℝ :=
  outcome.1.elim 0 (fun state => forfeitUtility setup.program forfeit utility
    (setup.parameterOutcome parameter state) who) - outcome.2 who * deposit who

/-- The finite history type of the intended game, for finite commitment payload
types and a finite initial law. -/
theorem intended_finite_history [Finite Player] (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] : Finite setup.intendedProtocol.History :=
  have : Finite (setup.executionProtocol (CommitmentInterface.values setup.program)).History :=
    setup.finite_history finite _
  Finite.of_injective (setup.intendedRestriction (CommitmentInterface.values
    setup.program)).history (setup.intendedRestriction (CommitmentInterface.values
    setup.program)).history.injective

end Vegas.SourceProgram.Setup

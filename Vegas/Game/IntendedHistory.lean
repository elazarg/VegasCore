module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceInformation
public import Vegas.Source.IntendedGame

@[expose] public section

/-! # Finite intended-game histories

The intended game has finitely many histories when the commitment payload types
and the initial law are finite.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

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

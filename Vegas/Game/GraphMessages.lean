/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphSetup
import Vegas.Graph.MessageService

/-! # The source compiler's serviced pending-message target

The target first samples the specified initial setup, then runs the actual
compiled graph in the shared public-message policy game. Player strategies
range over arbitrary native policies. Only the service realization fixes
invocation opportunities and reserved inclusion/clock commands; its wire
policy remains adaptive.

This module defines the end-to-end compiler and outcome interpretation. It
does not assert the honest or unilateral-deviation law; the unproved capstones
in `Paper.lean` state those obligations for these concrete definitions.
-/

noncomputable section
namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

/-- Every sampled private setup is initialized separately; players use one
native policy across the setup distribution. -/
def pendingGame (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) : GameForm Player :=
  runtime.servicedGame setup.graph (setup.initialLaw.map fun initial => encodeState initial.1)
    roster reactionRounds wire

/-- Source strategy translation is the composition of the two actual compilers. -/
def compilePendingStrategy (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    runtime.application.PlayerPolicy :=
  runtime.compilePlayerPolicy setup.graph who
    (compileGraphPolicy setup.program setup.namesNodup initialMap [] who policy)

/-- Missing terminal outcomes stay explicit until completion is established.
The full typed environment is an ideal semantic readout, not a ledger decoder
for undisclosed private values. -/
def pendingOutcome (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (execution : runtime.application.PolicyExecution) :
    Option (State L setup.program.terminalCtx) :=
  execution.native.application.outcome?.map setup.decodeGraph

end Vegas.SourceProgram.Setup

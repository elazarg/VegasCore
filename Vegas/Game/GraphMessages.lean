/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphSetup
import Vegas.Graph.MessageServiceTermination

/-! # The source compiler's serviced pending-message target

The target first samples the specified initial setup, then runs the actual
compiled graph in the shared public-message policy game. Player strategies
range over arbitrary native policies. Only the service realization fixes
invocation opportunities and reserved inclusion/clock commands; its wire
policy remains adaptive.

The composed target always completes under its concrete service, even with
arbitrary player policies. This does not assert the honest or unilateral-
deviation law; the unproved capstones in `Paper.lean` state those obligations
for the actual compiler and outcome interpretation defined here.
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

/-- The concrete bounded service produces a decoded terminal state for every
supported target play, including arbitrary deviations and private initial setup.
This is completion, not a source execution-law or incentive correspondence. -/
theorem pendingGame_complete (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (outcome : runtime.application.PolicyExecution)
    (supported : outcome ∈
      ((setup.pendingGame runtime roster reactionRounds wire).play players).support) :
    (setup.pendingOutcome runtime outcome).isSome = true := by
  have completed : outcome.native.application.outcome?.isSome = true := by
    apply runtime.servicedGame_complete setup.graph
      (setup.initialLaw.map fun initial => encodeState initial.1)
      roster reactionRounds wire players outcome
    exact supported
  simpa only [pendingOutcome, Option.isSome_map] using completed

end Vegas.SourceProgram.Setup

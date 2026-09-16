/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventCompilation
import Vegas.Pending.EventPolicies
import Vegas.Pending.EventService

/-! # The full-source compiler's asynchronous pending-message target

These definitions compose source-to-event-graph compilation with the native
event-addressed policy compiler and public epoch service. They specify the
actual target game and semantic readout; they do not assert an execution-law
or strategic correspondence.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Private initial setup is sampled inside the asynchronous native game.
One player profile and one pair of public service policies are used across
the entire setup distribution. -/
def eventPendingGame (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm Player :=
  runtime.servicedEventGame
    (setup.initialLaw.map fun initial => setup.eventInputs initial.1)
    roster reactionRounds wire order

/-- Compose source policy compilation with the actual event-addressed native
policy compiler. -/
def compileEventPendingStrategy (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph)
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    runtime.application.PlayerPolicy :=
  runtime.compilePlayerPolicy who
    (EventLowering.compileEventPolicy setup.program setup.namesNodup who policy)

/-- Decode the complete terminal source state, retaining missing outcomes
explicitly. This semantic readout includes undisclosed private values; it is
not a decoder available to a public ledger observer. -/
def eventPendingOutcome (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph)
    (execution : runtime.application.PolicyExecution) :
    Option (State L setup.program.terminalCtx) :=
  if terminal : execution.native.application.config.cut.Terminal then
    some (EventLowering.terminalState setup.program setup.namesNodup
      ⟨execution.native.application.config, terminal⟩)
  else none

end Vegas.SourceProgram.Setup

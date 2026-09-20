/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ValueBindingEdge
import Vegas.Game.EventMessageStrategic
import GameTheoryExtensions.Core.MixtureSimulationComposition

/-! # The whole tower, read from the value-binding game

Two edges compose. The value-binding game simulates the source game with every
deviation considered, and the source game simulates the public pending-message
service with every native deviation considered. Composition needs the left edge
to consider everything, which it does, so the deviation class of the composite
is the right edge's: arbitrary native policies.

What that buys is a statement about the host in which binding an unopenable
candidate is not among the moves. Nothing is lost by leaving it out: the
composite equates laws, so the same approximate-Nash equivalence holds at
compiled profiles.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The composed certificate: from the value-binding game straight to the
public pending-message service, admitting every native unilateral policy. -/
def valueBindingPendingSimulation (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn setup.valueBindingGame
      (setup.eventPendingGame mode runtime roster reactionRounds wire order) some
      (setup.eventPendingPublicOutcome mode runtime) (fun _ _ => True) :=
  (setup.valueBindingSimulationOn some).trans
    (setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire order)
    (fun _ _ => trivial)

/-- Compiling a value-binding profile all the way to the host. -/
def compileValueBindingPendingProfile (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (who : Player) (strategy : ValueBindingPolicy who setup.program) :
    runtime.application.PlayerPolicy :=
  setup.compileEventPendingStrategy mode runtime who strategy.val

/-- Same-error Nash preservation and reflection between the value-binding game
and the message host, against arbitrary native deviations. Commit-time failure
is absent from the source side and costs nothing. -/
theorem valueBindingPendingGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : Profile setup.valueBindingGame.sig) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who))
        ε (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who)) ↔
      IsεNash setup.valueBindingGame utility ε profile := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome who => outcome.elim (missing who) (fun result => utility result who)
  exact GameForm.MixtureSimulationOn.isεNash_compileProfile_iff
    (setup.valueBindingPendingSimulation mode runtime feasible roster reactionRounds wire order)
    optionUtility ε profile (fun _ _ => trivial)

end Vegas.SourceProgram.Setup

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PurificationEdge
import Vegas.Game.ValueBindingEdge
import Vegas.Game.EventMessageStrategic
import GameTheory.Core.MixtureSimulationComposition

/-! # The whole tower, read from a restricted source game

Both restrictions of the source game — the policies that always bind a value,
and the policies that never randomize — simulate it with every deviation
considered. Composition needs exactly that of the left edge, so each composes
with the pending-message certificate, and the deviation class of the composite
is the right edge's: arbitrary native policies.

What that buys is a statement about the real host in which the restricted move
is not available on the source side: for a profile already in the class the same
approximate-Nash equivalence holds at compiled profiles, because the composite
equates laws. That is a statement about such profiles and the deviations they
face, not a claim that the restricted game has an equilibrium.
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

/-! ## From the pure-strategy game -/

/-- The composed certificate from the pure-strategy game to the public
pending-message service, admitting every native unilateral policy. -/
def purePendingSimulation (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn setup.pureGame
      (setup.eventPendingGame mode runtime roster reactionRounds wire order) some
      (setup.eventPendingPublicOutcome mode runtime) (fun _ _ => True) :=
  (setup.pureSimulationOn some).trans
    (setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire order)
    (fun _ _ => trivial)

/-- Compiling a pure profile all the way to the host. -/
def compilePurePendingProfile (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (who : Player) (policy : PurePolicy who setup.program) :
    runtime.application.PlayerPolicy :=
  setup.compileEventPendingStrategy mode runtime who
    (PurePolicy.toBehavioral setup.program policy)

/-- Checking a pure source profile against the real host needs only pure source
deviations. -/
theorem purePendingGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : Profile setup.pureGame.sig) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who))
        ε (fun who => setup.compilePurePendingProfile mode runtime who (profile who)) ↔
      IsεNash setup.pureGame utility ε profile := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome who => outcome.elim (missing who) (fun result => utility result who)
  exact GameForm.MixtureSimulationOn.isεNash_compileProfile_iff
    (setup.purePendingSimulation mode runtime feasible roster reactionRounds wire order)
    optionUtility ε profile (fun _ _ => trivial)

end Vegas.SourceProgram.Setup

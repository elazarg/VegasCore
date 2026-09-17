/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventCompilation
import Vegas.EventGraph.ExecutionMode
import Vegas.Pending.EventPolicies
import Vegas.Pending.EventService
import Vegas.Pending.EventServiceCompletion
import Vegas.Pending.EventHonestLaw

/-! # The full-source compiler's pending-message target

These definitions compose source-to-event-graph compilation with the native
event-addressed policy compiler and public epoch service. They specify the
actual target game and semantic readout. The honest outcome law composes the
graph-to-native service theorem with the full-source graph compilation law.
Dependency modes retain the same graph code and native executor; sequential
mode adds barriers that enforce completion order.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Private initial setup is sampled inside the selected native game.
One player profile and one pair of public service policies are used across
the entire setup distribution. -/
def eventPendingGame (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm Player :=
  runtime.servicedEventGame
    (setup.initialLaw.map fun initial => setup.eventInputs initial)
    roster reactionRounds wire order

/-- Compose source policy compilation with the actual event-addressed native
policy compiler. -/
def compileEventPendingStrategy (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    runtime.application.PlayerPolicy :=
  runtime.compilePlayerPolicy who
    (setup.eventGraph.toModePolicy mode who
      (EventLowering.compileEventPolicy setup.program who policy))

/-- Decode the complete terminal source state, retaining missing outcomes
explicitly. This semantic readout includes undisclosed private values; it is
not a decoder available to a public ledger observer. -/
def eventPendingOutcome (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (execution : runtime.application.PolicyExecution) :
    Option (State L setup.program.terminalCtx) :=
  if terminal : execution.native.application.config.cut.Terminal then
    some ((EventLowering.decodeState? (EventLowering.terminalRefs setup.program)
      execution.native.application.config.store).get
        (EventLowering.decodeState?_isSome_of_available _ _
          (fun field => execution.native.application.config.store_available_of_terminal
            terminal field)))
  else none

/-- On every serviced play, the optional source-state readout is exactly the
partial store decoder. Completion discharges its terminality test, even under
arbitrary native policies; no honest-execution law is assumed. -/
theorem eventPendingGame_map_outcome (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play players).map
        (setup.eventPendingOutcome mode runtime) =
      (((setup.eventPendingGame mode runtime roster reactionRounds wire order).play players).map
        (fun execution => execution.native.application.config.store)).map
          (EventLowering.decodeState? (EventLowering.terminalRefs setup.program)) := by
  rw [FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro execution supported
  have terminal := runtime.servicedEventGame_complete _ roster reactionRounds wire order
    players execution supported
  simp only [eventPendingOutcome, dif_pos terminal, Function.comp_apply]
  exact Option.some_get _

/-- The full-source compiler preserves the terminal-state law through actual
adaptive event service and public pending-message execution. -/
theorem eventPendingGame_honest_law (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (fun who => setup.compileEventPendingStrategy mode runtime who (profile who))).map
        (setup.eventPendingOutcome mode runtime) = (setup.run profile).map some := by
  rw [setup.eventPendingGame_map_outcome]
  change (((runtime.servicedEventGame _ roster reactionRounds wire order).play
    (runtime.compileProfile
      (setup.eventGraph.toModeProfile mode
        (EventLowering.compileEventProfile setup.program profile)))).map
        (fun execution => execution.native.application.config.store)).map _ = _
  rw [runtime.servicedEventGame_honest_store_law
    (setup.eventGraph.withMode_barrierOrdered
      (EventLowering.toEventGraph_barrierOrdered setup.program) mode) feasible]
  simp only [FinDist.bind_map, FinDist.map_bind]
  simp_rw [← (setup.eventGraph.withMode mode).runPolicies_canonical_normalize_eq,
    setup.eventGraph.runPolicies_withMode_store,
    setup.eventGraph.fromModeProfile_toModeProfile]
  have canonical := congrArg (fun law => law.map some)
    (EventLowering.scheduled_setup_law setup setup.eventGraph.canonicalScheduler profile)
  simp only [FinDist.map_bind, eventGraph,
    EventLowering.terminalOutcomes_map_decode] at canonical
  exact canonical

end Vegas.SourceProgram.Setup

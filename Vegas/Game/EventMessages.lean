/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventCompilation
import Vegas.Pending.EventPolicies
import Vegas.Pending.EventService
import Vegas.Pending.EventServiceCompletion
import Vegas.Pending.EventHonestLaw

/-! # The full-source compiler's asynchronous pending-message target

These definitions compose source-to-event-graph compilation with the native
event-addressed policy compiler and public epoch service. They specify the
actual target game and semantic readout. The honest outcome law composes the
graph-to-native service theorem with the full-source graph compilation law.
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

/-- On every serviced play, the optional source-state readout is exactly the
partial store decoder. Completion discharges its terminality test, even under
arbitrary native policies; no honest-execution law is assumed. -/
theorem eventPendingGame_map_outcome (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy) :
    ((setup.eventPendingGame runtime roster reactionRounds wire order).play players).map
        (setup.eventPendingOutcome runtime) =
      (((setup.eventPendingGame runtime roster reactionRounds wire order).play players).map
        (fun execution => execution.native.application.config.store)).map
          (EventLowering.decodeState? (EventLowering.terminalRefs setup.program)
            (EventLowering.terminalPublications setup.program setup.namesNodup)) := by
  rw [FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro execution supported
  have terminal := runtime.servicedEventGame_complete _ roster reactionRounds wire order
    players execution supported
  simp only [eventPendingOutcome, dif_pos terminal, Function.comp_apply,
    EventLowering.terminalState]
  exact Option.some_get _

/-- The full-source compiler preserves the terminal-state law through actual
adaptive event service and public pending-message execution. -/
theorem eventPendingGame_honest_law (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph) (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) :
    ((setup.eventPendingGame runtime roster reactionRounds wire order).play
      (fun who => setup.compileEventPendingStrategy runtime who (profile who))).map
        (setup.eventPendingOutcome runtime) = (setup.run profile).map some := by
  rw [setup.eventPendingGame_map_outcome]
  change (((runtime.servicedEventGame _ roster reactionRounds wire order).play
    (runtime.compileProfile
      (EventLowering.compileEventProfile setup.program setup.namesNodup profile))).map
        (fun execution => execution.native.application.config.store)).map _ = _
  rw [runtime.servicedEventGame_honest_store_law
    (EventLowering.toEventGraph_barrierOrdered setup.program setup.namesNodup) feasible]
  simp only [eventGraph, EventLowering.normalizeProfile_compileEventProfile,
    FinDist.bind_map, FinDist.map_bind]
  have canonical := congrArg (fun law => law.map some)
    (EventLowering.scheduled_setup_law setup setup.eventGraph.canonicalScheduler profile)
  simp only [FinDist.map_bind, eventGraph,
    EventLowering.terminalOutcomes_map_decode] at canonical
  exact canonical

end Vegas.SourceProgram.Setup

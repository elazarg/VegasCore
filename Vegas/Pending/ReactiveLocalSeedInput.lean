/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveSchedulerImplementation
import Interaction.ReactiveRecall

/-! # Event-local inputs shared by a scheduler and its owner

A local seed controller reads the current readiness-relative clock and the
complete emitted-envelope prefix of its own event. This scoped interface can
ignore past emission times; it does not represent every separable builder.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The data passed to a selected event's private seed controller. -/
structure LocalSeedInput (graph : Vegas.EventGraph Player L) where
  /-- Current clock measured from this attempt's readiness timestamp. -/
  elapsed : Nat
  /-- Complete own emitted-envelope prefix for the selected event. -/
  emitted : List (Message Player (WitnessedPacket graph))

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Read event-local data from the scheduler's actual public input. -/
def environmentSeedInput (owner : Player) (event : graph.EventId)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) : LocalSeedInput graph where
  elapsed := view.application.clock -
    (view.application.activatedAt event).getD view.application.clock
  emitted := (view.network.inputs.filter fun message => message.sender = owner).filter
    fun message => message.payload.call.event? graph = some event

/-- Read the same data from the owner's complete actual decision input. -/
def ownerSeedInput (event : graph.EventId)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) : LocalSeedInput graph where
  elapsed := view.application.publicView.clock -
    (view.application.publicView.activatedAt event).getD view.application.publicView.clock
  emitted := ((runtime.reactiveApplication leaks).outputs past).filter
    fun message => message.payload.call.event? graph = some event

/-- Genuine input recall reconstructs the complete local seed input; no
probabilistic factorization or posterior property is assumed. -/
theorem seedInput_eq_of_inputRecall (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (owner : Player) (event : graph.EventId) :
    runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment (runtime.reactiveApplication leaks)) =
      runtime.ownerSeedInput leaks event (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner) := by
  change LocalSeedInput.mk _ ((execution.network.inputs.filter
      fun message => message.sender = owner).filter _) =
    LocalSeedInput.mk _ (((runtime.reactiveApplication leaks).outputs
      (execution.recall owner)).filter _)
  rw [recalled owner]
  rfl

/-- Every actual initialized native history supplies the same local input to
the private controller and the event owner. -/
theorem seedInput_eq_of_trace
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (owner : Player) (event : graph.EventId) :
    runtime.environmentSeedInput leaks owner event
        (control.execution.observeEnvironment (runtime.reactiveApplication leaks)) =
      runtime.ownerSeedInput leaks event (control.execution.recall owner)
        (control.execution.observe (runtime.reactiveApplication leaks) owner) :=
  runtime.seedInput_eq_of_inputRecall leaks control.execution
    ((runtime.reactiveApplication leaks).history_inputRecall initial horizon scheduler trace)
    owner event

end Vegas.EventGraphRuntime

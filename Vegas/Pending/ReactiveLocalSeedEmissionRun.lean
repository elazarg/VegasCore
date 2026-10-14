/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedEmissionPrefix
import Vegas.Pending.ReactiveLocalSeedPositiveLog
import Interaction.ReactivePolicyInvariant

/-! # Emission-prefix recovery along actual surviving ready runs

The owner's full final recall reconstructs the authored packet prefix of
every earlier seed query from its activation index. Packet publication and
receipt clocks do not enter this readout.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Actual surviving ready intervals recover all local-query packet prefixes
from own recall, allowing packets to have already been sent. -/
theorem runJoint_log_emittedAtActivation
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (preserves : ∀ execution memory next, controller.domain execution →
      execution.application.publicView.EventReady event →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next)
    (count : Nat) (execution next : (app).Execution)
    (memory after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (valid : execution.application.Invariant inputs)
    (ready : execution.application.publicView.EventReady event)
    (genuine : controller.domain execution) (recalled : execution.InputRecall app)
    (positiveMatch : positiveQueries memory.log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexMatch : memory.activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (remembered : ∀ entry ∈ memory.log,
      entry.query.activationIndex ≤
        runtime.readyActivationCount leaks event (execution.recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (execution.recall owner) entry.query.activationIndex)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    ∀ entry ∈ after.log,
      entry.query.activationIndex ≤ runtime.readyActivationCount leaks event (next.recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (next.recall owner) entry.query.activationIndex := by
  have recallInvariant :
      (app).PolicyInvariant players (fun execution => execution.InputRecall app) :=
    { respond := fun execution who action valid _ => (app).respond_inputRecall
        execution who action valid
      environment := fun execution next command valid reached => (app).environment_inputRecall
        execution next command valid reached }
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact remembered
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have first := runtime.reactive_dispatch_progress leaks inputs players execution middle _
        valid moved
      obtain ⟨ticks, progress⟩ := controller.runJoint_progress localLaw remainderLaw remainder
        inputs players count middle _ next after first.invariant later
      have middleUnfinished : event ∉ middle.application.config.cut.completed :=
        fun completed => unfinished (progress.completed completed)
      have middleReady : middle.application.publicView.EventReady event := by
        apply (middle.application.publicView_eventReady event).mpr
        rcases first.ready_or_completed event
          ((execution.application.publicView_eventReady event).mp ready) with done | ready
        · exact False.elim (middleUnfinished done)
        · exact ready
      have middleRemembered := controller.dispatch_log_emittedAtActivation remainder memory players
        execution middle recalled ready indexMatch remembered moved
      have matched := controller.dispatch_ownerLog remainder memory execution middle players genuine
        recalled positiveMatch indexMatch moved
      exact ih middle _ first.invariant middleReady
        (preserves execution memory middle genuine ready moved middleUnfinished)
        (recallInvariant.dispatch _ execution middle recalled moved) matched.1 matched.2
          middleRemembered later

end Vegas.EventGraphRuntime.LocalSeedController

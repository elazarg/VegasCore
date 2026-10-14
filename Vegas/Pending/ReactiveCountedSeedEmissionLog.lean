/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedEmissionRun
import Vegas.Pending.ReactiveCountedSeedOwnerLog

/-! # Actual counted-service emission prefixes in the local query log

The full initial game draw and arbitrary earlier execution are retained.
First readiness and protected survival derive the packet-prefix readout at
every earlier actual query, including after the owner's packet was sent.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Actual initialized clean one-packet runs reconstruct every query's authored
packet prefix from full owner recall and its local activation index. -/
theorem runJoint_counted_log_emittedAtActivation
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (owned : graph.actor? event = some owner)
    (setup : graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace
        (some ⟨remaining, none, ReactiveApplication.Execution.initial app (State.initial setup)⟩))
    (localSeed : LocalSeed) (remainderSeed : RestSeed)
    (count : Nat) (next : (app).Execution)
    (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app (State.initial setup))
          (initialMemory localSeed remainderSeed)).support)
    (ready : next.application.publicView.EventReady event)
    (unmissed : next.application.publicView.missedBindingBy owner = false) :
    ∀ entry ∈ after.log,
      entry.query.activationIndex ≤ runtime.readyActivationCount leaks event (next.recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (next.recall owner) entry.query.activationIndex := by
  classical
  have initialValid := State.initial_invariant setup
  obtain ⟨ticks, progress⟩ := controller.runJoint_progress localLaw remainderLaw remainder setup
    players count (ReactiveApplication.Execution.initial app (State.initial setup))
      (initialMemory localSeed remainderSeed) next after initialValid reached
  have readyCut := (next.application.publicView_eventReady event).mp ready
  have present := (progress.invariant.activated_iff event).mpr ⟨readyCut, by simp [owned]⟩
  obtain ⟨entered, enteredEq⟩ := Option.isSome_iff_exists.mp present
  have initialFresh : ∀ entered, (State.initial setup).activatedAt event = some entered →
      entered = (State.initial setup).clock := by
    intro entered activated
    have bounded := initialValid.activated_le event entered activated
    change entered ≤ 0 at bounded
    change entered = 0
    omega
  obtain ⟨beforeCount, afterCount, prior, total, earlier, suffix, activated, priorValid,
    priorEmpty⟩ := controller.runJoint_ready_suffix localLaw remainderLaw remainder setup players
      owned localSeed remainderSeed count
        (ReactiveApplication.Execution.initial app (State.initial setup)) next after initialValid
          initialFresh rfl ⟨entered, enteredEq⟩ readyCut.1 reached
  obtain ⟨extended, ⟨priorTrace⟩⟩ := controller.runJoint_trace localLaw remainderLaw remainder
    (bounds.onePacketMenu runtime leaks) (inputs.map State.initial) players covered beforeCount
      horizon scheduler remaining
        (ReactiveApplication.Execution.initial app (State.initial setup))
          (initialMemory localSeed remainderSeed) prior (initialMemory localSeed remainderSeed)
            trace earlier
  have priorClear := controller.runJoint_unmissed_before localLaw remainderLaw remainder players
    afterCount prior next (initialMemory localSeed remainderSeed) after suffix unmissed
  have priorGenuine : controller.domain prior := by
    rw [domainEq]
    exact runtime.countedSeedDomain_of_history leaks bounds inputs (horizon + beforeCount) extended
      ⟨remaining, none, prior⟩ priorTrace owner rfl priorClear
  have priorRecall := (app).history_inputRecall (inputs.map State.initial)
    (horizon + beforeCount) extended
      ((bounds.onePacketMenu runtime leaks).toRawTrace _ _ _ priorTrace)
  have preserves : ∀ execution memory next, controller.domain execution →
      execution.application.publicView.EventReady event →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next := by
    intro execution memory next genuine ready moved unfinished
    rw [domainEq] at genuine ⊢
    exact runtime.countedSeedDomain_dispatch_of_ready_survives leaks bounds inputs ordered players
      covered owner event owned execution next genuine
        ((execution.application.publicView_eventReady event).mp ready) _ moved unfinished
  have priorReady : prior.application.publicView.EventReady event := by
    apply (prior.application.publicView_eventReady event).mpr
    exact ((priorValid.activated_iff event).mp (by rw [activated]; rfl)).1
  apply controller.runJoint_log_emittedAtActivation localLaw remainderLaw remainder setup players
    preserves afterCount prior next (initialMemory localSeed remainderSeed) after priorValid
      priorReady priorGenuine priorRecall
  · exact priorEmpty.symm
  · have lengthEq := congrArg List.length priorEmpty
    rw [runtime.ownerActivationQueries_length] at lengthEq
    exact lengthEq.symm
  · simp [initialMemory]
  · exact readyCut.1
  · exact suffix

end Vegas.EventGraphRuntime.LocalSeedController

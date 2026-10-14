/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedReadySuffix
import Vegas.Pending.ReactiveLocalSeedEarlierClearance
import Vegas.Pending.ReactiveLocalSeedSurvivorLog
import Vegas.Pending.ReactiveLocalSeedHistory
import Vegas.Pending.ReactiveProtectedEpisode

/-! # Genuine counted-service owner logs from initialized actual runs

The selected event may become ready after arbitrary earlier execution.
Its actual first-ready earlier is clean whenever the final owner has no
binding miss; protected ordered survival then discharges the service domain.
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

/-- Actual initialized clean one-packet runs derive all surviving raw-log
invariants, including for events first activated strictly after initialization. -/
theorem runJoint_counted_ownerLog
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
    CountedQueryLog after.log ∧
      (∀ entry ∈ after.log, entry.reply = .activation ∨ entry.reply = .exhausted) ∧
      positiveQueries after.log = runtime.ownerActivationQueries leaks event (next.recall owner) ∧
      after.activationIndex = runtime.readyActivationCount leaks event (next.recall owner) ∧
      exhaustedClocks after.log =
        List.range (runtime.environmentSeedInput leaks owner event
          (next.observeEnvironment app)).elapsed ++
        if after.closedAt = some (runtime.environmentSeedInput leaks owner event
            (next.observeEnvironment app)).elapsed then
          [(runtime.environmentSeedInput leaks owner event
            (next.observeEnvironment app)).elapsed] else [] := by
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
      execution.application.Invariant setup →
      execution.application.activatedAt event = some prior.application.clock →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next := by
    intro execution memory next genuine valid active moved unfinished
    rw [domainEq] at genuine ⊢
    exact runtime.countedSeedDomain_dispatch_of_activated_survives leaks bounds inputs ordered
      players covered owner event owned execution next genuine setup valid prior.application.clock
        active _ moved unfinished
  apply controller.runJoint_survivorLog localLaw remainderLaw remainder setup players
    prior.application.clock preserves afterCount prior (initialMemory localSeed remainderSeed)
      next after readyCut.1 suffix priorGenuine priorValid activated priorRecall
        CountedQueryLog.empty
  · simp [initialMemory]
  · exact priorEmpty.symm
  · have lengthEq := congrArg List.length priorEmpty
    rw [runtime.ownerActivationQueries_length] at lengthEq
    exact lengthEq.symm
  · change [] = List.range
        (prior.application.clock -
          (prior.application.activatedAt event).getD prior.application.clock) ++
      if (none : Option Nat) = some
          (prior.application.clock - (prior.application.activatedAt event).getD
            prior.application.clock) then
        [prior.application.clock -
          (prior.application.activatedAt event).getD prior.application.clock]
          else []
    rw [activated]
    simp

end Vegas.EventGraphRuntime.LocalSeedController

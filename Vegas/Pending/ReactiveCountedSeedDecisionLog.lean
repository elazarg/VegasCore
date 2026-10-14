/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedSeedOwnerLog
import Vegas.Pending.ReactiveCountedSeedEmissionLog
import Vegas.Pending.ReactiveLocalSeedActivationLog
import Interaction.ReactiveResponseAccounting

/-! # Raw local seed logs at actual clean owner decisions

Initialized supported fixed-seed executions derive all local log invariants.
The actual next owner activation therefore has its raw-log data determined
by the owner's complete observed activation history and elapsed clock.
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

/-- Actual supported clean owner decisions determine the complete replayed
query log by genuine owner information, with no query-log recovery premise. -/
theorem runRounds_activation_log_signature
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
    (count : Nat) (before active : (app).Execution)
    (reached : before ∈ ((app).runRounds
      (controller.fixedScheduler remainder (initialMemory localSeed remainderSeed)) players count
        (ReactiveApplication.Execution.initial app (State.initial setup))).support)
    (chosen : .activate owner ∈ (controller.fixedScheduler remainder
      (initialMemory localSeed remainderSeed) before.environmentRecall
        (before.observeEnvironment app)).support)
    (observed : active ∈ (before.environmentStep app (.activate owner)).support)
    (ready : before.application.publicView.EventReady event)
    (unmissed : before.application.publicView.missedBindingBy owner = false) :
    CountedQueryLog (controller.replay remainder (initialMemory localSeed remainderSeed)
      active.environmentRecall).log ∧
    (∀ entry ∈ (controller.replay remainder (initialMemory localSeed remainderSeed)
        active.environmentRecall).log,
      entry.reply = .activation ∨ entry.reply = .exhausted) ∧
    (∀ entry ∈ (controller.replay remainder (initialMemory localSeed remainderSeed)
        active.environmentRecall).log,
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (active.recall owner) entry.query.activationIndex) ∧
    positiveQueries (controller.replay remainder (initialMemory localSeed remainderSeed)
      active.environmentRecall).log =
        runtime.ownerActivationQueries leaks event (active.recall owner) ++
          [⟨runtime.ownerSeedInput leaks event (active.recall owner) (active.observe app owner),
              runtime.readyActivationCount leaks event (active.recall owner)⟩] ∧
    (exhaustedClocks (controller.replay remainder (initialMemory localSeed remainderSeed)
      active.environmentRecall).log).length =
        (runtime.ownerSeedInput leaks event (active.recall owner)
          (active.observe app owner)).elapsed := by
  classical
  let memory := controller.replay remainder (initialMemory localSeed remainderSeed)
    before.environmentRecall
  have joint : (before, memory) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app (State.initial setup))
          (initialMemory localSeed remainderSeed)).support := by
    rw [controller.runJoint_initial]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨before, reached, rfl⟩
  obtain ⟨counted, unresolved, positives, indexed, clocks⟩ :=
    controller.runJoint_counted_ownerLog localLaw remainderLaw remainder bounds inputs ordered
      domainEq players covered owned setup horizon scheduler remaining trace localSeed remainderSeed
        count before memory joint ready unmissed
  have remembered := controller.runJoint_counted_log_emittedAtActivation localLaw remainderLaw
    remainder bounds inputs ordered domainEq players covered owned setup horizon scheduler remaining
      trace localSeed remainderSeed count before memory joint ready unmissed
  obtain ⟨extended, ⟨beforeTrace⟩⟩ := controller.runJoint_trace localLaw remainderLaw remainder
    (bounds.onePacketMenu runtime leaks) (inputs.map State.initial) players covered count horizon
      scheduler remaining (ReactiveApplication.Execution.initial app (State.initial setup))
        (initialMemory localSeed remainderSeed) before memory trace joint
  have genuine : controller.domain before := by
    rw [domainEq]
    exact runtime.countedSeedDomain_of_history leaks bounds inputs (horizon + count) extended
      ⟨remaining, none, before⟩ beforeTrace owner rfl unmissed
  have recalled := (app).history_inputRecall (inputs.map State.initial) (horizon + count) extended
    ((bounds.onePacketMenu runtime leaks).toRawTrace _ _ _ beforeTrace)
  have activated : (controller.step remainder memory before.environmentRecall
      (before.observeEnvironment app)).1 = .activate owner :=
    ((PMF.mem_support_pure_iff _ _).mp chosen).symm
  have inputEq := runtime.environmentActivation_ownerSeedInput leaks before active owner owner event
    observed
  have recallEq := (app).environmentStep_recall before active (.activate owner) observed
  obtain ⟨countedAfter, unresolvedAfter, emittedAfter, positiveEq, clockEq⟩ :=
    controller.activation_log_signature remainder memory before genuine recalled ready activated
      counted unresolved (fun entry member => (remembered entry member).2) positives indexed clocks
  have replayEq : controller.replay remainder (initialMemory localSeed remainderSeed)
      active.environmentRecall =
        (controller.step remainder memory before.environmentRecall
          (before.observeEnvironment app)).2 := by
    rw [(app).environmentStep_environmentRecall before active (.activate owner) observed]
    exact controller.replay_snoc remainder (initialMemory localSeed remainderSeed)
      before.environmentRecall ⟨before.observeEnvironment app, .activate owner⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rwa [replayEq]
  · rw [replayEq]
    exact unresolvedAfter
  · rw [replayEq, recallEq]
    exact emittedAfter
  · rw [replayEq, inputEq, recallEq]
    exact positiveEq
  · rw [replayEq, inputEq]
    exact clockEq

end Vegas.EventGraphRuntime.LocalSeedController

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedSeedOwnerLog
import Vegas.Pending.ReactiveLocalSeedUnsentActivation
import Vegas.Pending.ReactiveLocalSeedUnsent
import Interaction.ReactiveResponseAccounting

/-! # Raw local seed logs at actual clean unsent decisions

Initialized supported fixed-seed executions derive all local log invariants.
The actual next owner activation therefore has a raw-log encoding determined
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

/-- Actual supported clean unsent decisions determine the complete replayed
query log by genuine owner information, with no query-log recovery premise. -/
theorem runRounds_unsent_activation_signature
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
    (unmissed : before.application.publicView.missedBindingBy owner = false)
    (empty : (runtime.ownerSeedInput leaks event (active.recall owner)
      (active.observe app owner)).emitted = []) :
    ∃ word : List Bool,
      (controller.replay remainder (initialMemory localSeed remainderSeed)
        active.environmentRecall).log =
          encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word ∧
      positiveQueries (encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word) =
        runtime.ownerActivationQueries leaks event (active.recall owner) ++
          [⟨runtime.ownerSeedInput leaks event (active.recall owner) (active.observe app owner),
              runtime.readyActivationCount leaks event (active.recall owner)⟩] ∧
      (exhaustedClocks
        (encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word)).length =
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
  have beforeEmpty : (runtime.environmentSeedInput leaks owner event
      (before.observeEnvironment app)).emitted = [] := by
    rw [runtime.seedInput_eq_of_inputRecall leaks before recalled owner event, ← inputEq]
    exact empty
  have unsent := controller.runJoint_unsent_queryInputs localLaw remainderLaw remainder players
    count (State.initial setup) localSeed remainderSeed before memory joint beforeEmpty
  obtain ⟨word, logEq, positiveEq, clockEq⟩ := controller.activation_unsent_signature remainder
    memory before genuine recalled ready activated counted unresolved unsent
      (by rwa [inputEq] at empty) positives indexed clocks
  have replayEq : controller.replay remainder (initialMemory localSeed remainderSeed)
      active.environmentRecall =
        (controller.step remainder memory before.environmentRecall
          (before.observeEnvironment app)).2 := by
    rw [(app).environmentStep_environmentRecall before active (.activate owner) observed]
    exact controller.replay_snoc remainder (initialMemory localSeed remainderSeed)
      before.environmentRecall ⟨before.observeEnvironment app, .activate owner⟩
  refine ⟨word, ?_, ?_, ?_⟩
  · rwa [replayEq]
  · rw [inputEq, recallEq]
    exact positiveEq
  · rw [inputEq]
    exact clockEq

end Vegas.EventGraphRuntime.LocalSeedController

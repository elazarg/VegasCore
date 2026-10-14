/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedSeedDecisionLog

/-! # Genuine owner observation fibers determine the private query log

The two histories may have different hidden initial inputs, command counts,
and scheduler seeds. Equality of actual active-owner information nevertheless
forces equality of their complete local query logs.
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

/-- Every genuine supported clean owner observation fiber has one raw
local query log. Initial private game inputs and scheduler seeds may vary. -/
theorem runRounds_log_eq_of_owner_info
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (owned : graph.actor? event = some owner)
    (setup : Bool → graph.Inputs) (horizon : Bool → Nat)
    (scheduler : Bool → (app).Scheduler) (remaining : Bool → Nat)
    (trace : ∀ side, ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      (horizon side) (scheduler side)).Trace
        (some ⟨remaining side, none,
          ReactiveApplication.Execution.initial app (State.initial (setup side))⟩))
    (localSeed : Bool → LocalSeed) (remainderSeed : Bool → RestSeed)
    (count : Bool → Nat) (before active : Bool → (app).Execution)
    (reached : ∀ side, before side ∈ ((app).runRounds
      (controller.fixedScheduler remainder (initialMemory (localSeed side) (remainderSeed side)))
        players (count side)
          (ReactiveApplication.Execution.initial app (State.initial (setup side)))).support)
    (chosen : ∀ side, .activate owner ∈ (controller.fixedScheduler remainder
      (initialMemory (localSeed side) (remainderSeed side)) (before side).environmentRecall
        ((before side).observeEnvironment app)).support)
    (observed : ∀ side,
      active side ∈ ((before side).environmentStep app (.activate owner)).support)
    (ready : ∀ side, (before side).application.publicView.EventReady event)
    (unmissed : ∀ side, (before side).application.publicView.missedBindingBy owner = false)
    (informationEq : ((active false).recall owner, (active false).observe app owner) =
      ((active true).recall owner, (active true).observe app owner)) :
    (controller.replay remainder (initialMemory (localSeed false) (remainderSeed false))
      (active false).environmentRecall).log =
    (controller.replay remainder (initialMemory (localSeed true) (remainderSeed true))
      (active true).environmentRecall).log := by
  obtain ⟨left, leftUnresolved, leftEmitted, leftPositive, leftClock⟩ :=
    controller.runRounds_activation_log_signature localLaw remainderLaw remainder bounds inputs
      ordered domainEq players covered owned (setup false) (horizon false) (scheduler false)
        (remaining false) (trace false) (localSeed false) (remainderSeed false) (count false)
          (before false) (active false) (reached false) (chosen false) (observed false)
            (ready false) (unmissed false)
  obtain ⟨right, rightUnresolved, rightEmitted, rightPositive, rightClock⟩ :=
    controller.runRounds_activation_log_signature localLaw remainderLaw remainder bounds inputs
      ordered domainEq players covered owned (setup true) (horizon true) (scheduler true)
        (remaining true) (trace true) (localSeed true) (remainderSeed true) (count true)
          (before true) (active true) (reached true) (chosen true) (observed true)
            (ready true) (unmissed true)
  have recallEq := congrArg Prod.fst informationEq
  have viewEq := congrArg Prod.snd informationEq
  change (active false).recall owner = (active true).recall owner at recallEq
  change (active false).observe app owner = (active true).observe app owner at viewEq
  have positiveEq : positiveQueries (controller.replay remainder
      (initialMemory (localSeed false) (remainderSeed false))
        (active false).environmentRecall).log =
        positiveQueries (controller.replay remainder
          (initialMemory (localSeed true) (remainderSeed true))
            (active true).environmentRecall).log := by
    rw [leftPositive, rightPositive, recallEq, viewEq]
  have clockEq : (exhaustedClocks (controller.replay remainder
      (initialMemory (localSeed false) (remainderSeed false))
        (active false).environmentRecall).log).length =
      (exhaustedClocks (controller.replay remainder
        (initialMemory (localSeed true) (remainderSeed true))
          (active true).environmentRecall).log).length := by
    rw [leftClock, rightClock, recallEq, viewEq]
  let emittedAt := runtime.ownerEmissionsAtActivation leaks event ((active false).recall owner)
  have rightEmitted' : ∀ entry ∈ (controller.replay remainder
      (initialMemory (localSeed true) (remainderSeed true)) (active true).environmentRecall).log,
      entry.query.input.emitted = emittedAt entry.query.activationIndex := by
    intro entry member
    dsimp only [emittedAt]
    rw [recallEq]
    exact rightEmitted entry member
  exact CountedQueryLog.eq_of_emission_signature emittedAt left right leftEmitted rightEmitted'
    leftUnresolved rightUnresolved positiveEq clockEq

end Vegas.EventGraphRuntime.LocalSeedController

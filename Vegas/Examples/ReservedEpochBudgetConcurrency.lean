/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReservedEpochUsableConcurrency
import Vegas.Pending.ReservedEpochEmptyPrefix
import Vegas.Pending.ReservedEpochResources
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveSchedulerImplementation

/-! # Simultaneous usable traffic at the derived reserved capacity -/

noncomputable section

namespace Vegas.Examples.ReservedEpochBudgetConcurrency

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open CommitTimingInformation
open ReservedEpochConcurrency (tape prior response players offer first second commitmentMessage)

abbrev Player := CommitTimingInformation.Player
abbrev graph := CommitTimingInformation.graph
abbrev runtime := CommitTimingInformation.runtime
abbrev leaks := CommitTimingInformation.leaks
abbrev app := CommitTimingInformation.app

private def body (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := [] }

def beforeOffers (capacity : Nat) (bit : Bool) : app.Execution :=
  ReservedEpoch.emptyPrefix runtime leaks capacity (initialExecution bit)

def afterFirst (capacity : Nat) (reverse bit : Bool) : app.Execution :=
  offer (beforeOffers capacity bit) (first reverse)

def afterBoth (capacity : Nat) (reverse bit : Bool) : app.Execution :=
  offer (afterFirst capacity reverse bit) (second reverse)

def selectedScheduler (capacity : Nat) : app.Scheduler :=
  (ReservedEpoch.implementation runtime leaks capacity prior).scheduler

private theorem beforeOffers_body (capacity : Nat) (bit : Bool) :
    body (beforeOffers capacity bit) = body (ReservedEpochConcurrency.beforeOffers bit) := by
  simp only [body, beforeOffers, ReservedEpoch.emptyPrefix_application,
      ReservedEpoch.emptyPrefix_network, ReservedEpoch.emptyPrefix_receipts,
      ReservedEpoch.emptyPrefix_recall, ReservedEpochConcurrency.beforeOffers,
      ReservedEpochConcurrency.waitState]

private theorem offer_body (left right : app.Execution) (owner : Player)
    (same : body left = body right) : body (offer left owner) = body (offer right owner) := by
  have application := congrArg ReactiveApplication.Execution.application same
  have network := congrArg ReactiveApplication.Execution.network same
  have receipts := congrArg ReactiveApplication.Execution.receipts same
  have sameRecall := congrArg ReactiveApplication.Execution.recall same
  change left.application = right.application at application
  change left.network = right.network at network
  change left.receipts = right.receipts at receipts
  change left.recall = right.recall at sameRecall
  simp only [body, offer, ReactiveApplication.Execution.sampledActivation,
    ReactiveApplication.Execution.respond, ReactiveApplication.Execution.observe,
    ReactiveApplication.Execution.observeEnvironment, application, network, receipts, sameRecall]

private theorem afterBoth_body (capacity : Nat) (reverse bit : Bool) :
    body (afterBoth capacity reverse bit) = body (ReservedEpochConcurrency.afterBoth reverse bit) :=
  offer_body _ _ (second reverse)
    (offer_body _ _ (first reverse) (beforeOffers_body capacity bit))

private theorem completeActivation (execution : app.Execution) (owner : Player) :
    execution.environmentStep app (.activate owner) =
      PMF.pure (execution.sampledActivation app owner
        (execution.network.pending.map Message.id).toFinset) := by
  rw [ReactiveApplication.Execution.activation_samples]
  change (MessageNetwork.completePendingObservation owner execution.network.pending).map _ = _
  simp only [MessageNetwork.completePendingObservation, PMF.pure_map]

private theorem round_offer (capacity : Nat) (reverse : Bool) (position : Fin 2)
    (execution : app.Execution)
    (cursor : execution.environmentRecall.length = capacity + position.val) :
    app.round (ReservedEpoch.family runtime leaks capacity (tape reverse)) players execution =
      PMF.pure (offer execution ((tape reverse).owner 0 position)) := by
  have selected := ReservedEpoch.activation_at runtime leaks capacity (tape reverse) 0 position
    (execution.observeEnvironment app) (by rfl)
  simp only [Nat.zero_mul, Nat.zero_add] at selected
  simp only [ReactiveApplication.round, ReservedEpoch.family, PMF.pure_bind, cursor, selected,
    ReactiveApplication.dispatch, completeActivation, PMF.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    players, PMF.pure_map, offer]

theorem first_callbacks_law (capacity : Nat) (reverse bit : Bool) :
    app.runRounds (ReservedEpoch.family runtime leaks capacity (tape reverse)) players
      (capacity + 2) (initialExecution bit) = PMF.pure (afterBoth capacity reverse bit) := by
  have empty := ReservedEpoch.empty_processing_prefix_law runtime leaks capacity (tape reverse)
    players 0 0 capacity (initialExecution bit) (by simp only [Nat.zero_mul, Nat.zero_add]; rfl)
      (by omega) (by rfl) rfl
  have firstRound := round_offer capacity reverse 0 (beforeOffers capacity bit) (by
    rw [beforeOffers, ReservedEpoch.emptyPrefix_length]
    change 0 + capacity = capacity + 0
    omega)
  have secondRound := round_offer capacity reverse 1 (afterFirst capacity reverse bit) (by
    simp only [afterFirst, offer, beforeOffers, ReactiveApplication.Execution.sampledActivation,
      ReactiveApplication.respond_environmentRecall, List.length_append, List.length_singleton,
      ReservedEpoch.emptyPrefix_length]
    change 0 + capacity + 1 = capacity + 1
    omega)
  rw [ReservedEpochConcurrency.tape_owner_first] at firstRound
  rw [ReservedEpochConcurrency.tape_owner_second] at secondRound
  rw [app.runRounds_add, empty, PMF.pure_bind]
  change (app.round _ _ (beforeOffers capacity bit)).bind _ = _
  rw [firstRound, PMF.pure_bind]
  change (app.round _ _ (afterFirst capacity reverse bit)).bind _ = _
  rw [secondRound, PMF.pure_bind]
  rfl

theorem concurrent_prefix_supported (capacity : Nat) (reverse bit : Bool) :
    afterBoth capacity reverse bit ∈ (app.runRounds (selectedScheduler capacity) players
      (capacity + 2) (initialExecution bit)).support := by
  have realized := ReservedEpoch.realize runtime leaks capacity prior players (capacity + 2)
    (initialState bit)
  change (prior.bind fun tape => app.runRounds (ReservedEpoch.family runtime leaks capacity tape)
    players (capacity + 2) (initialExecution bit)) =
      app.runRounds (selectedScheduler capacity) players (capacity + 2) (initialExecution bit)
        at realized
  rw [← realized, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨tape reverse, ReservedEpochConcurrency.tape_supported reverse, by
    rw [first_callbacks_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl⟩

theorem two_valid_packets_pending (capacity : Nat) (reverse bit : Bool) :
    (afterBoth capacity reverse bit).network.pending =
        [commitmentMessage (first reverse), commitmentMessage (second reverse)] ∧
      first reverse ≠ second reverse ∧
      ∀ owner : Player,
        commitmentMessage owner ∈ (afterBoth capacity reverse bit).network.pending ∧
        PhaseCount.permits (afterBoth capacity reverse bit).network.inputs
          (commitmentMessage owner) = true ∧
        (afterBoth capacity reverse bit).application.current.native.WithinDeadline runtime
          (bindingEvent owner) ∧
        (∃ next, app.handle (afterBoth capacity reverse bit).application
          (commitmentMessage owner) = some next) ∧
        (afterBoth capacity reverse bit).application.current.native.bindingResult
          (owner, .prepared 0) .bool = .success true := by
  have application := congrArg ReactiveApplication.Execution.application
    (afterBoth_body capacity reverse bit)
  have network := congrArg ReactiveApplication.Execution.network
    (afterBoth_body capacity reverse bit)
  change (afterBoth capacity reverse bit).application =
    (ReservedEpochConcurrency.afterBoth reverse bit).application at application
  change (afterBoth capacity reverse bit).network =
    (ReservedEpochConcurrency.afterBoth reverse bit).network at network
  rw [application, network]
  refine ⟨ReservedEpochConcurrency.canonical_pending reverse bit,
    ReservedEpochConcurrency.distinct_pending_owners reverse, ?_⟩
  intro owner
  refine ⟨ReservedEpochConcurrency.owner_message_pending reverse bit owner, ?_,
    ReservedEpochConcurrency.pending_binding_timely reverse bit owner,
    ReservedEpochConcurrency.pending_binding_admissible reverse bit owner,
    ReservedEpochConcurrency.pending_binding_usable reverse bit owner⟩
  rw [ReservedEpochConcurrency.pending_inputs]
  exact ReservedEpochConcurrency.pending_permitted reverse bit _
    (ReservedEpochConcurrency.owner_message_pending reverse bit owner)

theorem derived_capacity_supported (reverse bit : Bool) :
    afterBoth (ReservedEpoch.packetCapacity runtime) reverse bit ∈
      (app.runRounds (selectedScheduler (ReservedEpoch.packetCapacity runtime)) players
        (ReservedEpoch.packetCapacity runtime + 2) (initialExecution bit)).support ∧
    (afterBoth (ReservedEpoch.packetCapacity runtime) reverse bit).network.pending =
      [commitmentMessage (first reverse), commitmentMessage (second reverse)] :=
  ⟨concurrent_prefix_supported _ reverse bit, (two_valid_packets_pending _ reverse bit).1⟩

end Vegas.Examples.ReservedEpochBudgetConcurrency

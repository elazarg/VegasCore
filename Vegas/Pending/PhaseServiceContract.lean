/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ReactiveServiceConditions

/-! # Opportunity and protected inclusion for physical attempt coordinates -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "P" => phaseApplication runtime leaks

/-- An actual activation in the same physical readiness episode, retaining the
original activation stamp and the full recorded environment observation. -/
def OwnerActivatedSince (history : List (P).EnvironmentEntry)
    (coordinate : CommitAttemptEvent graph) (owner : Player) (entered : Nat) : Prop :=
  ∃ entry ∈ history, entry.command = .activate owner ∧
    entry.beforeView.application.attempt = coordinate.attempt ∧
    entry.beforeView.application.native.EventReady coordinate.event ∧
    entry.beforeView.application.native.activatedAt coordinate.event = some entered

/-- Once its original reaction bound has passed, a currently ready event has
an owner activation in its own attempt and readiness episode. -/
def OpportunityAt (execution : (P).Execution) (delay : graph.EventId → Nat) : Prop :=
  ∀ event owner entered, graph.actor? event = some owner →
    execution.application.current.native.publicView.EventReady event →
    execution.application.current.native.activatedAt event = some entered →
    entered + delay event < execution.application.current.native.clock →
    OwnerActivatedSince runtime leaks execution.environmentRecall
      ⟨execution.application.attempt, event⟩ owner entered

/-- Only another identifier emitted by the same owner for the same physical
attempt-event coordinate removes the sole-packet guarantee. -/
def EmitsOtherFor (entry : (P).PlayerEntry) (coordinate : CommitAttemptEvent graph)
    (identifier : MessageId Player) : Prop :=
  ∃ message, entry.emitted = some message ∧ message.sender = identifier.1 ∧
    message.payload.attempt = coordinate.attempt ∧
    message.payload.packet.call.event? graph = some coordinate.event ∧ message.id ≠ identifier

/-- Protected inclusion retains the original strict clock bound. Retirement
ends the original coordinate; a newly installed attempt is a different event. -/
def ProtectedInclusionAt (execution : (P).Execution) (bound : graph.EventId → Nat) : Prop :=
  ∀ (coordinate : CommitAttemptEvent graph) owner,
    graph.actor? coordinate.event = some owner →
    ∀ (earlier later : List (P).PlayerEntry) entry message,
      execution.recall owner = earlier ++ entry :: later →
      entry.emitted = some message → message.sender = owner →
      message.payload.attempt = coordinate.attempt →
      message.payload.packet.call.event? graph = some coordinate.event →
      entry.beforeView.application.1.publicView.EventReady coordinate.event →
      (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor runtime leaks other coordinate message.id) →
      execution.application.attempt = coordinate.attempt →
      coordinate.event ∉ execution.application.current.native.config.cut.completed →
      entry.beforeView.application.1.publicView.clock + bound coordinate.event <
        execution.application.current.native.clock →
      ∃ accepted, (message.id, accepted) ∈ execution.receipts

/-- Opportunity quantifies over every legal physical history, including all
deviations and every retry; it is not a property only of a prescribed profile. -/
def Opportunity (initial : PMF (P).State) (horizon : Nat) (scheduler : (P).Scheduler)
    (delay : graph.EventId → Nat) : Prop :=
  ∀ control, ((P).protocol initial horizon scheduler).Trace (some control) →
    OpportunityAt runtime leaks control.execution delay

/-- The sole-packet inclusion guarantee applies at every legal physical
history, with its complete retained submissions and receipts. -/
def ProtectedInclusion (initial : PMF (P).State) (horizon : Nat) (scheduler : (P).Scheduler)
    (bound : graph.EventId → Nat) : Prop :=
  ∀ control, ((P).protocol initial horizon scheduler).Trace (some control) →
    ProtectedInclusionAt runtime leaks control.execution bound

/-- Finite protocol settlement has completed the surviving semantic graph;
voided attempt records remain in the physical state and recall. -/
def CompletesPlay (initial : PMF (P).State) (horizon : Nat) (scheduler : (P).Scheduler) : Prop :=
  ∀ control, ((P).protocol initial horizon scheduler).Trace (some control) →
    (P).terminal (some control) → control.execution.application.current.native.config.cut.Terminal

/-- The asynchronous service contract is imposed on actual physical runs.
The existing runtime `AsyncTimely` supplies its separate numerical margin. -/
structure AsyncContract (initial : PMF (P).State) (horizon : Nat) (scheduler : (P).Scheduler)
    (delay bound : graph.EventId → Nat) : Prop where
  opportunity : Opportunity runtime leaks initial horizon scheduler delay
  inclusion : ProtectedInclusion runtime leaks initial horizon scheduler bound
  completes : CompletesPlay runtime leaks initial horizon scheduler

end Vegas.EventGraphRuntime.PhaseService

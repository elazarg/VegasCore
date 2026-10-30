/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactivePublication
import Interaction.MessageNetworkIdentity
import Vegas.Pending.ServicePlan

/-! # Reserved service with one owner activation

A network opportunity can activate any player, include a packet, or wait.
Activation samples private observations using a separate rule. Those samples
are absent from scheduler state and recall.
Application sampling, clock ticks, and expiry remain controlled by the
service contract. Each strategic visit reserves one owner activation followed
by network opportunities and event-addressed inclusion. There is no reaction
roster and no private preparation phase.
Each envelope can be included at most once, including when its call is rejected.
Retrying a call requires a fresh envelope.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

inductive NetworkChoice (Player : Type) where
  | activate (who : Player)
  | include (id : MessageId Player)
  | wait

def NetworkChoice.command (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    NetworkChoice Player → (runtime.reactiveApplication leaks).Command
  | .activate who => .activate who
  | .include id => .include id
  | .wait => .wait

abbrev NetworkPolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :=
  List (runtime.reactiveApplication leaks).EnvironmentEntry →
    (runtime.reactiveApplication leaks).EnvironmentView → PMF (NetworkChoice Player)

/-- A network policy branches finitely at every recall and view. -/
class NetworkPolicy.FiniteSupport {runtime : EventGraphRuntime graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    (network : runtime.NetworkPolicy leaks) : Prop where
  support_finite : ∀ history view, (network history view).support.Finite

/-- Selection is by event and authenticated author, excluding spent identifiers. -/
def reactiveLatest (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
      (runtime.reactiveApplication leaks).Command :=
  match view.network.pending.reverse.find? (fun message =>
      message.sender = owner ∧ message.payload.call.event? graph = some event ∧
        view.Unpublished (runtime.reactiveApplication leaks) message.id) with
  | none => .wait
  | some message => .include message.id

/-- Including the latest packet for a completed target preserves the application.
Identifier uniqueness ensures the selected identifier names the selected packet. -/
theorem reactiveLatest_application_of_completed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (event : graph.EventId) (owner : Player)
    (completed : event ∈ execution.application.config.cut.completed)
    (unique : execution.network.UniqueIds)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (runtime.reactiveLatest leaks event owner
        (execution.observeEnvironment (runtime.reactiveApplication leaks)))).support) :
    next.application = execution.application := by
  unfold reactiveLatest at reached
  split at reached
  · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff] at reached
    subst next
    rfl
  · rename_i selected selectedEq
    have selectedPending := List.mem_reverse.mp (List.mem_of_find?_eq_some selectedEq)
    have selectedAddressed := List.find?_some selectedEq
    simp only [decide_eq_true_eq] at selectedAddressed
    have selectedNamed : selected.payload.call.event? graph = some event := selectedAddressed.2.1
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff] at reached
    subst next
    change (execution.includePending (runtime.reactiveApplication leaks)
      selected.id).application = _
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases lookup : execution.network.lookup selected.id with
    | none => rfl
    | some message =>
        have present := List.mem_of_find?_eq_some lookup
        have identifiedBool := List.find?_some lookup
        have identified : message.id = selected.id := by
          simpa only [decide_eq_true_eq] using identifiedBool
        have same : message = selected :=
          (unique.pending selected selectedPending).pending message present identified
        subst message
        have rejected := reactiveHandle_none (leaks := leaks)
          (handle_eq_none_of_completed runtime execution.application
            ⟨selected.id, selected.payload.call⟩ event selectedNamed completed)
        simp only [rejected, Option.getD_none]

def interactionInstruction (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks)
    (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
    ServiceInstruction graph → PMF (runtime.reactiveApplication leaks).Command
  | .player who => PMF.pure (.activate who)
  | .wire => (network history view).map (fun choice =>
      (runtime.reactiveApplication leaks).atMostOnceCommand view (choice.command runtime leaks))
  | .includeLatest event owner => PMF.pure (runtime.reactiveLatest leaks event owner view)
  | .sample event => PMF.pure (.application (.executeSample event))
  | .tick => PMF.pure (.application .advanceClock)
  | .expire event => PMF.pure (.application (.expire event))

/-- A reserved instruction branches finitely without any restriction on the
discretionary network policy, because it never calls that policy. -/
theorem interactionInstruction_support_finite_of_not_wire (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks)
    (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (instruction : ServiceInstruction graph) (reserved : instruction ≠ .wire) :
    (runtime.interactionInstruction leaks network history view instruction).support.Finite := by
  cases instruction <;> simp_all [interactionInstruction]

end Vegas.EventGraphRuntime

-- ReactiveBindingService and ReactiveDisclosureService prove full wire-block
-- realization under prescribed-owner packet integrity. Conflicting packets
-- from earlier deviations by that owner require a separate continuation analysis.

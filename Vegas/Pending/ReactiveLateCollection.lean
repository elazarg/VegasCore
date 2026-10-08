/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLateFailure
import Vegas.Pending.ReactiveSettledCollection

/-! # Collection from packets that may stay dead

A packet whose event completes without accepting it is forbidden by the
settled record, so an audit that observes every forbidden packet of its author
with probability at least `rate` collects from the author with at least that
probability at every such terminal history. When terminal play from a history
leaves the packet without an accepting receipt with probability at least
`floor`, under any behavioral continuation, the expected collection is at
least `rate * floor`: the two factors are the audit's coverage and the
builder's failure floor, and nothing is assumed about how the packet's fate
correlates with the continuation. The late-send instance reads the floor off
`Vegas.EventGraphRuntime.LateSendsFailAtLeast`.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A packet emitted by an entry of a player's recall is in the traffic of the
state. -/
theorem emitted_mem_stateTraffic (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (history : (menu.protocol initial horizon scheduler).History)
    (control : (runtime.reactiveApplication leaks).Control)
    (current : history.state = some control) (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who)
    (message : Message Player (WitnessedPacket graph)) (emitted : entry.emitted = some message) :
    ∃ record ∈ (runtime.reactiveApplication leaks).stateTraffic history.state,
      record.envelope = message := by
  have input := (runtime.reactiveApplication leaks).history_inputRecall initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  have traffic := (runtime.reactiveApplication leaks).stateTraffic_inputs initial horizon
    scheduler (menu.toRawTrace initial horizon scheduler history.trace)
  rw [current] at input traffic ⊢
  change control.execution.InputRecall _ at input
  change _ = control.execution.network.inputs at traffic
  have output : message ∈
      (runtime.reactiveApplication leaks).outputs (control.execution.recall who) :=
    List.mem_filterMap.mpr ⟨entry, member, emitted⟩
  rw [← input who] at output
  have carried := (List.mem_filter.mp output).1
  rw [← traffic] at carried
  exact List.mem_map.mp carried

variable [Fintype Player]

/-- **Collection from a packet that may stay dead.** A packet of `who` present
in the traffic at a history is forbidden by every settled record in which its
event completed without accepting it. If terminal play from the history, under
a behavioral continuation, leaves the packet without an accepting receipt with
probability at least `floor`, and the audit observes every forbidden packet of
`who` with probability at least `rate`, then the expected collection from
`who` is at least `rate * floor`. -/
theorem deadPacket_collection_continuation
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (completes : CompletesPlay runtime leaks initial horizon scheduler)
    (sample : List (SettledRecord graph × Message Player (WitnessedPacket graph)) →
      PMF (List (SettledRecord graph × Message Player (WitnessedPacket graph))))
    (who : Player) (rate : ℝ) (nonnegative : 0 ≤ rate)
    (coverage : ∀ actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol initial horizon scheduler).History)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).stateTraffic history.state)
    (sender : record.envelope.sender = who) (event : graph.EventId)
    (named : record.envelope.payload.call.event? graph = some event) (floor : ℝ)
    (fails : floor ≤ (((menu.information initial horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded initial horizon scheduler).wellFoundedHistories profile
          history).toOuterMeasure
      {final | ∀ control, final.state = some control →
        (record.envelope.id, true) ∉ control.execution.receipts}).toReal) :
    rate * floor ≤ expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded initial horizon scheduler).wellFoundedHistories profile history)
      (fun final => TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks fun settled =>
          (runtime.reactiveApplication leaks).sampledTrafficAudit
            (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
            (fun evidence => evidence.1.permits evidence.2) sample)
        final.state who) := by
  classical
  let dead : Set (menu.protocol initial horizon scheduler).History :=
    {final | ∀ control, final.state = some control →
      (record.envelope.id, true) ∉ control.execution.receipts}
  have pointwise : ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded initial horizon scheduler).wellFoundedHistories profile history).support,
      rate * (if final ∈ dead then (1 : ℝ) else 0) ≤
        TerminalAudit.charge (runtime.serviceAuditObservation leaks)
          (runtime.serviceAudit leaks fun settled =>
            (runtime.reactiveApplication leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) sample)
          final.state who := by
    intro final supported
    split_ifs with isDead
    · rw [mul_one]
      have terminal := (menu.information initial horizon
        scheduler).runBehavioralTerminalFrom_support_terminal _ profile history final supported
      have reach : (menu.protocol initial horizon scheduler).ReachesWithin (2 * horizon + 1)
          history final := by
        rw [(menu.information initial horizon
          scheduler).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _
          (menu.bounded initial horizon scheduler)] at supported
        exact (menu.information initial horizon scheduler).runBehavioralFrom_reachesWithin
          profile _ history final supported
      have persist : record ∈ (runtime.reactiveApplication leaks).stateTraffic final.state := by
        rw [← menu.trafficAudit_eq_stateTraffic initial horizon scheduler history] at present
        rw [← menu.trafficAudit_eq_stateTraffic initial horizon scheduler final]
        exact (menu.trafficAudit_reaches initial horizon scheduler reach).subset present
      obtain ⟨state, trace⟩ := final
      cases state with
      | none => exact (show False from terminal).elim
      | some control =>
          have cutTerminal : control.execution.application.config.cut.completed = Finset.univ :=
            completes control (menu.toRawTrace initial horizon scheduler trace) terminal
          have settled : event ∈
              (runtime.settledRecord leaks control.execution).view.observation.completionOrder := by
            change event ∈
              (graph.publicObserve control.execution.application.config).completionOrder
            rw [EventGraph.publicObserve_completionOrder]
            exact (control.execution.application.config.history_exact event).mpr
              (by rw [cutTerminal]; exact Finset.mem_univ event)
          have forbidden :
              (runtime.settledRecord leaks control.execution).permits record.envelope = false :=
            SettledRecord.permits_eq_false_of_settled _ _ event named settled
              (fun accepted => isDead control rfl accepted.1)
          exact runtime.serviceAudit_charge_from_record leaks
            (fun settled traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
            (fun evidence => evidence.1.permits evidence.2) sample who rate coverage control record
            persist sender forbidden
    · rw [mul_zero]
      exact (TerminalAudit.charge_mem_Icc _ _ _ _).1
  calc rate * floor ≤ rate * ((((menu.information initial horizon
          scheduler).runBehavioralTerminalFrom
          (menu.bounded initial horizon scheduler).wellFoundedHistories profile
            history).toOuterMeasure dead).toReal) :=
        mul_le_mul_of_nonneg_left fails nonnegative
    _ = expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom
          (menu.bounded initial horizon scheduler).wellFoundedHistories profile history)
          (fun final => rate * if final ∈ dead then (1 : ℝ) else 0) := by
        rw [expect_const_mul]
        congr 1
        rw [← expect_indicator _ dead]
        exact congrArg (expect _) (funext fun final => by congr)
    _ ≤ _ := expect_mono pointwise
        (payoffIntegrable_of_bounded _ _ (C := |rate|) fun final => by split_ifs <;> simp)
        (TerminalAudit.payoffIntegrable_charge _ _ _ _)

/-- **Late-send collection from the failure floor and the coverage rate.** In
the bounded raw runtime of a builder whose late sends fail with probability at
least `floor`, after an owner has sent a late packet for its event, every
behavioral continuation collects from the owner with expected probability at
least `rate * floor`, when the audit observes every forbidden packet of the
owner with probability at least `rate`. -/
theorem lateSend_collection_continuation (bounds : MessageBounds graph)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (completes : CompletesPlay runtime leaks initial horizon scheduler)
    (sample : List (SettledRecord graph × Message Player (WitnessedPacket graph)) →
      PMF (List (SettledRecord graph × Message Player (WitnessedPacket graph))))
    (rate : ℝ) (nonnegative : 0 ≤ rate) (floor : ℝ)
    (lateFailure : runtime.LateSendsFailAtLeast leaks bounds initial horizon scheduler floor)
    (profile : ∀ player, ((bounds.rawMenu runtime leaks).information initial horizon
      scheduler).BehavioralPolicy player)
    (history : ((bounds.rawMenu runtime leaks).protocol initial horizon scheduler).History)
    (control : (runtime.reactiveApplication leaks).Control) (current : history.state = some control)
    (event : graph.EventId) (owner : Player) (owned : graph.actor? event = some owner)
    (coverage : ∀ actual record, record ∈ actual → record.2.sender = owner →
      record.1.permits record.2 = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (earlier later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph))
    (recalled : control.execution.recall owner = earlier ++ entry :: later)
    (sender : message.sender = owner) (late : runtime.LateSend leaks event earlier entry message) :
    rate * floor ≤
      expect (((bounds.rawMenu runtime leaks).information initial horizon
          scheduler).runBehavioralTerminalFrom
          ((bounds.rawMenu runtime leaks).bounded initial horizon scheduler).wellFoundedHistories
          profile history)
        (fun final => TerminalAudit.charge (runtime.serviceAuditObservation leaks)
          (runtime.serviceAudit leaks fun settled =>
            (runtime.reactiveApplication leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) sample)
          final.state owner) := by
  obtain ⟨record, present, envelope⟩ := runtime.emitted_mem_stateTraffic leaks
    (bounds.rawMenu runtime leaks) initial horizon scheduler history control current owner entry
    (by rw [recalled]; simp) message late.1
  have fails := lateFailure profile history control current event owner owned earlier later entry
    message recalled sender late
  rw [← envelope] at fails
  exact runtime.deadPacket_collection_continuation leaks (bounds.rawMenu runtime leaks) initial
    horizon scheduler completes sample owner rate nonnegative coverage profile history record
    present (by rw [envelope]; exact sender) event (by rw [envelope]; exact late.2.1) floor fails

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMonitoring
import Vegas.Pending.EventPublicBarrier
import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.ReactiveServiceEvaluation

/-! # Monitoring packets outside the current public event

A barrier-ordered graph has at most one ready public event. A report included
while that event remains ready therefore rejects every differently addressed
packet, even if its address becomes valid later. The persistent receipt records
this actual rejection without adding timestamps, phase certificates, or access
to the watcher's private sample. Freshness excludes already published envelopes.

The service must schedule this report block before completing the current event.
The lemmas do not classify all departures, prove reporting incentives, or show
that every rejected packet deserves a charge.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Public service for a reporting window. The broadcaster and original author
come from the existing wire input; the private sample is not inspected. -/
def reportNetwork (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (watcher : Player) : runtime.NetworkPolicy leaks := fun _ view =>
  PMF.pure <| match view.network.inputs.getLast? with
    | none => .wait
    | some input =>
        if input.broadcaster = watcher ∧ input.envelope.sender ≠ watcher then
          .include input.envelope.id else .wait

theorem reportNetwork_instruction (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (watcher : Player)
    (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
    runtime.interactionInstruction leaks (runtime.reportNetwork leaks watcher)
      history view .wire =
        PMF.pure ((runtime.reactiveApplication leaks).includeReported watcher view) := by
  cases latest : view.network.inputs.getLast? with
  | none =>
      simp [interactionInstruction, reportNetwork, ReactiveApplication.includeReported,
        latest, NetworkChoice.command, ReactiveApplication.atMostOnceCommand, PMF.pure_map]
  | some input =>
      by_cases reported : input.broadcaster = watcher ∧ input.envelope.sender ≠ watcher <;>
        simp [interactionInstruction, reportNetwork, ReactiveApplication.includeReported,
          latest, reported, NetworkChoice.command, ReactiveApplication.atMostOnceCommand,
          PMF.pure_map]

/-- The generic monitoring proof is the actual two-instruction native service
block, not a separately assumed report-delivery mechanism. -/
theorem run_report_plan (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    runtime.runInteractionPlan leaks players (runtime.reportNetwork leaks watcher)
      [.player watcher, .wire] execution =
        (runtime.reactiveApplication leaks).reportInclusion players watcher execution := by
  have active : runtime.interactionStep leaks players (runtime.reportNetwork leaks watcher)
      (.player watcher) execution =
        (runtime.reactiveApplication leaks).dispatch players (.activate watcher) execution := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind]
  rw [runInteractionPlan, active]
  simp only [runInteractionPlan, interactionStep, reportNetwork_instruction,
    PMF.pure_bind, PMF.bind_pure, ReactiveApplication.reportInclusion]

/-- Rejection depends on the current ready event, not merely the author.
This also covers premature packets for a later event owned by the same player. -/
theorem handle_eq_none_of_other_event_ready_public
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (state : State graph) (current : graph.EventId)
    (isPublic : (graph.outputLayout current).IsPublic)
    (ready : state.config.cut.Ready current)
    (message : Message Player (Payload graph))
    (other : Payload.event? graph message.payload ≠ some current) :
    runtime.handle state message = none := by
  cases accepted : runtime.handle state message with
  | none => rfl
  | some next =>
      obtain ⟨actual, addressed, actualReady, _, _⟩ :=
        runtime.handle_config_mem_step state next message accepted
      have same := ordered.ready_public_unique state.config.cut isPublic ready actualReady
      exact (other (addressed.trans (congrArg some same))).elim

/-- The existing native report block gives an attributable rejected receipt
with at least the passive sampling probability. Every later policy and scheduler
is unrestricted, including later publication and pending-message observation. -/
theorem sampling_out_of_phase_receipt_lower
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (ordered : graph.BarrierOrdered) (current : graph.EventId)
    (isPublic : (graph.outputLayout current).IsPublic)
    (ready : execution.application.config.cut.Ready current)
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : execution.network.lookup id = some message) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (other : Payload.event? graph message.payload.call ≠ some current)
    (reports : ∀ observed ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
        (.activate watcher)).support,
      message ∈ (observed.observe (runtime.reactiveApplication leaks) watcher).messages.leaked →
        players watcher (observed.recall watcher)
            (observed.observe (runtime.reactiveApplication leaks) watcher) =
          PMF.pure ⟨some (.replay id)⟩)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat) :
    ((leaks watcher execution.network.pending).toOuterMeasure {selected | id ∈ selected}).toReal ≤
      ((((runtime.reactiveApplication leaks).reportInclusion players watcher execution).bind
        ((runtime.reactiveApplication leaks).runRounds scheduler players count)).toOuterMeasure
            {final | (id, false) ∈ final.receipts}).toReal := by
  apply (runtime.reactiveApplication leaks).sampling_rejected_receipt_lower players watcher
    execution id message found foreign unknown fresh reports _ scheduler count
  exact runtime.handle_eq_none_of_other_event_ready_public ordered execution.application current
    isPublic ready ⟨message.id, message.payload.call⟩ other

end Vegas.EventGraphRuntime

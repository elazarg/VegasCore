/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingFirstPacket
import Vegas.Game.SourceServiceLateDecisionCompletion
import Vegas.Pending.ReactiveDecisionOrigin

/-! # Actual owner-silent completion of an unrecorded decision

The initialized raw trace and actual owner recall rule out an earlier owner
packet. The owner-silent continuation preserves that fact. Complete play and
the actual accepted-packet origin then force a public missed decision.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- An actual owner-silent completed continuation of an unrecorded strategic
event has a public miss and no owner packet naming the event. -/
theorem sourceService_silent_unrecorded_completion
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (Function.update players owner (application setup leaks).silentPolicy)
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support) :
    event ∈ stopped.application.config.cut.completed ∧
      event ∈ stopped.application.missedEvents ∧
      (runtime setup).eventRecorded leaks (stopped.recall owner) event = false ∧
      stopped.network.Satisfies (fun message => message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event) := by
  let app := application setup leaks
  let silentPlayers := Function.update players owner app.silentPolicy
  have retained : app.PolicyInvariant silentPlayers
      (fun current => (runtime setup).eventRecorded leaks (current.recall owner) event = false) := {
    respond := fun current who response holds supported => by
      apply Eq.trans ((runtime setup).eventRecorded_respond_other leaks current who owner response
        event ?_) holds
      intro same
      subst who
      dsimp only [silentPlayers] at supported
      rw [Function.update_self] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      intro impossible
      cases impossible
    environment := fun current next command holds moved => by
      rw [app.environmentStep_recall current next command moved]
      exact holds }
  obtain ⟨used, budget, rounds, length⟩ := app.runUntil_runRounds scheduler silentPlayers
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - execution.environmentRecall.length) execution stopped reached
  have unrecordedFinal := retained.runRounds scheduler used execution stopped unrecorded rounds
  have accounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
  change execution.environmentRecall.length + remaining = horizon at accounted
  have completed := runUntilHorizon_completes contract.completes (by omega)
    (by simpa only [show horizon - execution.environmentRecall.length = remaining by omega]
      using trace) stopped reached
  have within : used ≤ remaining := by omega
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler silentPlayers
    (remaining - used) used execution stopped
    (by simpa only [Nat.sub_add_cancel within] using trace) rounds
  have facts := legalFacts setup leaks horizon scheduler _ finalTrace
  have noPacket := sourceService_unrecorded_event_packets setup leaks stopped owner event
    facts.provenance unrecordedFinal
  have marked : event ∈ stopped.application.missedEvents := by
    by_contra clear
    have inputTrace := finalTrace
    rw [initialLaw_eq_inputs] at inputTrace
    have origin := completedDecisionRecall_history (runtime setup) leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler inputTrace
    obtain ⟨message, output, authored, named, _receipt⟩ := origin event owner owned completed clear
    rw [← facts.inputs owner] at output
    exact noPacket.inputs message (List.mem_filter.mp output).1 authored named
  exact ⟨completed, marked, unrecordedFinal, noPacket⟩

end Vegas

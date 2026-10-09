/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveProvenance
import Interaction.ReactiveTrafficState

/-! # Ledger identifiers certify the actual authored envelope

Actual raw histories retain full envelope identity across authored inputs,
traffic records and ledger entries. A published identifier cannot certify a
different payload or certificate from the message originally submitted.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Authenticated provenance and exact own output recall put every retained
network envelope in the complete list of authored inputs. -/
theorem retained_envelopes_mem_inputs (execution : app.Execution)
    (origins : execution.Provenance app) (recalled : execution.InputRecall app) :
    execution.network.Satisfies (fun message => message ∈ execution.network.inputs) := by
  apply origins.mono
  intro message issued
  obtain ⟨entry, member, _, _, emitted, _⟩ := issued
  have output : message ∈ app.outputs (execution.recall message.sender) :=
    List.mem_filterMap.mpr ⟨entry, member, emitted⟩
  rw [← recalled message.sender] at output
  exact (List.mem_filter.mp output).1

/-- Every ledger envelope was actually submitted at an earlier player
response, even if the application rejected that envelope. -/
theorem ledger_subset_inputs_history (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.network.ledger ⊆ control.execution.network.inputs := by
  exact (app.retained_envelopes_mem_inputs control.execution
    (app.history_provenance initial horizon scheduler trace)
    (app.history_inputRecall initial horizon scheduler trace)).ledger

/-- Two actual authored input envelopes with the same identifier have the
same complete contents. No payload or scheduler restriction is assumed. -/
theorem input_identifier_injective_history (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (first second : Message Principal app.Payload)
    (firstInput : first ∈ control.execution.network.inputs)
    (secondInput : second ∈ control.execution.network.inputs)
    (same : first.id = second.id) : first = second := by
  have unique := app.uniqueIds_history scheduler initial horizon control trace
  exact (unique.inputs second secondInput).inputs first firstInput same

/-- A ledger entry bearing an authored input's identifier is that exact
input envelope, including its certificate and payload. -/
theorem input_envelope_eq_ledger_of_id_eq (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (message published : Message Principal app.Payload)
    (input : message ∈ control.execution.network.inputs)
    (ledger : published ∈ control.execution.network.ledger)
    (same : message.id = published.id) : message = published := by
  have unique := app.uniqueIds_history scheduler initial horizon control trace
  exact ((unique.inputs message input).ledger published ledger same.symm).symm

/-- Identifier matching against the public ledger certifies the actual
envelope from the execution's complete traffic readout. -/
theorem traffic_envelope_eq_ledger_of_id_eq (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (traffic : app.TrafficRecord) (member : traffic ∈ app.executionTraffic control.execution)
    (published : Message Principal app.Payload)
    (ledger : published ∈ control.execution.network.ledger)
    (same : traffic.envelope.id = published.id) : traffic.envelope = published := by
  have inputs := app.stateTraffic_inputs initial horizon scheduler trace
  change (app.executionTraffic control.execution).map TrafficRecord.envelope =
    control.execution.network.inputs at inputs
  apply app.input_envelope_eq_ledger_of_id_eq initial horizon scheduler control trace
    traffic.envelope published _ ledger same
  rw [← inputs]
  exact List.mem_map.mpr ⟨traffic, member, rfl⟩

/-- If an actual traffic identifier is published, its original complete
envelope is present in the ledger. -/
theorem traffic_envelope_mem_ledger_of_published (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (traffic : app.TrafficRecord) (member : traffic ∈ app.executionTraffic control.execution)
    (published : traffic.envelope.id ∈ control.execution.network.ledger.map Message.id) :
    traffic.envelope ∈ control.execution.network.ledger := by
  obtain ⟨message, ledger, same⟩ := List.mem_map.mp published
  have actual := app.traffic_envelope_eq_ledger_of_id_eq initial horizon scheduler control trace
    traffic member message ledger same.symm
  exact actual.symm ▸ ledger

end Interaction.ReactiveApplication

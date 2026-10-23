/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveProvenance

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

end Interaction.ReactiveApplication

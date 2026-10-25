/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveInputOrder

/-! # Collection from persistent earlier-input verdicts -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
    (app : ReactiveApplication Principal)

/-- A per-record collection bound persists through every actual menu continuation.
The checker may depend on the entire earlier same-author input context. -/
theorem audit_collection_continuation
    (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    (verdict : List (Message Principal app.Payload) → Message Principal app.Payload → Bool)
    (congruent : ∀ left right message,
      (∀ other, (other ∈ left ∧ other.sender = message.sender ∧ other.id.2 < message.id.2) ↔
        (other ∈ right ∧ other.sender = message.sender ∧ other.id.2 < message.id.2)) →
      verdict left message = verdict right message)
    (audit : List app.TrafficRecord → PMF (Principal → Bool)) (bound : Principal → ℝ)
    (collected : ∀ traffic record, record ∈ traffic →
      verdict (traffic.map TrafficRecord.envelope) record.envelope = false →
      bound record.envelope.sender ≤
        (((audit traffic).map (fun charges => charges record.envelope.sender)) true).toReal)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (control : app.Control) (current : history.state = some control)
    (message : Message Principal app.Payload) (present : message ∈ control.execution.network.inputs)
    (forbidden : verdict control.execution.network.inputs message = false) :
    bound message.sender ≤
      expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history)
        (fun final => TerminalAudit.charge app.stateTraffic audit final.state message.sender) := by
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  calc
    bound message.sender =
        expect (model.runBehavioralFrom profile fuel history)
          (fun _ => bound message.sender) :=
      (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _)
        (TerminalAudit.payoffIntegrable_charge _ _ _ _)
      intro final supported
      have path := menu.reaches_raw initial horizon scheduler
        (protocol.runRandomizedFor_reachesWithin (model.randomizedChooser profile) fuel history
          final supported)
      have traffic := app.stateTraffic_reaches initial horizon scheduler path
      change app.stateTraffic history.state <+: app.stateTraffic final.state at traffic
      rw [current] at traffic
      have currentInputs := app.stateTraffic_inputs initial horizon scheduler
        (menu.toRawTrace initial horizon scheduler history.trace)
      change (app.stateTraffic history.state).map ReactiveApplication.TrafficRecord.envelope =
        history.state.elim [] (fun control => control.execution.network.inputs) at currentInputs
      rw [current] at currentInputs
      obtain ⟨record, recorded, envelope⟩ := List.mem_map.mp (by rw [currentInputs]; exact present :
        message ∈ (app.stateTraffic (some control)).map ReactiveApplication.TrafficRecord.envelope)
      have kept : record ∈ app.stateTraffic final.state := traffic.subset recorded
      cases finalState : final.state with
      | none =>
          rw [finalState] at kept
          exact (List.not_mem_nil kept).elim
      | some after =>
          have retained := app.earlier_inputs_reaches path control after current finalState message
            present
          have finalInputs := app.stateTraffic_inputs initial horizon scheduler
            (menu.toRawTrace initial horizon scheduler final.trace)
          change (app.stateTraffic final.state).map ReactiveApplication.TrafficRecord.envelope =
            final.state.elim [] (fun control => control.execution.network.inputs) at finalInputs
          rw [finalState] at finalInputs kept
          have charged := collected (app.stateTraffic (some after)) record kept
            (by rw [finalInputs, envelope];
                exact (congruent _ _ message retained.2).trans forbidden)
          rw [envelope] at charged
          exact charged

end Interaction.ReactiveApplication

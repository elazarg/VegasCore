/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobService
import Vegas.Examples.LateOpeningRuntimeUtility
import Mathlib.Data.List.TakeWhile

/-! # Authentic collection after a clean accepted Bob binding

Bob has one compiled binding event. An accepted commitment using his first
prepared handle passes the settled content check. A later certified opening
also passes once accepted. Authentic sampling therefore charges neither kind
of envelope, independently of their emission clocks or the escrow size.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobService

/-- The prefix contains only accepted canonical Bob binding envelopes.
Alice's earlier traffic is unrestricted. -/
def CleanBindings (execution : app.Execution) : Prop :=
  ∀ message ∈ execution.network.inputs, message.sender = bob →
    ∃ token, message.payload =
      ⟨.commitment bobBindEvent (bob, .prepared 0), none, token⟩ ∧
      (message.id, true) ∈ execution.receipts

/-- Bob owns exactly one binding, so no Bob binding precedes it even in an
arbitrary public completion list. -/
theorem binding_count_before (view : PublicView nativeGraph) :
    view.bindingCountBefore bob bobBindEvent = 0 := by
  have predicate : bindingOwnedBy nativeGraph bob =
      fun event => decide (event = bobBindEvent) := by
    funext event
    change Fin 3 at event
    fin_cases event <;> rfl
  unfold PublicView.bindingCountBefore
  rw [predicate]
  apply List.countP_eq_zero.mpr
  intro event member
  have different := List.mem_takeWhile_imp member
  simpa only [decide_eq_true_eq] using different

/-- An accepted canonical first binding is permitted at every settled record. -/
theorem binding_permitted (record : SettledRecord nativeGraph)
    (message : Message Player (WitnessedPacket nativeGraph))
    (owner : message.sender = bob) (token : Option (ReadinessToken nativeGraph))
    (content : message.payload = ⟨.commitment bobBindEvent (bob, .prepared 0), none, token⟩)
    (accepted : (message.id, true) ∈ record.receipts) : record.permits message = true := by
  apply SettledRecord.permits_of_accepted record message bobBindEvent
    (by simp only [content]; rfl) accepted
  unfold SettledRecord.SettledContent
  rw [content]
  change (none : Option (OpeningFact nativeGraph)) = none ∧
    (bob, Slot.prepared (inputCount := nativeGraph.inputCount) 0) =
      (message.sender, Slot.prepared (record.view.bindingCountBefore message.sender bobBindEvent))
  rw [owner, binding_count_before]
  exact ⟨rfl, rfl⟩

/-- Successful Bob binding has no public binding omission. -/
theorem no_binding_omission (physical : EventGraphRuntime.State nativeGraph)
    (valid : physical.BindingInvariant) (answer : Answer)
    (bound : physical.config.store (.inr bobBindEvent) = some (.success answer)) :
    physical.publicView.missedBindingBy bob = false := by
  obtain ⟨candidate, accepted, _, _⟩ := valid.success_provenance bobBinding answer bound
  apply physical.publicView.missedBindingBy_clear
  intro event
  change Fin 3 at event
  fin_cases event
  · exact physical.publicView.missedBinding_of_not_binding aliceEvent
      (by intro owner payload same; cases same)
  · exact physical.publicView.missedBinding_of_accepted bobBindEvent candidate accepted
  · exact physical.publicView.missedBinding_of_not_binding bobRevealEvent
      (by intro owner payload same; cases same)

/-- The actual final audit is zero when all Bob envelopes are accepted
canonical bindings or the specified accepted certified answer opening. -/
theorem charge_zero (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (answer : Answer)
    (bound : control.execution.application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (origin : app.Execution) (candidate : Handle nativeGraph)
    (accepted : ((openingMessage origin candidate answer).id, true) ∈ control.execution.receipts)
    (only : ∀ message ∈ control.execution.network.inputs, message.sender = bob →
      (∃ token, message.payload =
        ⟨.commitment bobBindEvent (bob, .prepared 0), none, token⟩ ∧
        (message.id, true) ∈ control.execution.receipts) ∨
      message = openingMessage origin candidate answer)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks sample)
      (some control) bob = 0 := by
  have aligned : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph))) LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control) := by
    have same : (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
      rw [PMF.map_comp]
      rfl
    rwa [same]
  have valid := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) aligned
  change TerminalAudit.charge
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
      app.sampledTrafficAudit
        (fun traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
        (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
        sample) (some control) bob = 0
  rw [LateOpeningRuntimeService.runtime.serviceAudit_charge,
    no_binding_omission control.execution.application valid answer bound]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro traffic member owner
    have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change (app.executionTraffic control.execution).map
      ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
    have present : traffic.envelope ∈ control.execution.network.inputs := by
      rw [← inputs]
      exact List.mem_map.mpr ⟨traffic, member, rfl⟩
    change (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits
      traffic.envelope = true
    rcases only traffic.envelope present owner with ⟨token, content, receipt⟩ | same
    · exact binding_permitted _ _ owner token content receipt
    · rw [same]
      exact opening_permitted origin candidate answer _ accepted

end Vegas.Examples.LateOpeningRuntimeBobAudit

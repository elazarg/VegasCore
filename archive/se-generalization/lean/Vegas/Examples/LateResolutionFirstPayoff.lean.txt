/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionFirstDecision
import Vegas.Examples.LateResolutionSourceEquilibrium

/-! # Actual settlement after an accepted protected first decision -/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

def firstDecisionEndpoint (disclose : Bool) : app.Execution :=
  completedExpiryExecution (tickExecution (tickExecution (waitExecution
    ((secondDecisionExecution disclose).respond app owner ⟨none⟩))))

theorem first_decision_completed (disclose : Bool) :
    resolution ∈ (secondDecisionExecution disclose).application.config.cut.completed := by
  rw [second_decision_application]
  change resolution ∈ (firstExecution.application.config.cut.complete resolution
    first_resolution_ready).completed
  exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)

theorem first_decision_pending (disclose : Bool) :
    (secondDecisionExecution disclose).network.pending = [] := by
  cases disclose <;> rfl

theorem first_completed_rounds (disclose : Bool) :
    app.runRounds scheduler (fun _ => app.silentPolicy) 4
      ((secondDecisionExecution disclose).respond app owner ⟨none⟩) =
      PMF.pure (firstDecisionEndpoint disclose) := by
  let current := (secondDecisionExecution disclose).respond app owner ⟨none⟩
  have position : current.environmentRecall.length = 6 := rfl
  have selected : stageCommand 6 (current.observeEnvironment app) = .wait := by
    change latestWithhold (current.observeEnvironment app) = .wait
    have empty : current.network.pending = [] := first_decision_pending disclose
    simp only [latestWithhold, ReactiveApplication.Execution.observeEnvironment,
      MessageNetwork.publicView, empty, List.reverse_nil, List.find?_nil]
  have first : app.round scheduler (fun _ => app.silentPolicy) current =
      current.environmentStep app .wait := by
    simp only [ReactiveApplication.round, scheduler, position, selected, PMF.pure_bind,
      ReactiveApplication.dispatch]
    change (current.environmentStep app .wait).bind PMF.pure = _
    exact PMF.bind_pure _
  rw [ReactiveApplication.runRounds, first, wait_environment, PMF.pure_bind]
  rw [ticks_before_expiry (waitExecution current) (by
    simp only [waitExecution, List.length_append, List.length_singleton, position])]
  have completed : resolution ∈
      (tickExecution (tickExecution (waitExecution current))).application.config.cut.completed :=
    first_decision_completed disclose
  rw [expiry_environment_completed _ completed]
  rfl

theorem first_endpoint_application (disclose : Bool) :
    (firstDecisionEndpoint disclose).application =
      { firstDecisionState disclose with clock := 3 } := by
  change { (secondDecisionExecution disclose).application with
    clock := (secondDecisionExecution disclose).application.clock + 1 + 1 } = _
  rw [second_decision_application]

theorem first_endpoint_readout (disclose : Bool) :
    sourceReadout setup leaks (app.finished (firstDecisionEndpoint disclose)) =
      some (sourceDone disclose).state := by
  apply sourceReadout_eq_some
  · rw [first_endpoint_application]
    cases disclose <;> decide
  · rw [first_endpoint_application]
    intro name cell source
    cases source with
    | here => cases disclose <;> rfl
    | there source =>
      cases source with
      | here => rfl
      | there source =>
        cases source with
        | here => rfl
        | there source =>
          cases source with
          | here => rfl
          | there source => cases source

theorem first_endpoint_content (disclose : Bool) :
    ((runtime setup).settledRecord leaks (firstDecisionEndpoint disclose)).SettledContent
      (firstDecisionMessage disclose) := by
  cases disclose with
  | false => rfl
  | true =>
      constructor
      · rfl
      · rfl

theorem first_endpoint_traffic (disclose : Bool) :
    (app.executionTraffic (firstDecisionEndpoint disclose)).map
      ReactiveApplication.TrafficRecord.envelope = [firstDecisionMessage disclose] := by
  cases disclose <;> rfl

theorem first_endpoint_permitted (disclose : Bool) (record : app.TrafficRecord)
    (present : record ∈ app.executionTraffic (firstDecisionEndpoint disclose)) :
    ((runtime setup).settledRecord leaks (firstDecisionEndpoint disclose)).permits
      record.envelope = true := by
  have member : record.envelope ∈ [firstDecisionMessage disclose] := by
    rw [← first_endpoint_traffic disclose]
    exact List.mem_map.mpr ⟨record, present, rfl⟩
  have same := List.mem_singleton.mp member
  rw [same]
  apply SettledRecord.permits_of_accepted _ _ resolution
  · cases disclose <;> rfl
  · change ((owner, 0), true) ∈ (firstDecisionEndpoint disclose).receipts
    exact (first_decision_included disclose).2
  · exact first_endpoint_content disclose

theorem first_endpoint_charge (disclose : Bool)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    GameTheory.Enforcement.TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (app.finished (firstDecisionEndpoint disclose))
        owner = 0 := by
  unfold sourceServiceAudit ReactiveApplication.finished
  rw [(runtime setup).serviceAudit_charge]
  have clear : (firstDecisionEndpoint disclose).application.publicView.missedDecisionBy owner =
      false := by rw [first_endpoint_application]; cases disclose <;> rfl
  rw [clear]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record present _
    exact first_endpoint_permitted disclose record present

theorem first_endpoint_value (disclose : Bool)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) :
    auditedUtility sample deposit (app.finished (firstDecisionEndpoint disclose)) owner =
      if disclose then 1 else 0 := by
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
  rw [first_endpoint_charge disclose sample authentic]
  simp only [zero_mul, sub_zero]
  unfold baseUtility
  rw [first_endpoint_readout]
  cases disclose <;> rfl

end Vegas.LateResolutionService

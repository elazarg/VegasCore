/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionFirstOptimality
import Vegas.Pending.ReactiveCompletedConfig

/-! # Raw continuation bounds after either recorded first resolution

These bounds use the actual completed typed configuration. They allow every
raw response and every later physical policy; authentic observation is not
needed for their upper bounds because the actual collected charge is
nonnegative. The clean retained comparator has zero charge by the separate
initialized first-decision settlement theorem.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

theorem second_decision_config_complete (disclose : Bool) :
    (secondDecisionExecution disclose).application.config.cut.completed = Finset.univ := by
  rw [second_decision_application]
  change insert resolution (insert sample1 (insert sample0 ∅)) =
    (Finset.univ : Finset nativeGraph.EventId)
  decide

theorem completed_response_rounds_config (disclose : Bool) (response : app.Action)
    (players : Player → app.Policy) (count : Nat) (last : app.Execution)
    (supported : last ∈ (app.runRounds scheduler players count
      ((secondDecisionExecution disclose).respond app owner response)).support) :
    last.application.config = (secondDecisionExecution disclose).application.config := by
  let preserved := (runtime setup).reactiveCompletedConfigInvariant leaks
    (secondDecisionExecution disclose).application.config (second_decision_config_complete disclose)
  exact (preserved.policyInvariant app players).runRounds scheduler count _ last
    (preserved.respond _ owner response rfl) supported

theorem completed_config_readout (disclose : Bool) (last : app.Execution)
    (same : last.application.config = (secondDecisionExecution disclose).application.config) :
    sourceReadout setup leaks (app.finished last) = some (sourceDone disclose).state := by
  have endpoint : (firstDecisionEndpoint disclose).application.config =
      (secondDecisionExecution disclose).application.config := by
    rw [first_endpoint_application, second_decision_application]
  have decoded : sourceReadout setup leaks (app.finished last) =
      sourceReadout setup leaks (app.finished (firstDecisionEndpoint disclose)) := by
    unfold sourceReadout ReactiveApplication.finished
    simp only [Option.bind_some]
    rw [same, endpoint]
  exact decoded.trans (first_endpoint_readout disclose)

theorem completed_config_audited_value_le (disclose : Bool) (last : app.Execution)
    (same : last.application.config = (secondDecisionExecution disclose).application.config)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) :
    auditedUtility sample deposit (app.finished last) owner ≤ if disclose then 1 else 0 := by
  have charge := (GameTheory.Enforcement.TerminalAudit.charge_mem_Icc
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
    (app.finished last) owner).1
  have base : baseUtility setup leaks sourceUtility (app.finished last) owner =
      if disclose then 1 else 0 := by
    unfold baseUtility
    rw [completed_config_readout disclose last same]
    cases disclose <;> rfl
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
  rw [base]
  exact sub_le_self _ (mul_nonneg charge nonnegative)

/-- The actual terminal native law of any response menu cannot improve the
recorded source value at a completed second input. -/
theorem completed_native_value_le (menu : app.ResponseMenu)
    (profile : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (disclose : Bool)
    (current : history.state = some ⟨4, some owner, secondDecisionExecution disclose⟩)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) :
    expect ((menu.information (initialLaw setup) horizon scheduler).runBehavioralFrom
      profile 21 history) (fun final => auditedUtility sample deposit final.state owner) ≤
        if disclose then 1 else 0 := by
  have integrable : PayoffIntegrable
      ((menu.information (initialLaw setup) horizon scheduler).runBehavioralFrom
        profile 21 history) (fun final => auditedUtility sample deposit final.state owner) := by
    apply payoffIntegrable_of_bounded _ _ (C := 1 + deposit)
    intro final
    have bounds := auditedUtility_bounds sample deposit nonnegative final.state owner
    exact abs_le.mpr ⟨by linarith [bounds.1], by linarith [bounds.2]⟩
  apply expect_le_const _ _ integrable _
  intro final supported
  have reached : final.state ∈
      (((menu.information (initialLaw setup) horizon scheduler).runBehavioralFrom
        profile 21 history).map ExecutionProtocol.History.state).support := by
    rw [PMF.support_map]
    exact Set.mem_image_of_mem _ supported
  rw [late_native_run_state menu profile history (secondDecisionExecution disclose) current
    (by rfl), PMF.support_bind] at reached
  obtain ⟨action, _, finished⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨last, continued, same⟩ := PMF.support_map .. ▸ finished
  rw [← same]
  exact completed_config_audited_value_le disclose last
    (completed_response_rounds_config disclose (action.getD ⟨none⟩)
      (fun _ => app.silentPolicy) 4 last continued) sample deposit nonnegative

end Vegas.LateResolutionService

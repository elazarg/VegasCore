/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit
import Vegas.Examples.LateOpeningRuntimeOptionalInformation
import Vegas.Examples.LateOpeningRuntimeBobInformation
import Vegas.Examples.LateOpeningRuntimeBobRationality
import Interaction.ReactiveRawRoundTrace

/-! # Full continuation comparisons after successful Bob binding

The original assessment, complete compatible history fiber and every future
policy remain unchanged. Successful binding rules out the deterministic public
omission surcharge, so sampled and scaled full-audit expected payoffs agree.
This does not identify their realized settlement lotteries.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAllOrNonePostBinding
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService
open LateOpeningRuntimeAllOrNoneTrafficAudit

theorem finish_successful_binding_payoff
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace (some control))
    (active : control.actor = some bob) (answer : Answer)
    (bound : control.execution.application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (players : Player → app.Policy) (final : app.ProtocolState)
    (reached : final ∈ (app.finish initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight weightNonnegative)
        players (some control)).support)
    (reward forfeit : ℝ) (deposit : Player → ℝ) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit final bob =
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) final bob := by
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke] at reached
  obtain ⟨last, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨responded, responseSupported, later⟩ := Set.mem_iUnion₂.mp
    (PMF.support_bind .. ▸ supported)
  obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ responseSupported
  have controlEq : control = ⟨control.remaining, some bob, control.execution⟩ := by
    cases control
    simp_all
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight weightNonnegative) control.remaining
    control.execution bob response (by simpa only [← controlEq] using trace)
  have unchanged := (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    control.execution bob response).1
  exact successful_binding_continuation_payoff probability nonnegative bounded weight
    weightNonnegative ⟨control.remaining, none, control.execution.respond app bob response⟩
    respondedTrace answer (by simpa only [unchanged] using bound) players control.remaining
    last later reward forfeit deposit bob

theorem post_binding_context_value
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (boundFiber : ∀ history : InformationModel.InformationHistory
        (LateOpeningRuntimeGame.model weight weightNonnegative) bob site.1,
      ∃ control : app.Control,
      history.1.state = some control ∧ control.actor = some bob ∧
        Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace (some control)) ∧
        ∃ answer : Answer, control.execution.application.config.store (.inr bobBindEvent) =
          some (.success answer))
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralPolicy bob) :
    (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
      (sample probability nonnegative bounded) deposit assessment).value alternative =
    (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
      (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
      assessment).value alternative := by
  unfold LateOpeningRuntimeBobRationality.context
    InformationModel.BehavioralAssessment.truncatedContinuationContext
    InformationModel.BehavioralAssessment.continuationContextWith Context.value
    GameTheory.Protocol.Context.ofBelief InformationModel.truncatedRunner
  apply expect_congr_on_support
  intro final supported
  obtain ⟨history, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨control, stateEq, active, ⟨trace⟩, answer, bound⟩ := boundFiber history
  have mapped : final.state ∈
      (((LateOpeningRuntimeGame.model weight weightNonnegative).runBehavioralFrom (Profile.update
        (sig := (LateOpeningRuntimeGame.model weight weightNonnegative).behavioralSignature)
        assessment.strategy bob alternative)
        (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state).support :=
    by rw [PMF.support_map]; exact ⟨final, reached, rfl⟩
  rw [rawMenu.run_eq_finish initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight weightNonnegative)
    (Profile.update
      (sig := (LateOpeningRuntimeGame.model weight weightNonnegative).behavioralSignature)
      assessment.strategy bob alternative)
    (2 * LateOpeningRuntimeService.horizon + 1) history.1 (by
      rw [stateEq]
      have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight weightNonnegative) trace
      simp only [ReactiveApplication.rank, active, Option.isSome_some, ↓reduceIte]
      omega), stateEq] at mapped
  exact finish_successful_binding_payoff probability nonnegative bounded weight
    weightNonnegative control trace active answer bound _ final.state mapped reward forfeit deposit

theorem post_binding_context_rationality_iff
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (boundFiber : ∀ history : InformationModel.InformationHistory
        (LateOpeningRuntimeGame.model weight weightNonnegative) bob site.1,
      ∃ control : app.Control,
      history.1.state = some control ∧ control.actor = some bob ∧
        Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace (some control)) ∧
        ∃ answer : Answer, control.execution.application.config.store (.inr bobBindEvent) =
          some (.success answer))
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment) :
    assessment.IsSequentiallyRationalAt site
      (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
        (sample probability nonnegative bounded) deposit assessment) ↔
      assessment.IsSequentiallyRationalAt site
        (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
          assessment) := by
  have integrable (sampling) (collateral : Player → ℝ) (choice) :
      (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
        sampling collateral assessment).IntegrableAt choice :=
    payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit sampling collateral history.state
  unfold InformationModel.BehavioralAssessment.IsSequentiallyRationalAt
  rw [Context.isLocallyOptimal_iff_of_integrable
    (integrable _ _ _) (fun choice _ => integrable _ _ choice),
    Context.isLocallyOptimal_iff_of_integrable
      (integrable _ _ _) (fun choice _ => integrable _ _ choice)]
  simp_rw [post_binding_context_value probability nonnegative bounded weight weightNonnegative
    site boundFiber reward forfeit deposit assessment]

private theorem optional_bound_fiber
    (weight : ℝ) (nonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      bob site.1)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨12, some bob, execution⟩))
    (current : representative.1.state = some ⟨12, some bob, execution⟩)
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (history : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory bob site.1) :
    ∃ control : app.Control, history.1.state = some control ∧ control.actor = some bob ∧
      Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control)) ∧
      ∃ value : Answer, control.execution.application.config.store (.inr bobBindEvent) =
        some (.success value) := by
  obtain ⟨actual, stateEq, actualTrace, _, sameView⟩ :=
    LateOpeningRuntimeOptionalInformation.optional_history_same_information weight nonnegative
      site representative execution trace current history
  refine ⟨⟨12, some bob, actual⟩, stateEq, rfl, actualTrace, answer, ?_⟩
  rw [← LateOpeningRuntimeBobInformation.bound_same_view execution actual sameView]
  exact bound

private theorem final_bound_fiber
    (weight : ℝ) (nonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      bob site.1)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨6, some bob, execution⟩))
    (current : representative.1.state = some ⟨6, some bob, execution⟩)
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (history : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory bob site.1) :
    ∃ control : app.Control, history.1.state = some control ∧ control.actor = some bob ∧
      Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control)) ∧
      ∃ value : Answer, control.execution.application.config.store (.inr bobBindEvent) =
        some (.success value) := by
  obtain ⟨actual, stateEq, actualTrace, _, sameView⟩ :=
    LateOpeningRuntimeBobInformation.final_history_same_information weight nonnegative
      site representative execution trace current history
  refine ⟨⟨6, some bob, actual⟩, stateEq, rfl, actualTrace, answer, ?_⟩
  rw [← LateOpeningRuntimeBobInformation.bound_same_view execution actual sameView]
  exact bound

section OptionalCallback
variable (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
  (weight : ℝ) (weightNonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace
    (some ⟨12, some bob, execution⟩))
  (current : representative.1.state = some ⟨12, some bob, execution⟩)
  (answer : Answer)
  (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)

include representative trace current answer bound in
theorem optional_binding_context_value
    (alternative : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralPolicy bob) :
    (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
      (sample probability nonnegative bounded) deposit assessment).value alternative =
    (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
      (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
      assessment).value alternative :=
  post_binding_context_value probability nonnegative bounded weight weightNonnegative site
    (optional_bound_fiber weight weightNonnegative site representative execution trace current
      answer bound) reward forfeit deposit assessment alternative

include representative trace current answer bound in
theorem optional_binding_rationality_iff :
    assessment.IsSequentiallyRationalAt site
      (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
        (sample probability nonnegative bounded) deposit assessment) ↔
      assessment.IsSequentiallyRationalAt site
        (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
          assessment) :=
  post_binding_context_rationality_iff probability nonnegative bounded weight weightNonnegative
    site (optional_bound_fiber weight weightNonnegative site representative execution trace current
      answer bound) reward forfeit deposit assessment
end OptionalCallback

section FinalCallback
variable (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
  (weight : ℝ) (weightNonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace
    (some ⟨6, some bob, execution⟩))
  (current : representative.1.state = some ⟨6, some bob, execution⟩)
  (answer : Answer)
  (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)

include representative trace current answer bound in
theorem final_binding_context_value
    (alternative : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralPolicy bob) :
    (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
      (sample probability nonnegative bounded) deposit assessment).value alternative =
    (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
      (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
      assessment).value alternative :=
  post_binding_context_value probability nonnegative bounded weight weightNonnegative site
    (final_bound_fiber weight weightNonnegative site representative execution trace current
      answer bound) reward forfeit deposit assessment alternative

include representative trace current answer bound in
theorem final_binding_rationality_iff :
    assessment.IsSequentiallyRationalAt site
      (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
        (sample probability nonnegative bounded) deposit assessment) ↔
      assessment.IsSequentiallyRationalAt site
        (LateOpeningRuntimeBobRationality.context weight weightNonnegative site reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
          assessment) :=
  post_binding_context_rationality_iff probability nonnegative bounded weight weightNonnegative
    site (final_bound_fiber weight weightNonnegative site representative execution trace current
      answer bound) reward forfeit deposit assessment
end FinalCallback

end Vegas.Examples.LateOpeningRuntimeAllOrNonePostBinding

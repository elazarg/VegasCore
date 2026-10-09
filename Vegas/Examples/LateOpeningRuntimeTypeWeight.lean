/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood
import Vegas.Examples.LateOpeningRuntimeSourceBeliefs
import Interaction.ReactiveHorizonContinuation

/-! # Positive initialized weights under native full mixing

Every initialized bit and private label has positive prior probability. The
actual protected sender activation admits silence, so a fully mixed native
assessment assigns positive probability to that response. Their product is
the initialized type weight used by the complete information-group formulas.
The result gives no uniform lower bound along a consistency sequence.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeTypeWeight

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeInitializedPrefix LateOpeningRuntimeFirstRetryComparison
  LateOpeningRuntimeInitializedTypeLikelihood

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem prior_probability_positive (bit : Bool) (label : Fin 3) :
    0 < (prior (bit, label)).toReal := by
  apply ENNReal.toReal_pos
  · rw [prior_apply]
    exact mul_ne_zero (bitLaw_ne_zero bit) (by norm_num)
  · exact prior.apply_ne_top _

/-- Every initialized type has a legal bounded raw history at its actual
protected sender decision, independently of every player policy. -/
theorem protected_decision_trace (bit : Bool) (label : Fin 3) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨25, some alice, protectedDecision bit label⟩)) := by
  obtain ⟨initialTrace⟩ := rawMenu.trace_initial initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (initialPhysical bit label)
      (initialPhysical_supported bit label)
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 25 (initialExecution bit label)
      (protectedDecision bit label) (.activate alice) initialTrace
  · exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [recorded_activation _ alice (by rfl)]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- Silence has positive physical mass at each actual protected decision
under full mixing of the native behavioral strategy. -/
theorem protected_silence_supported
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (bit : Bool) (label : Fin 3) :
    (⟨none⟩ : app.Action) ∈
      (players weight nonnegative assessment.strategy alice
        ((protectedDecision bit label).recall alice)
        ((protectedDecision bit label).observe app alice)).support := by
  classical
  obtain ⟨trace⟩ := protected_decision_trace weight nonnegative bit label
  have covered : ∀ who, rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who
        (players weight nonnegative assessment.strategy who) := by
    intro who control actual active response selected
    exact rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who)
        _ _ response selected
  have restricted : assessment.strategy = fun who =>
      rawMenu.restrictPolicy initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) who
          (players weight nonnegative assessment.strategy who) := by
    funext who
    exact (rawMenu.restrict_decode_embedPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who)).symm
  apply rawMenu.fullyMixed_response_support initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (players weight nonnegative assessment.strategy) covered assessment restricted mixed
        alice 25 (protectedDecision bit label) trace ⟨none⟩
  change (⟨none⟩ : app.Action) ∈
    (ReactiveApplication.ResponseMenu.fromSubmissions _).actions _ _ _
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  trivial

theorem typeWeight_positive
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (bit : Bool) (label : Fin 3) :
    0 < typeWeight weight nonnegative assessment.strategy bit label := by
  unfold typeWeight
  apply mul_pos (prior_probability_positive bit label)
  apply ENNReal.toReal_pos
  · exact (PMF.mem_support_iff _ _).mp
      (protected_silence_supported weight nonnegative assessment mixed bit label)
  · exact PMF.apply_ne_top _ _

/-- The same positivity holds at every term of any supplied common fully
mixed witness, even when the weights converge to zero. -/
theorem witness_typeWeight_positive
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed) (n : ℕ) (bit : Bool) (label : Fin 3) :
    0 < typeWeight weight nonnegative (sequence n).strategy bit label :=
  typeWeight_positive weight nonnegative (sequence n) (mixed n) bit label

end Vegas.Examples.LateOpeningRuntimeTypeWeight

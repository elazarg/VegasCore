/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding
import Vegas.Examples.LateOpeningRuntimeAllOrNoneCleanBinding
import Vegas.Examples.LateOpeningRuntimeAllOrNoneDirtyFailedBinding
import Vegas.Examples.LateOpeningRuntimeAllOrNonePostBinding
import Vegas.Examples.LateOpeningRuntimeContinuationRationality

/-! # Actual receiver continuation rationality under sampled traffic audit

Live binding callbacks are classified by the actual stored Alice publication
and the receiver's complete earlier recall. Already-bound callbacks use exact
continuation payoff equality. The original assessment and opponents are retained.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open LateOpeningRuntimeSource LateOpeningRuntimeService
  LateOpeningRuntimeAllOrNoneTrafficAudit LateOpeningRuntimeAllOrNoneBinding
  LateOpeningRuntimeAllOrNoneCleanBinding LateOpeningRuntimeAllOrNoneDirtyFailedBinding
  LateOpeningRuntimeAllOrNonePostBinding LateOpeningRuntimeContinuationRationality

theorem receiver_continuations_rational
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (rational : ReceiverContinuationsRational weight weightNonnegative assessment
      (LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability nonnegative bounded) deposit)) :
    ReceiverContinuationsRational weight weightNonnegative assessment
      (LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner)) := by
  classical
  intro site representative control current actor live
  have localRational := rational site representative control current actor live
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight weightNonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight weightNonnegative))] at localRational ⊢
  rcases control with ⟨remaining, observedActor, execution⟩
  dsimp only at actor live current
  subst observedActor
  rcases live with ⟨remainingEq, ready, timely⟩ | ⟨remainingEq, answer, bound⟩
  · subst remaining
    have trace := current ▸ representative.1.trace
    have rawTrace := rawMenu.toRawTrace _ _ _ trace
    have available : (execution.application.config.store (.inr aliceEvent)).isSome := by
      rw [Config.store_output, execution.application.config.output_available]
      exact ready.2 (by decide)
    obtain ⟨publication, stored⟩ := Option.isSome_iff_exists.mp available
    cases publication with
    | failure =>
        by_cases quiet : LateOpeningRuntimeBobBindingService.SilentRecall execution
        · let decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory
              weight weightNonnegative :=
            ⟨execution, rawTrace, quiet, stored, ready, timely⟩
          exact failed_binding_rationality_scaled probability nonnegative bounded weight
            weightNonnegative site representative decision current reward forfeit deposit
              forfeitNonnegative collateral assessment localRational
        · exact dirty_failed_binding_rationality_scaled weight weightNonnegative site
            representative execution trace ready current timely quiet stored reward forfeit
              deposit probability nonnegative bounded forfeitNonnegative collateral assessment
                localRational
    | success bit =>
        by_cases quiet : LateOpeningRuntimeBobBindingService.SilentRecall execution
        · let decision : LateOpeningRuntimeBobSuccessInformation.DecisionHistory
              weight weightNonnegative :=
            ⟨execution, rawTrace, quiet, bit, stored, ready, timely⟩
          exact clean_binding_rationality_scaled probability nonnegative bounded weight
            weightNonnegative site representative decision current reward forfeit deposit
              forfeitNonnegative collateral assessment localRational
        · exact dirty_binding_rationality_scaled weight weightNonnegative site representative
            execution trace ready current reward forfeit deposit probability nonnegative bounded
              timely quiet bit stored forfeitNonnegative collateral assessment localRational
  · have trace := rawMenu.toRawTrace _ _ _ (current ▸ representative.1.trace)
    rcases remainingEq with remainingEq | remainingEq <;> subst remaining
    · exact (optional_binding_rationality_iff probability nonnegative bounded weight
        weightNonnegative site representative execution trace current answer bound reward forfeit
          deposit assessment).mp localRational
    · exact (final_binding_rationality_iff probability nonnegative bounded weight
        weightNonnegative site representative execution trace current answer bound reward forfeit
          deposit assessment).mp localRational

end Vegas.Examples.LateOpeningRuntimeAllOrNoneRationality

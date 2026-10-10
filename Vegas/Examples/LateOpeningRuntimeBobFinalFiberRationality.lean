/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobFinalObservation

/-! # Final native publication on every compatible hidden history

The final owner-readout law is common to the complete information class.
Sequential rationality therefore forces successful publication on all its
hidden histories, including those with zero assessment belief. Earlier
cleanliness, readiness and timeliness remain actual representative premises.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobFinalFiberRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobService LateOpeningRuntimeBobIncentive LateOpeningRuntimeBobInformation
  LateOpeningRuntimeBobRationality LateOpeningRuntimeBobFinalObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨6, some bob, decision.execution⟩)

private def answerView (view : PlayerView nativeGraph) : Option (PublicationResult Answer) :=
  view.observation.store (.inr bobRevealEvent)

private theorem answerView_physical (physical : app.State) :
    answerView (physical.playerView bob) = physical.config.store (.inr bobRevealEvent) := by
  exact nativeGraph.playerStore_of_visible bob physical.config.store (.inr bobRevealEvent)
    (by decide)

theorem continuation_answer_same_information
    (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (response : app.Action) (firstPlayers secondPlayers : Player → app.Policy) :
    (continuation weight nonnegative first response firstPlayers).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) =
    (continuation weight nonnegative second response secondPlayers).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) := by
  have observed := continuation_owner_same_information weight nonnegative
    first.execution second.execution first.trace second.trace sameRecall
    sameView response firstPlayers secondPlayers
  have readout := congrArg (PMF.map answerView) observed
  simpa only [continuation, PMF.map_comp, Function.comp_def, answerView_physical] using readout

def responseContinuationLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : DecisionHistory weight nonnegative) (players : Player → app.Policy) :
    PMF app.Execution :=
  ((assessment.strategy bob site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
    continuation weight nonnegative history response players

theorem finalLaw_answer_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (players : Player → app.Policy) :
    (finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).map
        (fun final => final.application.config.store (.inr bobRevealEvent)) =
    (responseContinuationLaw weight nonnegative site assessment decision players).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) := by
  unfold finalLaw
  rw [PMF.map_bind]
  calc
    _ = (assessment.belief bob site).bind (fun _ =>
        (responseContinuationLaw weight nonnegative site assessment decision players).map
          (fun final => final.application.config.store (.inr bobRevealEvent))) := by
      apply bind_congr_on_support _
      intro history _
      dsimp only [responseContinuationLaw]
      rw [PMF.map_bind, PMF.map_bind]
      apply bind_congr_on_support _
      intro response _
      have compatible := decisionOfInformation_spec weight nonnegative site representative
        decision current history
      exact continuation_answer_same_information weight nonnegative _ decision
        compatible.2.1.symm compatible.2.2.symm response _ players
    _ = _ := PMF.bind_const _ _

private theorem failure_probability_same (first second : PMF app.Execution)
    (same : first.map (fun final => final.application.config.store (.inr bobRevealEvent)) =
      second.map (fun final => final.application.config.store (.inr bobRevealEvent))) :
    (first.toOuterMeasure
      {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
    (second.toOuterMeasure
      {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal := by
  have mapped := congrArg (fun law : PMF (Option (PublicationResult Answer)) =>
    (law.toOuterMeasure {result | result = some .failure}).toReal) same
  simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using mapped

variable (reward forfeit : ℝ)
  (sample : List (SettledEvidence setup .sequential) →
    PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)

theorem rational_every_history_failure_zero
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit sample deposit assessment))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (players : Player → app.Policy) :
    ((responseContinuationLaw weight nonnegative site assessment
      (decisionOfInformation weight nonnegative site representative decision current history)
      players).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
          0 := by
  have assessed := rational_final_failure_zero weight nonnegative site representative decision
    current reward forfeit sample deposit forfeitPositive authentic depositNonnegative
      assessment rational
  have common := finalLaw_answer_law weight nonnegative site representative decision current
    assessment players
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  have fixed : (responseContinuationLaw weight nonnegative site assessment decision players).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) =
    (responseContinuationLaw weight nonnegative site assessment
      (decisionOfInformation weight nonnegative site representative decision current history)
      players).map (fun final => final.application.config.store (.inr bobRevealEvent)) := by
    unfold responseContinuationLaw
    rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro response _
    exact continuation_answer_same_information weight nonnegative _ _ compatible.2.1
      compatible.2.2 response players players
  exact (failure_probability_same _ _ (common.trans fixed)).symm.trans assessed

theorem rational_supported_publication
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit sample deposit assessment))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) := by
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  have zero := rational_every_history_failure_zero weight nonnegative site representative decision
    current reward forfeit sample deposit forfeitPositive authentic depositNonnegative assessment
      rational history players
  have finalSupported : final ∈
      (responseContinuationLaw weight nonnegative site assessment recovered players).support := by
    rw [responseContinuationLaw, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨response, supported, reached⟩
  have probabilityZero : (responseContinuationLaw weight nonnegative site assessment recovered
      players).toOuterMeasure
      {last | last.application.config.store (.inr bobRevealEvent) = some .failure} = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp zero |>.resolve_right
      (outerMeasure_ne_top _ _)
  have noFailure : final.application.config.store (.inr bobRevealEvent) ≠ some .failure := by
    intro failure
    exact ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mp probabilityZero).le_bot
      ⟨finalSupported, failure⟩
  obtain ⟨trace⟩ := continuation_trace weight nonnegative recovered response players final reached
  have complete := (contract weight nonnegative).completes ⟨0, none, final⟩ trace ⟨rfl, rfl⟩
  obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobRevealEvent))
  cases result with
  | failure => exact (noFailure stored).elim
  | success opened =>
      obtain ⟨bit, label, invariant⟩ := history_initial_invariant
        LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)
          ⟨6, some bob, recovered.execution⟩ recovered.trace
      have same := bob_continuation_success_immutable LateOpeningRuntimeService.runtime leaks
        players (LateOpeningRuntimeService.scheduler weight nonnegative) 6 recovered.execution final
          _ invariant recovered.answer recovered.bound response reached opened stored
      have sameAnswer : recovered.answer = decision.answer := by
        have compatible := decisionOfInformation_spec weight nonnegative site representative
          decision current history
        have boundEq := bound_same_view decision.execution recovered.execution compatible.2.2
        rw [decision.bound, recovered.bound] at boundEq
        exact PublicationResult.success.inj (Option.some.inj boundEq.symm)
      rw [same, sameAnswer] at stored
      exact stored

/-- Whole-game sequential rationality publishes on every legal hidden history
of a clean final site, whether or not its assessment belief is positive there. -/
theorem sequentially_rational_supported_publication
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history =>
        LateOpeningRuntimeNash.payoff reward forfeit sample deposit history.state who))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) := by
  apply rational_supported_publication weight nonnegative site representative decision current
    reward forfeit sample deposit forfeitPositive authentic depositNonnegative assessment _
      history response supported players final reached
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

/-- The same full-information publication law holds in each existing native
sequential equilibrium; consistency is not needed for this local implication. -/
theorem equilibrium_supported_publication
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history =>
        LateOpeningRuntimeNash.payoff reward forfeit sample deposit history.state who))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) :=
  sequentially_rational_supported_publication weight nonnegative site representative decision
    current reward forfeit sample deposit forfeitPositive authentic depositNonnegative assessment
      equilibrium.1 history response supported players final reached

end Vegas.Examples.LateOpeningRuntimeBobFinalFiberRationality

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalContext
import Vegas.Examples.LateOpeningRuntimeBobSunkDisclosure

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalRationality
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService
  LateOpeningRuntimeOptionalInformation LateOpeningRuntimeBobDirtyOptionalContext
  LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobBindingDecision (context context_integrable answerPlayers)
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (executionTrace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
    (some ⟨12, some bob, execution⟩))
  (current : representative.1.state = some ⟨12, some bob, execution⟩)
  (answer : Answer)
  (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
  (ready : execution.application.config.cut.Ready bobRevealEvent)
  (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
  (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

include ready in
theorem canonical_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) =
    expect (canonicalFinalLaw weight nonnegative site representative execution
      executionTrace current
      answer assessment) (fun final => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) bob) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative answer))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [canonical_context_outcome_law weight nonnegative site representative execution executionTrace
    current answer ready, expect_map] at mapped
  exact mapped.symm

theorem incumbent_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (incumbentFinalLaw weight nonnegative site representative execution
      executionTrace current
      assessment) (fun final => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) bob) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [incumbent_context_outcome_law weight nonnegative site representative execution executionTrace
    current, expect_map] at mapped
  exact mapped.symm

include bound ready timely rejected in
theorem optional_failure_regret (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    forfeit * ((incumbentFinalLaw weight nonnegative site representative execution executionTrace
      current assessment).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal ≤
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) -
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) := by
  classical
  let recover := executionOfInformation weight nonnegative site representative execution
    executionTrace current
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  let raw := fun history => (app.invoke players bob (recover history)).bind
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 12)
  let comparator := fun history =>
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (answerPlayers weight nonnegative assessment answer) 12
      ((recover history).respond app bob
        (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
          ((recover history).recall bob) ((recover history).observe app bob) bobRevealEvent true))
  let payoff := fun final => LateOpeningRuntimeNash.payoff reward forfeit
    (fun actual => PMF.pure actual) deposit (app.finished final) bob
  have integrable (law : PMF app.Execution) : PayoffIntegrable law payoff :=
    payoffIntegrable_of_bounded _ _ fun final => LateOpeningRuntimeBobIncentive.payoff_bounded
      reward forfeit (fun actual => PMF.pure actual) deposit (app.finished final)
  have regret := expect_failure_regret (assessment.belief bob site) raw comparator payoff payoff
    {final | final.application.config.store (.inr bobRevealEvent) = some .failure} forfeit
    (integrable _) (integrable _) (fun _ _ => integrable _) (fun _ _ => integrable _) (by
      intro history _ final reached canonicalFinal canonicalReached
      obtain ⟨responded, responseSupported, continued⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      change responded ∈ ((players bob ((recover history).recall bob)
        ((recover history).observe app bob)).map
          (fun response => (recover history).respond app bob response)).support at responseSupported
      obtain ⟨response, _, responseEq⟩ := (PMF.mem_support_map_iff _ _ _).mp responseSupported
      subst responded
      have valid := executionOfInformation_spec weight nonnegative site representative execution
        executionTrace current history
      obtain ⟨rawTrace⟩ := valid.2.1
      have sameView := valid.2.2.2
      have actualBound := (LateOpeningRuntimeBobInformation.bound_same_view _ _ sameView).symm.trans
        bound
      have actualReady := LateOpeningRuntimeBobInformation.ready_same_view _ _ sameView ready
      have actualTimely := LateOpeningRuntimeBobInformation.timely_same_view _ _ sameView timely
      have sameReceipts := congrArg ReactiveApplication.PlayerView.receipts sameView
      change execution.receipts = (recover history).receipts at sameReceipts
      have actualRejected := sameReceipts ▸ rejected
      have comparison := LateOpeningRuntimeBobSunkDisclosure.canonical_dominates weight nonnegative
        11 (recover history) rawTrace answer actualBound actualReady actualTimely serial
          actualRejected
        reward forfeit forfeitNonnegative deposit response players _ final canonicalFinal continued
          canonicalReached
      simp only [Set.mem_ofPred_eq]
      by_cases failed : final.application.config.store (.inr bobRevealEvent) = some .failure
      · simpa only [failed, ite_true, mul_one, payoff] using comparison.2 failed
      · simpa only [failed, ite_false, mul_zero, add_zero, payoff] using comparison.1)
  rw [canonical_context_value weight nonnegative site representative execution
    executionTrace current
    answer ready, incumbent_context_value weight nonnegative site representative execution
    executionTrace current]
  exact regret

include bound ready timely rejected in
theorem rational_optional_failure_zero (forfeitPositive : 0 < forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ((incumbentFinalLaw weight nonnegative site representative execution executionTrace current
      assessment).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
      0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
        (answerFinitePolicy weight nonnegative answer) (Set.mem_univ _)
  have regret := optional_failure_regret weight nonnegative site representative execution
    executionTrace current answer bound ready timely serial rejected reward forfeit deposit
    forfeitPositive.le assessment
  have nonnegative := ENNReal.toReal_nonneg (a :=
    ((incumbentFinalLaw weight nonnegative site representative execution executionTrace current
      assessment).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}))
  nlinarith
end Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalRationality

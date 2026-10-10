/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyFinalIncentive
import Vegas.Examples.LateOpeningRuntimeBobDirtyFinalContext

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobDirtyFinalRationality
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService
  LateOpeningRuntimeBobInformation LateOpeningRuntimeBobDirtyFinalContext

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (executionTrace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨6, some bob, execution⟩))
  (current : representative.1.state = some ⟨6, some bob, execution⟩)

/-- The admissible whole-policy disclosure deviation uses the same complete receiver
information at every compatible final history. -/
private theorem opening_finalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    finalLaw weight nonnegative site representative execution executionTrace current assessment
      (openingPolicy weight nonnegative site representative execution current
        assessment) =
    (assessment.belief bob site).bind fun history =>
      let actual := executionOfInformation weight nonnegative site representative execution
        executionTrace current history
      app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (fun _ => app.silentPolicy) 6 (actual.respond app bob
          (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob (actual.recall bob)
            (actual.observe app bob) bobRevealEvent true)) := by
  classical
  unfold finalLaw openingPolicy
  rw [InformationModel.BehavioralPolicy.commit_self, PMF.pure_map]
  apply bind_congr_on_support _
  intro history _
  rw [PMF.pure_bind]
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    executionTrace current history
  change app.runRounds _ _ 6
    ((executionOfInformation weight nonnegative site representative execution
      executionTrace current history).respond app bob
    (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob (execution.recall bob)
      (execution.observe app bob) bobRevealEvent true)) = _
  rw [valid.2.2.1, valid.2.2.2]

variable (answer : Answer)
  (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
  (ready : execution.application.config.cut.Ready bobRevealEvent)
  (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
  (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

include bound ready timely rejected in
/-- With an earlier rejected envelope already charged, withholding disclosure loses
at least the forfeit in the actual full-evidence continuation context. -/
theorem final_failure_regret (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    forfeit * ((finalLaw weight nonnegative site representative execution executionTrace current
      assessment (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal ≤
    (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
      (fun actual => PMF.pure actual) deposit assessment).value
      (openingPolicy weight nonnegative site representative execution current
        assessment) -
    (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
      (fun actual => PMF.pure actual) deposit assessment).value (assessment.strategy bob) := by
  classical
  let recover := executionOfInformation weight nonnegative site representative execution
    executionTrace current
  let raw := fun history =>
    ((assessment.strategy bob site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
      app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (fun _ => app.silentPolicy) 6 ((recover history).respond app bob response)
  let comparator := fun history =>
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (fun _ => app.silentPolicy) 6 ((recover history).respond app bob
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
      obtain ⟨response, _, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
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
      have comparison := LateOpeningRuntimeBobDirtyFinalIncentive.canonical_dominates
        weight nonnegative
        (recover history) rawTrace answer actualBound actualReady actualTimely serial actualRejected
        reward forfeit forfeitNonnegative deposit response _ _ final canonicalFinal continued
          canonicalReached
      simp only [Set.mem_ofPred_eq]
      by_cases failed : final.application.config.store (.inr bobRevealEvent) = some .failure
      · simpa only [failed, ite_true, mul_one, payoff] using comparison.2 failed
      · simpa only [failed, ite_false, mul_zero, add_zero, payoff] using comparison.1)
  rw [context_value weight nonnegative site representative execution executionTrace current,
    context_value weight nonnegative site representative execution executionTrace current,
    opening_finalLaw weight nonnegative site representative execution executionTrace current]
  exact regret

include bound ready timely rejected in
/-- A rational receiver discloses almost surely at an actual final information site
with an earlier rejected receipt, without requiring a nonnegative receiver deposit. -/
theorem rational_final_failure_zero (forfeitPositive : 0 < forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
        (fun actual => PMF.pure actual) deposit assessment)) :
    ((finalLaw weight nonnegative site representative execution executionTrace current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
      0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (LateOpeningRuntimeBobRationality.context_integrable weight nonnegative site reward forfeit
      (fun actual => PMF.pure actual) deposit assessment (assessment.strategy bob))
    (fun alternative _ => LateOpeningRuntimeBobRationality.context_integrable weight nonnegative
      site reward forfeit (fun actual => PMF.pure actual) deposit assessment alternative)).mp
    rational (openingPolicy weight nonnegative site representative execution current
      assessment) (Set.mem_univ _)
  have regret := final_failure_regret weight nonnegative site representative execution
    executionTrace
    current answer bound ready timely serial rejected reward forfeit deposit forfeitPositive.le
      assessment
  have nonnegative := ENNReal.toReal_nonneg (a :=
    ((finalLaw weight nonnegative site representative execution executionTrace current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}))
  nlinarith
end Vegas.Examples.LateOpeningRuntimeBobDirtyFinalRationality

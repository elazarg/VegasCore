/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff
import Vegas.Examples.LateOpeningRuntimeEarlyBobSafeMenu
import Vegas.Examples.LateOpeningRuntimeBobIncentive
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Whole native answer deviations after Alice's publication failure

Each selected answer uses a genuine policy in the complete bounded raw menu.
Its assessment-context value is the probability that its fixed bit guess
matches Alice's initialized bit. Therefore one of the two bit guesses is worth
at least one half under every belief over this actual information class.
Sampled pending contents remain part of the information. The comparison
neither fixes a posterior distribution nor hides pending packet contents.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobSafeContinuation LateOpeningRuntimeBobAnswerPayoff
  LateOpeningRuntimeEarlyBobSafeMenu

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def answerPlayers
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) : Player → app.Policy :=
  Function.update (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) bob
      (answerPolicy answer)

theorem answerPlayers_admissible
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) (who : Player) :
    rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who
      (answerPlayers weight nonnegative assessment answer who) := by
  by_cases same : who = bob
  · subst who
    simpa only [answerPlayers, Function.update_self] using
      answerPolicy_admissible weight nonnegative answer
  · intro control _trace _active response supported
    simp only [answerPlayers, Function.update_of_ne same] at supported
    exact rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who)
      _ _ response supported

theorem answerProfile_as_restriction
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
      assessment.strategy bob (answerFinitePolicy weight nonnegative answer) =
    fun who => rawMenu.restrictPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who
      (answerPlayers weight nonnegative assessment answer who) := by
  classical
  funext who
  by_cases same : who = bob
  · subst who
    simp only [Profile.update_same, answerPlayers, Function.update_self, answerFinitePolicy]
  · rw [Profile.update_of_ne _ _ same]
    simp only [answerPlayers, Function.update_of_ne same,
      ReactiveApplication.ResponseMenu.decodeProfile]
    exact (rawMenu.restrict_decode_embedPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who)).symm

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)

def answerFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) : PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (answerPlayers weight nonnegative assessment answer) 14
      ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer))

theorem answer_current_continuation_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (answer : Answer) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom
      (Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
        assessment.strategy bob (answerFinitePolicy weight nonnegative answer))
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (answerPlayers weight nonnegative assessment answer) 14
      ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer))).map
          app.finished := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  rw [answerProfile_as_restriction weight nonnegative]
  rw [rawMenu.run_restrict_eq_finish initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    (answerPlayers weight nonnegative assessment answer)
    (answerPlayers_admissible weight nonnegative assessment answer)
    _ history.1 (by rw [valid.1]; change 29 ≤ 53; decide), valid.1]
  unfold ReactiveApplication.finish ReactiveApplication.resume
  have bound := answerPolicy_binding weight nonnegative answer 14 recovered.execution
    recovered.trace recovered.quiet recovered.ready (recovered.clock weight nonnegative)
  unfold ReactiveApplication.invoke
  change (((answerPlayers weight nonnegative assessment answer bob
    (recovered.execution.recall bob) (recovered.execution.observe app bob)).map
      (fun response => recovered.execution.respond app bob response)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (answerPlayers weight nonnegative assessment answer) 14)).map app.finished = _
  simp only [answerPlayers, Function.update_self, bound, PMF.pure_map, PMF.pure_bind]
  rfl

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

def context (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit history.state bob) (2 * LateOpeningRuntimeService.horizon + 1)

theorem answer_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative answer)).map History.state =
    (answerFinalLaw weight nonnegative site representative decision current assessment answer).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, answerFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  exact answer_current_continuation_law weight nonnegative site representative decision current
    assessment history answer

theorem answer_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) =
    expect (assessment.belief bob site) fun history =>
      if answer.val = (if originalBit (decisionOfInformation weight nonnegative site
        representative decision current history).execution then 5 else 4) then 1 else 0 := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative answer))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [answer_context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  have nativeValue : (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) =
      expect (answerFinalLaw weight nonnegative site representative decision current
        assessment answer) (fun final => LateOpeningRuntimeNash.payoff reward forfeit
          (fun actual => PMF.pure actual) deposit (app.finished final) bob) := mapped.symm
  rw [nativeValue]
  unfold answerFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final))]
  apply expect_congr_on_support
  intro history _
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  calc
    _ = expect _ (fun _ => if answer.val =
        (if originalBit recovered.execution then 5 else 4) then (1 : ℝ) else 0) := by
      apply expect_congr_on_support
      intro final reached
      exact failed_answer_continuation_payoff weight nonnegative recovered answer
        (answerPlayers weight nonnegative assessment answer)
        (by simp only [answerPlayers, Function.update_self]) reward forfeit deposit
        (fun actual => PMF.pure actual)
        (by
          intro actual observed supported
          cases (PMF.mem_support_pure_iff _ _).mp supported
          exact List.Subset.refl _) final reached
    _ = _ := expect_constant _ _

/-- The two fixed bit guesses, expressed as intended answer values. -/
def bitGuess (bit : Bool) : Answer :=
  ⟨if bit then 5 else 4, by cases bit <;> decide⟩

include representative decision current in
theorem bit_guess_context_values_sum
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative (bitGuess false)) +
      (context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative (bitGuess true)) = 1 := by
  rw [answer_context_value weight nonnegative site representative decision current,
    answer_context_value weight nonnegative site representative decision current]
  rw [← expect_add (payoffIntegrable_ite_one_zero _ _) (payoffIntegrable_ite_one_zero _ _)]
  calc
    _ = expect (assessment.belief bob site) (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro history _
      cases originalBit (decisionOfInformation weight nonnegative site representative decision
        current history).execution <;> norm_num [bitGuess]
    _ = 1 := expect_constant _ _

include representative decision current in
/-- A genuine whole-policy deviation is worth at least one half at this
actual failed-publication binding class under any assessment belief. -/
theorem exists_bit_guess_value_ge_half
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ∃ bit : Bool, (1 / 2 : ℝ) ≤
      (context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative (bitGuess bit)) := by
  have total := bit_guess_context_values_sum weight nonnegative site representative decision current
    reward forfeit deposit assessment
  by_cases lower : (1 / 2 : ℝ) ≤
      (context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative (bitGuess false))
  · exact ⟨false, lower⟩
  · exact ⟨true, by linarith⟩

theorem context_integrable
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    Context.IntegrableAt
      (context weight nonnegative site reward forfeit deposit assessment) alternative :=
  payoffIntegrable_of_bounded _ _ fun history =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
      deposit history.state

include representative decision current in
/-- Sequential rationality at this native binding decision guarantees value
at least one half, regardless of its possibly off-path posterior belief. -/
theorem rational_binding_value_ge_half
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (1 / 2 : ℝ) ≤ (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) := by
  obtain ⟨bit, lower⟩ := exists_bit_guess_value_ge_half weight nonnegative site representative
    decision current reward forfeit deposit assessment
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
  exact lower.trans (comparison (answerFinitePolicy weight nonnegative (bitGuess bit))
    (Set.mem_univ _))

include representative decision current in
/-- This value bound applies to every sequential equilibrium of the actual
bounded raw runtime at a failed-Alice first-binding information class. -/
theorem equilibrium_binding_value_ge_half
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    (1 / 2 : ℝ) ≤ (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) := by
  apply rational_binding_value_ge_half weight nonnegative site representative decision current
    reward forfeit deposit assessment
  have localRational := equilibrium.1 bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

end Vegas.Examples.LateOpeningRuntimeBobBindingDecision

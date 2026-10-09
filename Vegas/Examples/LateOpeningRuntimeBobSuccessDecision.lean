/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSuccessPayoff
import Vegas.Examples.LateOpeningRuntimeBobKnownBit

/-! # Whole answer values under actual successful-publication beliefs

The same genuine answer policies give the constant Safe value and the actual
conditional label masses at a timely first binding after Alice succeeds. Every
sampled packet remains in the information class; label masses are computed
from the assessment rather than supplied as posterior hypotheses.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSuccessDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBobSafeContinuation LateOpeningRuntimeBobSuccessPayoff
  LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobBindingDecision
  (answerPlayers answerPlayers_admissible answerProfile_as_restriction context context_integrable)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

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
      answerScore (originalLabel (decisionOfInformation weight nonnegative site
        representative decision current history).execution) answer := by
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
    _ = expect _ (fun _ => answerScore (originalLabel recovered.execution) answer) := by
      apply expect_congr_on_support
      intro final reached
      exact answer_continuation_payoff weight nonnegative recovered answer
        (answerPlayers weight nonnegative assessment answer)
        (by simp only [answerPlayers, Function.update_self]) reward forfeit deposit
        (fun actual => PMF.pure actual)
        (by
          intro actual observed supported
          cases (PMF.mem_support_pure_iff _ _).mp supported
          exact List.Subset.refl _) final reached
    _ = _ := expect_constant _ _

/-- A fixed guess for one of the three private labels. -/
def labelGuess (label : Fin 3) : Answer :=
  ⟨(label.val : Int) + 1, by have := label.isLt; constructor <;> omega⟩

def labelMass
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (label : Fin 3) : ℝ :=
  expect (assessment.belief bob site) fun history =>
    if originalLabel (decisionOfInformation weight nonnegative site representative decision current
      history).execution = label then 1 else 0

include representative decision current in
theorem safe_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative safe) = 2 / 5 := by
  rw [answer_context_value weight nonnegative site representative decision current]
  simp only [answerScore, show safe.val = 0 from rfl, ↓reduceIte, expect_constant]

theorem label_guess_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (label : Fin 3) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative (labelGuess label)) =
        labelMass weight nonnegative site representative decision current assessment label := by
  rw [answer_context_value weight nonnegative site representative decision current]
  apply expect_congr_on_support
  intro history _
  let hidden := originalLabel (decisionOfInformation weight nonnegative site representative decision
    current history).execution
  have nonzero : (label.val : Int) + 1 ≠ 0 := by omega
  change (if (label.val : Int) + 1 = 0 then (2 / 5 : ℝ)
    else if (label.val : Int) + 1 = (hidden.val : Int) + 1 then 1 else 0) =
      if hidden = label then 1 else 0
  rw [ite_eq_right nonzero]
  have sameLabel : ((label.val : Int) + 1 = (hidden.val : Int) + 1) ↔ hidden = label := by
    constructor
    · intro same
      apply Fin.ext
      have values : (hidden.val : Int) = label.val := by omega
      exact_mod_cast values
    · intro same
      rw [same]
  simp only [sameLabel]

include representative decision current in
theorem answer_context_value_eq_zero_of_high
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) (high : 4 ≤ answer.val) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) = 0 := by
  rw [answer_context_value weight nonnegative site representative decision current]
  calc
    _ = expect (assessment.belief bob site) (fun _ => (0 : ℝ)) := by
      apply expect_congr_on_support
      intro history _
      have bounded := (originalLabel (decisionOfInformation weight nonnegative site representative
        decision current history).execution).isLt
      have nonzero : answer.val ≠ 0 := by omega
      have distinct : answer.val ≠
          ((originalLabel (decisionOfInformation weight nonnegative site representative decision
            current history).execution).val : Int) + 1 := by omega
      simp only [answerScore, ite_eq_right nonzero, ite_eq_right distinct]
    _ = 0 := expect_constant _ _

/-- The complete physical continuation of the incumbent native profile,
averaged over the actual assessment information class. -/
def incumbentFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  (assessment.belief bob site).bind fun history =>
    (app.invoke players bob
      (decisionOfInformation weight nonnegative site representative decision current
        history).execution).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14)

theorem incumbent_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob)).map History.state =
    (incumbentFinalLaw weight nonnegative site representative decision current assessment).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, incumbentFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  simp only [Profile.update, Function.update_eq_self]
  calc
    _ = app.finish initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
        history.1.state :=
      rawMenu.run_eq_finish initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy 53 history.1
          (by rw [valid.1]; change 29 ≤ 53; decide)
    _ = _ := by rw [valid.1]; rfl


end Vegas.Examples.LateOpeningRuntimeBobSuccessDecision

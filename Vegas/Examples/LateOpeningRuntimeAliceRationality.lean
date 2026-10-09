/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceIncentive
import Interaction.ReactivePassiveDecision
import GameTheoryExtensions.Protocol.ContinuationHorizon
import GameTheoryExtensions.Math.Probability.Regret

/-! # Sequential rationality after an actual pending opening

The complete native posterior retains arbitrary private syntax of the earlier
opening. Bob's remaining policy is unrestricted. A positive collateral margin
forces silence at Alice's remaining response, with a quantitative bound from
the value of a genuine whole-policy deviation.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeAliceContinuation
  LateOpeningRuntimeAliceDecision LateOpeningRuntimeAliceIncentive LateOpeningRuntimeUtility
  LateOpeningRuntimeReadout

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨18, some alice, decision.execution⟩)

include current in
theorem site_information : site.1 =
    some (decision.execution.recall alice, decision.execution.observe app alice) := by
  rw [← representative.2]
  change (rawMenu.signals _ _ _).infoOf alice representative.1.trace = _
  rw [rawMenu.info, current]
  rfl

/-- Silence is already a legal response in the complete bounded raw menu. -/
def quietChoice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1 := by
  classical
  refine ⟨some ⟨none⟩, ?_⟩
  rw [site_information weight nonnegative site representative decision current]
  refine ⟨⟨none⟩, ?_, rfl⟩
  exact Finset.mem_insert_self _ _

def quietPolicy
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice := by
  classical
  exact (assessment.strategy alice).commit site.1
    (quietChoice weight nonnegative site representative decision current)

def responseLaw
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    PMF app.Action := (alternative site.1).map (fun choice => choice.1.getD ⟨none⟩)

def finalLaw (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    PMF app.Execution :=
  (assessment.belief alice site).bind fun history =>
    (responseLaw weight nonnegative site alternative).bind fun response =>
      continuation weight nonnegative
        (decisionOfInformation weight nonnegative site representative decision current history)
        response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)

theorem current_continuation_law
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom profile
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
      (responseLaw weight nonnegative site (profile alice)).bind fun response =>
        (continuation weight nonnegative
          (decisionOfInformation weight nonnegative site representative decision current history)
          response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) profile)).map
              app.finished := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have last := rawMenu.run_last_response_of_unactivated initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative)
      profile history.1 18 recovered.execution valid.1 (by rw [decision_cursor])
  rw [history.2] at last
  refine last.trans ?_
  apply bind_congr_on_support _
  intro response _
  unfold continuation
  rw [app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative)
    _ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) profile)
    (by intro who different; rw [Function.update_of_ne different]) 18 _
    (by change 8 ≤ recovered.execution.environmentRecall.length; rw [decision_cursor])]

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

def context (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit history.state alice) (2 * LateOpeningRuntimeService.horizon + 1)

theorem context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome alternative).map
      History.state =
    (finalLaw weight nonnegative site representative decision current assessment alternative).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, finalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  rw [current_continuation_law weight nonnegative site representative decision current,
    PMF.map_bind, Profile.update_same]
  apply bind_congr_on_support _
  intro response _
  unfold continuation
  rw [app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative)
    _ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
    (by
      intro who different
      change app.decodePolicy _ = app.decodePolicy _
      rw [Profile.update_of_ne _ _ different]) 18 _
    (by
      change 8 ≤ (decisionOfInformation weight nonnegative site representative decision current
        history).execution.environmentRecall.length
      rw [decision_cursor])]

theorem context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    (context weight nonnegative site reward forfeit deposit assessment).value alternative =
    expect (finalLaw weight nonnegative site representative decision current assessment alternative)
      (aliceUtility reward forfeit deposit) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome alternative)
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state alice)
  rw [context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  exact mapped.symm

theorem payoff_bounded
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice) (state : app.ProtocolState) :
    |LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state alice| ≤ reward + forfeit + deposit alice := by
  have base : |nativeBaseUtility reward forfeit state alice| ≤ reward + forfeit := by
    change |(serviceSourceReadout setup .sequential deadline leaks state).elim 0
      (fun terminal => sourceUtility reward forfeit terminal alice)| ≤ _
    cases read : serviceSourceReadout setup .sequential deadline leaks state with
    | none => simp only [Option.elim_none, abs_zero]; positivity
    | some terminal =>
        simp only [Option.elim_some]
        obtain ⟨lower, upper⟩ := sourceUtility_alice_bounds rewardNonnegative
          forfeitNonnegative terminal
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  have charged := GameTheory.Enforcement.TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      state alice
  unfold LateOpeningRuntimeNash.payoff GameTheory.Enforcement.TerminalAudit.utility
  calc
    _ ≤ |nativeBaseUtility reward forfeit state alice| +
        |GameTheory.Enforcement.TerminalAudit.charge
          (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
            state alice * deposit alice| := abs_sub _ _
    _ ≤ reward + forfeit + deposit alice := by
      rw [abs_mul, abs_of_nonneg charged.1, abs_of_nonneg depositNonnegative]
      nlinarith [charged.2]

theorem context_integrable
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    Context.IntegrableAt
      (context weight nonnegative site reward forfeit deposit assessment) alternative :=
  payoffIntegrable_of_bounded _ _ fun history =>
    payoff_bounded reward forfeit deposit rewardNonnegative forfeitNonnegative
      depositNonnegative history.state

theorem quiet_finalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    finalLaw weight nonnegative site representative decision current assessment
      (quietPolicy weight nonnegative site representative decision current assessment) =
    (assessment.belief alice site).bind fun history =>
      continuation weight nonnegative
        (decisionOfInformation weight nonnegative site representative decision current history)
        ⟨none⟩ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) := by
  classical
  unfold finalLaw responseLaw quietPolicy
  rw [InformationModel.BehavioralPolicy.commit_self, PMF.pure_map]
  simp only [quietChoice, Option.getD_some, PMF.pure_bind]

def margin : ℝ := deposit alice - reward -
  (1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) * (forfeit + deposit alice)

/-- The actual whole-policy deviation gains the collateral margin times the
probability of a second raw envelope, under the assessment's own posterior. -/
theorem quiet_regret
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    margin weight reward forfeit deposit *
        ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
          {response | response.transmission.isSome}).toReal ≤
      (context weight nonnegative site reward forfeit deposit assessment).value
        (quietPolicy weight nonnegative site representative decision current assessment) -
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy alice) := by
  classical
  let belief := assessment.belief alice site
  let actions := responseLaw weight nonnegative site (assessment.strategy alice)
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  let recover := decisionOfInformation weight nonnegative site representative decision current
  let utility := aliceUtility reward forfeit deposit
  let row := fun pair :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1 ×
        app.Action => expect
    (continuation weight nonnegative (recover pair.1) pair.2 players) utility
  let quiet := fun history => expect
    (continuation weight nonnegative (recover history) ⟨none⟩ players) utility
  let joint := belief.bind fun history => actions.map fun response => (history, response)
  have constantNonnegative : 0 ≤ reward + forfeit + deposit alice := by positivity
  have bound : ∀ final, |utility final| ≤ reward + forfeit + deposit alice := by
    intro final
    obtain ⟨lower, upper⟩ := aliceUtility_bounds rewardNonnegative forfeitNonnegative
      deposit depositNonnegative final
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have rowBound : ∀ pair, |row pair| ≤ reward + forfeit + deposit alice := by
    intro pair
    exact expect_abs_le_of_bounded constantNonnegative bound
  have quietBound : ∀ history, |quiet history| ≤ reward + forfeit + deposit alice := by
    intro history
    exact expect_abs_le_of_bounded constantNonnegative bound
  have regret := expect_failure_regret belief
    (fun history => actions.map fun response => (history, response)) PMF.pure row quiet
      {pair | pair.2.transmission.isSome} (margin weight reward forfeit deposit)
      (payoffIntegrable_of_bounded _ _ rowBound)
      (payoffIntegrable_of_bounded _ _ quietBound)
      (fun _ _ => payoffIntegrable_of_bounded _ _ rowBound)
      (fun _ _ => payoffIntegrable_of_bounded _ _ quietBound) (by
        intro history _ first firstReached second secondReached
        rw [PMF.mem_support_map_iff] at firstReached
        obtain ⟨response, _, rfl⟩ := firstReached
        rw [PMF.mem_support_pure_iff] at secondReached
        subst second
        rcases response with ⟨transmission⟩
        cases transmission with
        | none => simp [row, quiet]
        | some submission =>
            have comparison := quiet_second_packet_regret weight nonnegative positive
              (recover history) submission players players rewardNonnegative
                forfeitNonnegative deposit depositNonnegative
            rw [quietLaw_eq_continuation, secondLaw_eq_continuation] at comparison
            have converted : row (history, ⟨some submission⟩) +
                margin weight reward forfeit deposit ≤ quiet history := by
              change expect (continuation weight nonnegative (recover history)
                ⟨some submission⟩ players) utility + _ ≤ _
              dsimp only [margin]
              linarith [comparison]
            simpa using converted)
  have marginal : joint.map Prod.snd = actions := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
    change actions.map id = actions
    exact PMF.map_id actions
  have mass : (joint.toOuterMeasure {pair | pair.2.transmission.isSome}).toReal =
      (actions.toOuterMeasure {response | response.transmission.isSome}).toReal := by
    rw [← marginal, PMF.toOuterMeasure_map_apply]
    rfl
  have rawMean : expect joint row = expect
      (finalLaw weight nonnegative site representative decision current assessment
        (assessment.strategy alice)) utility := by
    rw [expect_bind_tower_bounded belief _ _ rowBound]
    unfold finalLaw
    rw [expect_bind_tower_bounded _ _ _ bound]
    apply expect_congr_on_support
    intro history _
    rw [expect_map, expect_bind_tower_bounded _ _ _ bound]
    rfl
  have quietMean : expect (belief.bind PMF.pure) quiet = expect
      (finalLaw weight nonnegative site representative decision current assessment
        (quietPolicy weight nonnegative site representative decision current assessment))
        utility := by
    rw [PMF.bind_pure, quiet_finalLaw,
      expect_bind_tower_bounded _ _ _ bound]
  change margin weight reward forfeit deposit *
    (joint.toOuterMeasure {pair | pair.2.transmission.isSome}).toReal ≤
      expect (belief.bind PMF.pure) quiet - expect joint row at regret
  rw [mass, quietMean, rawMean] at regret
  rw [context_value weight nonnegative site representative decision current,
    context_value weight nonnegative site representative decision current]
  exact regret

include representative decision current in
/-- Existing sequential rationality forces zero probability of a second
envelope whenever the checked collateral margin is strictly positive. -/
theorem rational_second_packet_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit rewardNonnegative
      forfeitNonnegative depositNonnegative assessment (assessment.strategy alice))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      rewardNonnegative forfeitNonnegative depositNonnegative assessment alternative)).mp rational
        (quietPolicy weight nonnegative site representative decision current assessment)
        (Set.mem_univ _)
  have regret := quiet_regret weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      assessment
  have nonnegative := ENNReal.toReal_nonneg (a :=
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | response.transmission.isSome}))
  nlinarith

include representative decision current in
/-- The actual well-founded native assessment supplies the required local
comparison, including at information sites reached only through deviations. -/
theorem sequentially_rational_second_packet_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 := by
  apply rational_second_packet_zero weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      marginPositive assessment
  have localRational := rational alice site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

include representative decision current in
/-- Every native sequential equilibrium is silent at these actual final
Alice sites, with arbitrary future Bob behavior and actual pending observations. -/
theorem equilibrium_second_packet_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 :=
  sequentially_rational_second_packet_zero weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      marginPositive assessment equilibrium.1

/-- A bound on the same genuine whole-policy deviation gives the quantitative
probability bound without a new approximate equilibrium definition. -/
theorem second_packet_le_of_deviation_regret
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (epsilon : ℝ)
    (regret : (context weight nonnegative site reward forfeit deposit assessment).value
        (quietPolicy weight nonnegative site representative decision current assessment) -
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy alice) ≤ epsilon) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | response.transmission.isSome}).toReal ≤
      epsilon / margin weight reward forfeit deposit := by
  apply (le_div_iff₀ marginPositive).mpr
  have bound := quiet_regret weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      assessment
  nlinarith

end Vegas.Examples.LateOpeningRuntimeAliceRationality

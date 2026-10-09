/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstResponse
import Vegas.Examples.LateOpeningRuntimeAliceFirstContinuation

/-! # Genuine or silent responses at Alice's first late callback

The current-law repair keeps silence and every genuine raw opening alias,
and replaces only a nongenuine packet with silence. The incumbent's own
sequentially rational final callback supplies the deferred opening lower
bound, so no future behavioral policy or opponent is replaced. The result
holds over every history in the actual native information set.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeAliceFirstDecision
  LateOpeningRuntimeAliceFirstResponse

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨22, some alice, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- The first late repair retains every permitted current branch and the
entire incumbent future. Its quantitative gain uses the actual audit charge. -/
theorem repair_regret
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit *
        ((responseLaw weight nonnegative site (assessment.strategy alice site.1)).toOuterMeasure
          {response | ¬ PermittedResponse weight nonnegative decision response}).toReal ≤
      (context weight nonnegative site reward forfeit deposit assessment).value
        (repairedPolicy weight nonnegative site representative decision current assessment) -
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy alice) := by
  classical
  let belief := assessment.belief alice site
  let actions := responseLaw weight nonnegative site (assessment.strategy alice site.1)
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  let recover := decisionOfInformation weight nonnegative site representative decision current
  let utility := aliceUtility reward forfeit deposit
  let row := fun pair :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1 ×
        app.Action => expect
    (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
      (recover pair.1) pair.2 players) utility
  let repaired := fun pair :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1 ×
        app.Action => (pair.1, repairResponse weight nonnegative decision pair.2)
  let joint := belief.bind fun history => actions.map fun response => (history, response)
  let bad : Set
      ((LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1 ×
        app.Action) := {pair | ¬ PermittedResponse weight nonnegative decision pair.2}
  let indicator := fun pair =>
    @ite ℝ (pair ∈ bad) (Classical.propDecidable _) 1 0
  have constantNonnegative : 0 ≤ reward + forfeit + deposit alice := by positivity
  have bound : ∀ final, |utility final| ≤ reward + forfeit + deposit alice := by
    intro final
    obtain ⟨lower, upper⟩ := aliceUtility_bounds rewardNonnegative forfeitNonnegative
      deposit depositNonnegative final
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have rowBound : ∀ pair, |row pair| ≤ reward + forfeit + deposit alice := by
    intro pair
    exact expect_abs_le_of_bounded constantNonnegative bound
  have domination : ∀ pair,
      row pair + LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit *
        indicator pair ≤ row (repaired pair) := by
    intro pair
    by_cases permitted : PermittedResponse weight nonnegative decision pair.2
    · simp [indicator, bad, repaired, repairResponse, permitted]
    · have nongenuine := (permitted_of_information weight nonnegative site representative
        decision current pair.1 pair.2).not.mpr permitted
      have facts := decisionOfInformation_spec weight nonnegative site representative decision
        current pair.1
      have bounded : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
            (some ⟨22, some alice, (recover pair.1).execution⟩) := by
        rw [← facts.1]
        exact pair.1.1.trace
      have lower := LateOpeningRuntimeAliceFirstContinuation.deferred_payoff_lower
        weight nonnegative reward forfeit deposit positive rewardNonnegative forfeitNonnegative
          depositNonnegative openingMarginPositive assessment rational (recover pair.1) bounded
      change -(1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) *
          (forfeit + deposit alice) ≤ row (pair.1, ⟨none⟩) at lower
      simp only [indicator, bad, Set.mem_ofPred_eq, permitted, not_false_eq_true, ↓reduceIte,
        mul_one, repaired, repairResponse]
      have upper : row pair ≤ reward - deposit alice := by
        rcases pair with ⟨history, ⟨transmission⟩⟩
        cases transmission with
        | none => exact (nongenuine trivial).elim
        | some submission =>
            change ¬ EmitsOpening weight nonnegative (recover history) submission at nongenuine
            exact LateOpeningRuntimeAliceFirstPacket.nongenuine_payoff_upper
              weight nonnegative (recover history) submission nongenuine players
                rewardNonnegative forfeitNonnegative deposit depositNonnegative
      dsimp only [LateOpeningRuntimeAliceRationality.margin]
      linarith
  have indicatorIntegrable : PayoffIntegrable joint indicator :=
    payoffIntegrable_ite_one_zero joint (· ∈ bad)
  have scaledIntegrable : PayoffIntegrable joint (fun pair =>
      LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit * indicator pair) :=
    payoffIntegrable_const_mul indicatorIntegrable
  have augmentedIntegrable : PayoffIntegrable joint (fun pair => row pair +
      LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit * indicator pair) :=
    payoffIntegrable_add (payoffIntegrable_of_bounded _ _ rowBound) scaledIntegrable
  have inequality := expect_mono (μ := joint) (fun pair _ => domination pair)
    augmentedIntegrable
    (payoffIntegrable_of_bounded _ _ (fun pair => rowBound (repaired pair)))
  rw [expect_add (payoffIntegrable_of_bounded _ _ rowBound) scaledIntegrable,
    expect_const_mul] at inequality
  have indicatorMean : expect joint indicator = (joint.toOuterMeasure bad).toReal :=
    expect_indicator joint bad
  rw [indicatorMean] at inequality
  have marginal : joint.map Prod.snd = actions := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
    change actions.map id = actions
    exact PMF.map_id actions
  have mass : (joint.toOuterMeasure bad).toReal =
      (actions.toOuterMeasure {response |
        ¬ PermittedResponse weight nonnegative decision response}).toReal := by
    rw [← marginal, PMF.toOuterMeasure_map_apply]
    rfl
  have rawMean : expect joint row = expect
      (finalLaw weight nonnegative site representative decision current assessment
        (assessment.strategy alice site.1)) utility := by
    rw [expect_bind_tower_bounded belief _ _ rowBound]
    unfold finalLaw
    rw [expect_bind_tower_bounded _ _ _ bound]
    apply expect_congr_on_support
    intro history _
    rw [expect_map, expect_bind_tower_bounded _ _ _ bound]
    rfl
  have repairedMean : expect joint (fun pair => row (repaired pair)) = expect
      (finalLaw weight nonnegative site representative decision current assessment
        ((assessment.strategy alice site.1).map
          (repairChoice weight nonnegative site representative decision current))) utility := by
    rw [expect_bind_tower_bounded belief _ _ (fun pair => rowBound (repaired pair))]
    unfold finalLaw
    rw [repaired_responseLaw, expect_bind_tower_bounded _ _ _ bound]
    apply expect_congr_on_support
    intro history _
    rw [expect_map, expect_bind_tower_bounded _ _ _ bound, expect_map]
    rfl
  rw [mass, rawMean, repairedMean] at inequality
  have repairedValue := context_value weight nonnegative site representative decision current
    reward forfeit deposit assessment ((assessment.strategy alice site.1).map
      (repairChoice weight nonnegative site representative decision current))
  have rawValue := context_value weight nonnegative site representative decision current
    reward forfeit deposit assessment (assessment.strategy alice site.1)
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at rawValue
  change (context weight nonnegative site reward forfeit deposit assessment).value
      (repairedPolicy weight nonnegative site representative decision current assessment) = _
    at repairedValue
  rw [← rawValue, ← repairedValue] at inequality
  linarith

include representative decision current in
/-- Global sequential rationality excludes every nongenuine first late
packet in the complete native information set. Silence remains permitted. -/
theorem sequentially_rational_nongenuine_packet_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice site.1)).toOuterMeasure
      {response | ¬ PermittedResponse weight nonnegative decision response}).toReal = 0 := by
  have localRational := rational alice site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit rewardNonnegative
      forfeitNonnegative depositNonnegative assessment (assessment.strategy alice))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      rewardNonnegative forfeitNonnegative depositNonnegative assessment alternative)).mp
        localRational
        (repairedPolicy weight nonnegative site representative decision current assessment)
        (Set.mem_univ _)
  have regret := repair_regret weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      openingMarginPositive assessment rational
  have marginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
      weight reward forfeit deposit := by
    dsimp only [LateOpeningRuntimeAliceRationality.margin,
      LateOpeningRuntimeAliceOpeningRationality.margin] at *
    linarith [min_le_right forfeit (deposit alice)]
  have massNonnegative := ENNReal.toReal_nonneg (a :=
    ((responseLaw weight nonnegative site (assessment.strategy alice site.1)).toOuterMeasure
      {response | ¬ PermittedResponse weight nonnegative decision response}))
  nlinarith

include representative decision current in
theorem equilibrium_nongenuine_packet_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice site.1)).toOuterMeasure
      {response | ¬ PermittedResponse weight nonnegative decision response}).toReal = 0 :=
  sequentially_rational_nongenuine_packet_zero weight nonnegative site representative decision
    current reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      openingMarginPositive assessment equilibrium.1

end Vegas.Examples.LateOpeningRuntimeAliceFirstRationality

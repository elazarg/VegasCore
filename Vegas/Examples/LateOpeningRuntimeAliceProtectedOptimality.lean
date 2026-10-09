/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceProtectedFiber
import Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality
import Vegas.Examples.LateOpeningRuntimePreservingSettlement
import Vegas.Examples.LateOpeningRuntimeTypeWeight

/-! # The protected sender value under preservation of the source law

The entire protected information class is the initialized physical state.
Its continuation context therefore evaluates the actual current response
followed by both original future policies. Reproducing the source's joint
terminal law fixes this incumbent value to half the sender reward for every
initialized type. Sequential rationality bounds current silence, and hence
the original first late continuation, by that value. No posterior assumption
or replacement of a future policy is used.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceProtectedOptimality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeInitializedPrefix LateOpeningRuntimeAliceContinuation
  LateOpeningRuntimePreservingLaw LateOpeningRuntimePreservingSettlement

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1) (bit : Bool) (label : Fin 3)
  (current : representative.1.state = some ⟨25, some alice, protectedDecision bit label⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- Every initialized type has its actual protected native decision class. -/
theorem information_representative :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1),
      representative.1.state = some ⟨25, some alice, protectedDecision bit label⟩ := by
  obtain ⟨trace⟩ := LateOpeningRuntimeTypeWeight.protected_decision_trace
    weight nonnegative bit label
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨25, some alice, protectedDecision bit label⟩, trace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (25 = 0 ∧ some alice = none)
    simp
  obtain ⟨site, same⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history running rfl
  exact ⟨site, ⟨history, same.symm⟩, rfl⟩

def context (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit history.state alice) (2 * LateOpeningRuntimeService.horizon + 1)

def responseLaw
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    PMF app.Action := law.map (fun choice => choice.1.getD ⟨none⟩)

/-- The original first late current law followed by both original futures. -/
def firstValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) : ℝ :=
  expect ((LateOpeningRuntimeFirstRetryComparison.firstResponses weight nonnegative
    assessment.strategy bit label).bind fun response =>
      app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
        22 ((firstLateDecision bit label).respond app alice response))
    (aliceUtility reward forfeit deposit)

include current in
private theorem site_information : site.1 =
    some ((protectedDecision bit label).recall alice,
      (protectedDecision bit label).observe app alice) := by
  rw [← representative.2]
  change (rawMenu.signals _ _ _).infoOf alice representative.1.trace = _
  rw [rawMenu.info, current]
  rfl

include current in
open Classical in
theorem context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      ((assessment.strategy alice).withLaw site.1 law)).map History.state =
      ((responseLaw weight nonnegative site law).bind fun response =>
        app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
          25 ((protectedDecision bit label).respond app alice response)).map app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind]
  calc
    _ = (assessment.belief alice site).bind fun _ =>
        ((responseLaw weight nonnegative site law).bind fun response =>
          app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
            (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
              (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
            25 ((protectedDecision bit label).respond app alice response)).map app.finished := by
      apply bind_congr_on_support
      intro history _
      have actual := LateOpeningRuntimeAliceProtectedFiber.information_history_state
        weight nonnegative site representative bit label current history
      have native := rawMenu.run_local_law_finish_of_information initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
        assessment.strategy history.1 alice 25 (protectedDecision bit label) actual site.1
        history.2 law (2 * LateOpeningRuntimeService.horizon)
        (by rw [actual]; change 51 ≤ 53; decide)
      unfold ReactiveApplication.finish ReactiveApplication.resume at native
      simp only [PMF.pure_bind] at native
      rw [PMF.map_bind]
      exact native
    _ = _ := PMF.bind_const _ _

include current in
open Classical in
theorem context_value_eq_physical
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      ((assessment.strategy alice).withLaw site.1 law) =
      expect ((responseLaw weight nonnegative site law).bind fun response =>
        app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
          25 ((protectedDecision bit label).respond app alice response))
        (aliceUtility reward forfeit deposit) := by
  have projected := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      ((assessment.strategy alice).withLaw site.1 law))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state alice)
  rw [context_outcome_law weight nonnegative site representative bit label current,
    expect_map] at projected
  exact projected.symm

include current in
private theorem current_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    responseLaw weight nonnegative site (assessment.strategy alice site.1) =
      rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy alice
        ((protectedDecision bit label).recall alice)
        ((protectedDecision bit label).observe app alice) := by
  unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
    ReactiveApplication.ResponseMenu.embedPolicy responseLaw
  rw [PMF.map_comp, site_information weight nonnegative site representative bit label current]
  rfl

private theorem initialized_terminal_payoff
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (same : nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      deposit profile = safeTerminalLaw reward)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile)
      26 (initialExecution bit label)).support) :
    aliceUtility reward forfeit deposit final = reward / 2 := by
  let root := (rawMenu.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).initHistory
  have evaluated := rawMenu.run_eq_finish initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile
      (2 * LateOpeningRuntimeService.horizon + 1) root (by exact le_refl _)
  have rootState : root.state = none := rfl
  rw [rootState] at evaluated
  have supported : app.finished final ∈
      (((LateOpeningRuntimeNash.model weight nonnegative).runBehavioral profile
        (2 * LateOpeningRuntimeService.horizon + 1)).map History.state).support := by
    change _ ∈ (((rawMenu.information initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).runBehavioralFrom profile
        (2 * LateOpeningRuntimeService.horizon + 1) root).map History.state).support
    rw [evaluated]
    change _ ∈ (initial.bind fun state =>
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) profile)
        26 (ReactiveApplication.Execution.initial app state)).map app.finished).support
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨initialPhysical bit label, initialPhysical_supported bit label, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
  obtain ⟨history, terminalReached, fixed⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have value := history_payoff_fixed weight nonnegative reward forfeit
    (fun actual => PMF.pure actual) deposit profile same history terminalReached alice
  rw [fixed] at value
  change aliceUtility reward forfeit deposit final =
    (if alice = alice then reward / 2 else (2 / 5 : ℝ)) at value
  rw [ite_eq_left rfl] at value
  exact value

include current in
open Classical in
/-- Joint source-law preservation fixes the incumbent protected value at
each actual initialized type, without a Bayes or equilibrium premise. -/
theorem preserving_incumbent_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (same : nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      deposit assessment.strategy = safeTerminalLaw reward) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy alice) = reward / 2 := by
  have physical := context_value_eq_physical weight nonnegative site representative bit label
    current reward forfeit deposit assessment (assessment.strategy alice site.1)
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self, current_law weight nonnegative site
    representative bit label current] at physical
  rw [physical, ← expect_constant _ (reward / 2)]
  apply expect_congr_on_support
  intro final reached
  apply initialized_terminal_payoff weight nonnegative bit label reward forfeit deposit
    assessment.strategy same final
  change final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
    (25 + 1) (initialExecution bit label)).support
  rw [ReactiveApplication.runRounds, protected_round weight nonnegative,
    ReactiveApplication.invoke, PMF.bind_map]
  exact reached

include current in
private def quietChoice :
    (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1 := by
  refine ⟨some ⟨none⟩, ?_⟩
  rw [site_information weight nonnegative site representative bit label current]
  exact ⟨⟨none⟩, bounds.silent_available LateOpeningRuntimeService.runtime leaks alice _ _, rfl⟩

include current in
open Classical in
/-- Changing only the protected response to silence reaches the original
first late response distribution and keeps every future policy. -/
theorem quiet_value_eq_first
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      ((assessment.strategy alice).commit site.1
        (quietChoice weight nonnegative site representative bit label current)) =
      firstValue weight nonnegative bit label reward forfeit deposit assessment := by
  change (context weight nonnegative site reward forfeit deposit assessment).value
    ((assessment.strategy alice).withLaw site.1 (PMF.pure _)) = _
  rw [context_value_eq_physical weight nonnegative site representative bit label current]
  simp only [responseLaw, PMF.pure_map, PMF.pure_bind]
  change expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
    25 ((protectedDecision bit label).respond app alice ⟨none⟩)) _ = _
  rw [LateOpeningRuntimeAliceProtectedFiber.protected_none_suffix]
  rfl

include current in
/-- A preserving sequentially rational native profile bounds the original
first late continuation at every initialized bit and private label. -/
theorem preserving_first_value_le_half
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (same : nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      deposit assessment.strategy = safeTerminalLaw reward) :
    firstValue weight nonnegative bit label reward forfeit deposit assessment ≤ reward / 2 := by
  classical
  have localRational := rational alice site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  have best := (Context.isLocallyOptimal_iff_of_integrable
    (payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)).mp
      localRational ((assessment.strategy alice).commit site.1
        (quietChoice weight nonnegative site representative bit label current)) (Set.mem_univ _)
  change (context weight nonnegative site reward forfeit deposit assessment).value _ ≤
    (context weight nonnegative site reward forfeit deposit assessment).value _ at best
  rw [quiet_value_eq_first weight nonnegative site representative bit label current,
    preserving_incumbent_value weight nonnegative site representative bit label current
      reward forfeit deposit assessment same] at best
  exact best

/-- At every initialized type the original first late value dominates
each legal current raw response with the original future retained. -/
theorem first_value_ge_response
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    LateOpeningRuntimeAliceFirstOptimality.responseValue weight nonnegative bit label
      reward forfeit deposit assessment response ≤
        firstValue weight nonnegative bit label reward forfeit deposit assessment := by
  classical
  obtain ⟨trace⟩ := LateOpeningRuntimeAliceFirstWitness.firstLateDecision_trace
    weight nonnegative bit label
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨22, some alice, firstLateDecision bit label⟩, trace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (22 = 0 ∧ some alice = none)
    simp
  obtain ⟨site, same⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history running rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨22, some alice, firstLateDecision bit label⟩ := rfl
  have best := LateOpeningRuntimeAliceFirstOptimality.sequentially_rational_value_ge_response
    weight nonnegative site representative bit label current reward forfeit deposit
      assessment rational response available
  have physical := LateOpeningRuntimeAliceFirstFiber.context_value_eq_physical weight nonnegative
    site representative bit label current reward forfeit deposit assessment
      (assessment.strategy alice site.1)
  have decoded : LateOpeningRuntimeAliceFirstResponse.responseLaw weight nonnegative site
      (assessment.strategy alice site.1) =
      LateOpeningRuntimeFirstRetryComparison.firstResponses weight nonnegative assessment.strategy
        bit label := by
    unfold LateOpeningRuntimeFirstRetryComparison.firstResponses
      LateOpeningRuntimeFirstRetryComparison.players ReactiveApplication.ResponseMenu.decodeProfile
      ReactiveApplication.decodePolicy ReactiveApplication.ResponseMenu.embedPolicy
      LateOpeningRuntimeAliceFirstResponse.responseLaw
    rw [PMF.map_comp, LateOpeningRuntimeAliceFirstResponse.site_information weight nonnegative
      site representative (LateOpeningRuntimeAliceFirstWitness.decisionHistory
        weight nonnegative bit label) current]
    rfl
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self, decoded] at physical
  rw [physical] at best
  exact best

/-- The preservation bound applies to every initialized bit and label,
including types whose later first callback is off the assessed path. -/
theorem preserving_first_value_le_half_all_types
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (same : nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      deposit assessment.strategy = safeTerminalLaw reward) :
    firstValue weight nonnegative bit label reward forfeit deposit assessment ≤ reward / 2 := by
  obtain ⟨site, representative, current⟩ :=
    information_representative weight nonnegative bit label
  exact preserving_first_value_le_half weight nonnegative site representative bit label current
    reward forfeit deposit assessment rational same

end Vegas.Examples.LateOpeningRuntimeAliceProtectedOptimality

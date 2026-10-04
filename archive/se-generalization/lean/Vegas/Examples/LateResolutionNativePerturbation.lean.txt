/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionNativeRationality

/-! # Actual fully mixed native regret near the waiting prescription

The standard native perturbation computes its beliefs from actual play. Its
continuation regret has a belief-independent lower bound because every history
at the late information site has the same waiting loss and legal FALSE remedy.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

theorem auditedUtility_bounds
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (state : app.ProtocolState) (who : Player) :
    auditedUtility sample deposit state who ∈ Set.Icc (-deposit) 1 := by
  have base : baseUtility setup leaks sourceUtility state who ∈ Set.Icc 0 1 := by
    unfold baseUtility
    cases decoded : sourceReadout setup leaks state with
    | none => simp
    | some source =>
        simp only [Option.elim_some, sourceUtility]
        split <;> norm_num
  have charge := GameTheory.Enforcement.TerminalAudit.charge_mem_Icc
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
    state who
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
  constructor <;> nlinarith [base.1, base.2, charge.1, charge.2]

theorem auditedUtility_integrable (law : PMF app.ProtocolState)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (who : Player) :
    PayoffIntegrable law (fun state => auditedUtility sample deposit state who) := by
  apply payoffIntegrable_of_bounded law _ (C := 1 + deposit)
  intro state
  have bounds := auditedUtility_bounds sample deposit nonnegative state who
  exact abs_le.mpr ⟨by linarith [bounds.1], by linarith [bounds.2]⟩

theorem late_native_choice_value (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (execution : app.Execution) (current : history.state = some ⟨4, some owner, execution⟩)
    (position : execution.environmentRecall.length = 6)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) :
    expect ((nativeModel bounds).runBehavioralFrom profile 21 history)
      (fun final => auditedUtility sample deposit final.state owner) =
    expect (profile owner (some (execution.recall owner, execution.observe app owner)))
      (fun choice => expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner (choice.val.getD ⟨none⟩))).map app.finished)
          (fun state => auditedUtility sample deposit state owner)) := by
  calc
    _ = expect (((nativeModel bounds).runBehavioralFrom profile 21 history).map
        GameTheory.Protocol.ExecutionProtocol.History.state)
          (fun state => auditedUtility sample deposit state owner) :=
      (expect_map (fun final :
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History => final.state)
        _ _).symm
    _ = _ := by
      rw [late_native_run_state (nativeMenu bounds) profile history execution current position,
        PMF.bind_map]
      exact expect_bind_tower _ _ _ (auditedUtility_integrable _ sample deposit nonnegative owner)

section Perturbation

variable (bounds : MessageBounds nativeGraph) (witness : app.Execution)
  (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
    (some ⟨4, some owner, witness⟩))
  (ready : witness.application.config.cut.Ready resolution)
  (entered : witness.application.activatedAt resolution = some 0)
  (clock : witness.application.clock = 1) (empty : witness.network = .empty)
  (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
  (deposit : ℝ) (nonnegative : 0 ≤ deposit) (turns : Nat)
  (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
  (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)

include ready entered clock empty nonnegative

theorem late_perturbed_wait_value_le :
    let assessment := (nativeMenu bounds).perturbedAssessment (initialLaw setup) horizon scheduler
      (nativeTurnProfile bounds turns timing profile) weight positive atMostOne
    (assessment.truncatedContinuationContext (lateSite bounds witness trace)
      (fun final => auditedUtility sample deposit final.state owner) 21).value
        (assessment.strategy owner) ≤ weight - (1 - weight) * deposit := by
  intro assessment
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    Profile.update_eq_self, expect_bind_of_finite]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro history _
  obtain ⟨execution, current, position, actualClock, actualReady, actualEntered, actualEmpty⟩ :=
    late_information_resources bounds witness trace ready entered clock empty history
  rw [late_native_choice_value bounds assessment.strategy history.1 execution current position
    sample deposit nonnegative]
  let input := some (execution.recall owner, execution.observe app owner)
  let value (choice : (nativeModel bounds).Choice owner input) : ℝ :=
    expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
      (execution.respond app owner (choice.val.getD ⟨none⟩))).map app.finished)
        (fun state => auditedUtility sample deposit state owner)
  have mixture : assessment.strategy owner input = mix weight positive.le atMostOne
      (((nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler).strategy
        owner input) (nativeTurnProfile bounds turns timing profile owner input) := rfl
  have waiting : expect (nativeTurnProfile bounds turns timing profile owner input) value =
      -deposit := by
    let rawValue (action : Option app.Action) : ℝ :=
      expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner (action.getD ⟨none⟩))).map app.finished)
          (fun state => auditedUtility sample deposit state owner)
    change expect (nativeTurnProfile bounds turns timing profile owner input)
      (fun choice => rawValue choice.val) = _
    calc
      _ = expect ((nativeTurnProfile bounds turns timing profile owner input).map Subtype.val)
          rawValue := (expect_map Subtype.val _ rawValue).symm
      _ = _ := by
        rw [late_nativeTurnProfile_waits bounds execution actualReady actualEntered actualClock
          turns timing profile, expect_pure]
        exact late_silence_value execution position actualReady actualEntered actualClock
          actualEmpty sample deposit
  have uniform : expect
      (((nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler).strategy
        owner input) value ≤ 1 := by
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1
    intro choice _
    exact expect_le_const _ _ (auditedUtility_integrable _ sample deposit nonnegative owner) 1
      (fun state _ => (auditedUtility_bounds sample deposit nonnegative state owner).2)
  change expect (assessment.strategy owner input) value ≤ _
  rw [mixture, expect_mix_of_finite, waiting]
  nlinarith

theorem late_perturbed_regret
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    let assessment := (nativeMenu bounds).perturbedAssessment (initialLaw setup) horizon scheduler
      (nativeTurnProfile bounds turns timing profile) weight positive atMostOne
    ∃ alternative : (nativeModel bounds).BehavioralPolicy owner,
      (assessment.truncatedContinuationContext (lateSite bounds witness trace)
        (fun final => auditedUtility sample deposit final.state owner) 21).value alternative = 0 ∧
      (1 - weight) * deposit - weight ≤
        (assessment.truncatedContinuationContext (lateSite bounds witness trace)
          (fun final => auditedUtility sample deposit final.state owner) 21).value alternative -
        (assessment.truncatedContinuationContext (lateSite bounds witness trace)
          (fun final => auditedUtility sample deposit final.state owner) 21).value
            (assessment.strategy owner) := by
  classical
  intro assessment
  let candidate : Handle nativeGraph := ⟨owner, .prepared 0⟩
  let choice : (nativeModel bounds).Choice owner (lateSite bounds witness trace).1 :=
    ⟨some (lateResponse candidate false), lateResponse candidate false,
      late_withhold_available bounds witness trace ready entered clock empty candidate, rfl⟩
  let alternative := (assessment.strategy owner).withLaw (lateSite bounds witness trace).1
    (PMF.pure choice)
  have chooses : (alternative (lateSite bounds witness trace).1).map Subtype.val =
      PMF.pure (some (lateResponse candidate false)) := by
    simp only [alternative, InformationModel.BehavioralPolicy.withLaw_self, PMF.pure_map]
    rfl
  have value := late_context_false_value bounds witness trace ready entered clock empty sample
    deposit assessment candidate authentic alternative chooses
  have upper := late_perturbed_wait_value_le bounds witness trace ready entered clock empty sample
    deposit nonnegative turns timing profile weight positive atMostOne
  refine ⟨alternative, value, ?_⟩
  rw [value]
  linarith

end Perturbation

/-- This is the actual fully mixed native Bayes assessment and a genuinely
reached information site. The bound holds without any assumed posterior or
identification of its play with a geometric physical path. -/
theorem exists_perturbed_native_late_regret (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    let assessment := (nativeMenu bounds).perturbedAssessment (initialLaw setup) horizon scheduler
      (nativeTurnProfile bounds turns timing profile) weight positive atMostOne
    ∃ (site : (nativeModel bounds).InformationSite owner)
      (alternative : (nativeModel bounds).BehavioralPolicy owner),
      (assessment.truncatedContinuationContext site
        (fun final => auditedUtility sample deposit final.state owner) 21).value alternative = 0 ∧
      (1 - weight) * deposit - weight ≤
        (assessment.truncatedContinuationContext site
          (fun final => auditedUtility sample deposit final.state owner) 21).value alternative -
        (assessment.truncatedContinuationContext site
          (fun final => auditedUtility sample deposit final.state owner) 21).value
            (assessment.strategy owner) ∧
      ∀ history : (nativeModel bounds).InformationHistory owner site.1,
        history.1 ∈ ((nativeModel bounds).runBehavioral assessment.strategy
          history.1.trace.length).support := by
  intro assessment
  obtain ⟨before, witness, _, _, _, ⟨trace⟩, _, clock, ready, entered, empty⟩ :=
    exists_late_risk_turn bounds
  obtain ⟨alternative, value, bound⟩ := late_perturbed_regret bounds witness trace ready entered
    clock empty sample deposit nonnegative turns timing profile weight positive atMostOne authentic
  refine ⟨lateSite bounds witness trace, alternative, value, bound, ?_⟩
  intro history
  exact ((nativeMenu bounds).perturbedAssessment_fullyMixed (initialLaw setup) horizon scheduler
    (nativeTurnProfile bounds turns timing profile) weight positive atMostOne).history_supported
      history.1.trace

/-- At one fixed actual information site, shrinking native trembles leaves a
strict conditional regret, even if the source profile and turn timing vary.
All histories in its fiber have positive actual native probability. -/
theorem exists_nonvanishing_perturbed_native_regret (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (depositPositive : 0 < deposit) (turns : Nat)
    (timing : Nat → TurnTiming setup turns)
    (profile : Nat → BehavioralProfile setup.program)
    (weight : Nat → ℝ) (positive : ∀ n, 0 < weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Filter.Tendsto weight Filter.atTop (nhds 0)) :
    ∃ site : (nativeModel bounds).InformationSite owner,
      ∀ᶠ n in Filter.atTop,
        let assessment := (nativeMenu bounds).perturbedAssessment (initialLaw setup) horizon
          scheduler (nativeTurnProfile bounds turns (timing n) (profile n)) (weight n)
            (positive n) (atMostOne n)
        ∃ alternative : (nativeModel bounds).BehavioralPolicy owner,
          deposit / 2 ≤
            (assessment.truncatedContinuationContext site
              (fun final => auditedUtility sample deposit final.state owner) 21).value alternative -
            (assessment.truncatedContinuationContext site
              (fun final => auditedUtility sample deposit final.state owner) 21).value
                (assessment.strategy owner) ∧
          ∀ history : (nativeModel bounds).InformationHistory owner site.1,
            history.1 ∈ ((nativeModel bounds).runBehavioral assessment.strategy
              history.1.trace.length).support := by
  obtain ⟨before, witness, _, _, _, ⟨trace⟩, _, clock, ready, entered, empty⟩ :=
    exists_late_risk_turn bounds
  refine ⟨lateSite bounds witness trace, ?_⟩
  have small : ∀ᶠ n in Filter.atTop, weight n < deposit / (2 * (deposit + 1)) :=
    (tendsto_order.mp vanishes).2 _ (by positivity)
  filter_upwards [small] with n small
  obtain ⟨alternative, _, bound⟩ := late_perturbed_regret bounds witness trace ready entered clock
    empty sample deposit depositPositive.le turns (timing n) (profile n) (weight n)
      (positive n) (atMostOne n) authentic
  refine ⟨alternative, ?_, ?_⟩
  · have weighted := (lt_div_iff₀ (by positivity : 0 < 2 * (deposit + 1))).mp small
    exact (by nlinarith : deposit / 2 ≤ (1 - weight n) * deposit - weight n).trans bound
  · intro history
    exact ((nativeMenu bounds).perturbedAssessment_fullyMixed (initialLaw setup) horizon scheduler
      (nativeTurnProfile bounds turns (timing n) (profile n)) (weight n) (positive n)
        (atMostOne n)).history_supported history.1.trace

end Vegas.LateResolutionService

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSeenLikelihood
import Vegas.Examples.LateOpeningRuntimeInitializedPrefix
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.EventSequentialTiming
import Vegas.Examples.LateOpeningRuntimeBindingObservationWitness
import Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw

/-! # Initialized type weights in complete native seen-information groups

The type weight is the original initialized prior atom multiplied by the
original protected-silence atom. The initialized-input readout is immutable
through every raw branch, so filtering an actual complete information class
by that readout extracts this weight from the original prefix law.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeInitializedPrefix
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeSeenLikelihood
open Filter

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem input_parameter_injective : Function.Injective
    (fun parameter : Parameter => setup.eventInputs (sourceInitial parameter.1 parameter.2)) := by
  rintro ⟨bit, label⟩ ⟨otherBit, otherLabel⟩ same
  have bits := congrFun same aliceInput
  change (.success bit : PublicationResult Bool) = .success otherBit at bits
  have labels := congrArg (fun inputs : nativeGraph.Inputs => (inputs labelInput).val) same
  have sameBit : bit = otherBit := PublicationResult.success.inj bits
  have sameLabel : label = otherLabel := by
    apply Fin.ext
    change (label.val : Int) = (otherLabel.val : Int) at labels
    exact_mod_cast labels
  exact Prod.ext sameBit sameLabel

theorem first_binding_inputs (bit : Bool) (label : Fin 3) (response : app.Action)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (firstBindingLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response players).support) :
    final.application.config.inputs = setup.eventInputs (sourceInitial bit label) := by
  let invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have valid : State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) (firstLateDecision bit label).application := by
    change ({ initialPhysical bit label with clock := 1 } : app.State).Invariant _
    exact (State.initial_invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label))).add_clock 1
  obtain ⟨before, continued, activated⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have sent := invariant.respond (firstLateDecision bit label) alice response valid
  have retained := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 7 _ before sent continued
  exact (invariant.environmentStep before final (.activate bob)
    retained activated).reachable.inputs_eq

theorem original_inputs (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3)
    (final : app.Execution)
    (reached : final ∈ (originalLaw weight nonnegative profile bit label).support) :
    final.application.config.inputs = setup.eventInputs (sourceInitial bit label) := by
  obtain ⟨response, _, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  exact first_binding_inputs weight nonnegative bit label response
    (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative profile) final continued

def typeWeight (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) : ℝ :=
  (prior (bit, label)).toReal *
    (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative profile alice
      ((protectedDecision bit label).recall alice)
      ((protectedDecision bit label).observe app alice) ⟨none⟩).toReal

theorem typeWeight_nonnegative (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) : 0 ≤ typeWeight weight nonnegative profile bit label :=
  mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem seen_execution_ready (bit : Bool) (label : Fin 3) (accepted : Bool) :
    (seenExecution bit label accepted).application.config.cut.Ready bobBindEvent := by
  cases accepted
  · exact LateOpeningRuntimeBindingObservation.failedAnswerDecision_binding_ready
      bit label 0 true false
  · simp only [seenExecution, ↓reduceIte]
    rw [LateOpeningRuntimeLateAcceptance.answerDecision_physical]
    change bobBindEvent ∉ ({aliceEvent} : Finset nativeGraph.EventId) ∧
      nativeGraph.order.predecessors bobBindEvent ⊆ {aliceEvent}
    decide

def typedSeenEvent (bit : Bool) (label : Fin 3) (accepted : Bool) : Set app.ProtocolState :=
  {state | app.observe bob state =
      some (LateOpeningRuntimeBindingObservation.bobInformation
        (seenExecution bit label accepted)) ∧
    initializedInputs state = some (setup.eventInputs (sourceInitial bit label))}

open Classical in
theorem typed_branch_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (accepted : Bool) (parameter : Parameter) :
    ((originalLaw weight nonnegative profile parameter.1 parameter.2).toOuterMeasure
      {final | (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
        typedSeenEvent bit label accepted}).toReal =
      if (bit, label) = parameter then
        ((originalLaw weight nonnegative profile bit label).toOuterMeasure
          (seenEvent bit label accepted)).toReal else 0 := by
  classical
  by_cases same : (bit, label) = parameter
  · subst parameter
    rw [ite_eq_left rfl, ← expect_indicator, ← expect_indicator]
    apply expect_congr_on_support
    intro final reached
    have inputs := original_inputs weight nonnegative profile bit label final reached
    have equal : (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
        typedSeenEvent bit label accepted ↔ final ∈ seenEvent bit label accepted := by
      change (some (LateOpeningRuntimeBindingObservation.bobInformation final) =
          some (LateOpeningRuntimeBindingObservation.bobInformation
            (seenExecution bit label accepted)) ∧
        some final.application.config.inputs =
          some (setup.eventInputs (sourceInitial bit label))) ↔ _
      rw [inputs]
      simp only [Option.some.injEq, and_true]
      rfl
    change (if (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
      typedSeenEvent bit label accepted then (1 : ℝ) else 0) = _
    rw [equal]
  · rw [ite_eq_right same]
    have zero : (originalLaw weight nonnegative profile parameter.1 parameter.2).toOuterMeasure
        {final | (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
          typedSeenEvent bit label accepted} = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro final reached member
      have inputs := original_inputs weight nonnegative profile parameter.1 parameter.2
        final reached
      have filtered := member.2
      change some final.application.config.inputs =
        some (setup.eventInputs (sourceInitial bit label)) at filtered
      rw [inputs] at filtered
      exact same ((input_parameter_injective (Option.some.inj filtered)).symm)
    rw [zero, ENNReal.toReal_zero]

variable (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1) (bit : Bool) (label : Fin 3) (accepted : Bool)
  (current : representative.1.state =
    some ⟨14, some bob, seenExecution bit label accepted⟩)

include current in
theorem site_information : site.1 =
    some (LateOpeningRuntimeBindingObservation.bobInformation
      (seenExecution bit label accepted)) := by
  have information := representative.2
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob
      representative.1.trace = site.1 at information
  rw [rawMenu.info, current] at information
  exact information.symm

include current in
theorem initialized_seen_probability (profile : Profile weight nonnegative) :
    ((bindingPrefix weight nonnegative profile).toOuterMeasure
      (typedSeenEvent bit label accepted)).toReal =
        typeWeight weight nonnegative profile bit label *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (seenEvent bit label accepted)).toReal := by
  classical
  have information := site_information weight nonnegative site representative
    bit label accepted current
  have member : bobObservationRecord bit label true ∈
      (seenExecution bit label accepted).recall bob := by
    rw [seen_execution_recall]
    exact List.mem_singleton.mpr rfl
  have identity := clean_information_probability weight nonnegative site representative
    ⟨14, some bob, seenExecution bit label accepted⟩ current rfl
      (bobObservationRecord bit label true) member (by change 0 < 1; decide) rfl
      profile (typedSeenEvent bit label accepted)
        (fun state filtered => filtered.1.trans information.symm)
  change ((bindingPrefix weight nonnegative profile).toOuterMeasure
      (typedSeenEvent bit label accepted)).toReal =
    expect prior (fun parameter =>
      (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative profile alice
        ((protectedDecision parameter.1 parameter.2).recall alice)
        ((protectedDecision parameter.1 parameter.2).observe app alice) ⟨none⟩).toReal *
      ((originalLaw weight nonnegative profile parameter.1 parameter.2).toOuterMeasure
        {final | (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
          typedSeenEvent bit label accepted}).toReal) at identity
  rw [identity]
  calc
    _ = expect prior (fun parameter => if (bit, label) = parameter then
        (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative profile alice
          ((protectedDecision bit label).recall alice)
          ((protectedDecision bit label).observe app alice) ⟨none⟩).toReal *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (seenEvent bit label accepted)).toReal else 0) := by
      apply expect_congr_on_support
      intro parameter _
      rw [typed_branch_probability]
      split_ifs with same
      · subst parameter
        rfl
      · rw [mul_zero]
    _ = _ := by
      rw [expect_ite_eq]
      unfold typeWeight
      ring

include current in
theorem initialized_seen_error (profile : Profile weight nonnegative)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error) :
    |((bindingPrefix weight nonnegative profile).toOuterMeasure
        (typedSeenEvent bit label accepted)).toReal -
      typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label *
          earlySilenceProbability weight nonnegative profile bit label *
            settlementProbability weight accepted / 2| ≤
      error * typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label := by
  rw [initialized_seen_probability weight nonnegative site representative
    bit label accepted current profile]
  have difference :
      typeWeight weight nonnegative profile bit label *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (seenEvent bit label accepted)).toReal -
        typeWeight weight nonnegative profile bit label *
          genuineProbability weight nonnegative profile bit label *
            earlySilenceProbability weight nonnegative profile bit label *
              settlementProbability weight accepted / 2 =
      typeWeight weight nonnegative profile bit label *
        (((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (seenEvent bit label accepted)).toReal -
          genuineProbability weight nonnegative profile bit label *
            earlySilenceProbability weight nonnegative profile bit label *
              settlementProbability weight accepted / 2) := by ring
  rw [difference, abs_mul, abs_of_nonneg (typeWeight_nonnegative weight nonnegative
    profile bit label)]
  have close := original_seen_error weight nonnegative profile bit label accepted
    error errorNonnegative bound
  calc
    _ ≤ typeWeight weight nonnegative profile bit label *
        (error * genuineProbability weight nonnegative profile bit label) :=
      mul_le_mul_of_nonneg_left close
        (typeWeight_nonnegative weight nonnegative profile bit label)
    _ = _ := by ring

include current in
/-- This is the sum over every actual raw history in the receiver class with
the given immutable initialized input, including every private packet alias. -/
theorem initialized_history_seen_error (profile : Profile weight nonnegative)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error) :
    |InformationModel.finiteHistoryReach profile bob site
        (readoutHistories weight nonnegative site initializedInputs
          (some (setup.eventInputs (sourceInitial bit label)))) -
      typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label *
          earlySilenceProbability weight nonnegative profile bit label *
            settlementProbability weight accepted / 2| ≤
      error * typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label := by
  rw [initialized_type_reach_eq_prefix weight nonnegative site representative
    (seenExecution bit label accepted) current (seen_execution_ready bit label accepted)]
  have information := site_information weight nonnegative site representative
    bit label accepted current
  rw [information]
  exact initialized_seen_error weight nonnegative site representative bit label accepted
    current profile error errorNonnegative bound

/-- Both canonical retained-opening observations are actual native information
classes, constructed from admitted initialized raw histories. -/
theorem exists_seen_representative (positive : 0 < weight) (bit : Bool) (label : Fin 3)
    (accepted : Bool) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1),
      representative.1.state = some ⟨14, some bob, seenExecution bit label accepted⟩ := by
  cases accepted
  · obtain ⟨site, representative, current, _⟩ :=
      LateOpeningRuntimeBindingObservationWitness.failed_information_representative
        weight nonnegative bit label 0 true false (Or.inl rfl)
    exact ⟨site, representative, current⟩
  · obtain ⟨trace⟩ := LateOpeningRuntimeLateHistories.answerDecision_trace
      weight nonnegative positive bit label 0 true (Or.inl rfl)
    let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
      ⟨some ⟨14, some bob, LateOpeningRuntimeLateAcceptance.answerDecision bit label 0 true⟩,
        trace⟩
    have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
      change ¬ (14 = 0 ∧ some bob = none)
      simp
    obtain ⟨site, same⟩ :=
      (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
        bob history running rfl
    exact ⟨site, ⟨history, same.symm⟩, rfl⟩

/-- The original early receiver atom converges to one at the actual legal
seen-opening information class along the same assessment sequence. -/
theorem early_silence_tendsto
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (bit : Bool) (label : Fin 3) :
    Tendsto (fun n => earlySilenceProbability weight nonnegative (sequence n).strategy bit label)
      atTop (nhds 1) := by
  obtain ⟨site, history, current⟩ :=
    LateOpeningRuntimeEarlyResponseLaw.information_representative
      weight nonnegative bit label 0 true (Or.inl rfl)
  have information := history.2
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob
      history.1.trace = site.1 at information
  rw [rawMenu.info, current] at information
  have observed : site.1 = some
      ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).recall bob,
        (LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).observe app bob) :=
    information.symm
  have decoded : PMFConvergesPointwise (fun n =>
      players weight nonnegative (sequence n).strategy bob
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).recall bob)
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).observe app bob))
      (players weight nonnegative assessment.strategy bob
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).recall bob)
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).observe app bob)) := by
    have limit := (converges.strategy bob site).map (fun choice => choice.1.getD ⟨none⟩)
    simp only [players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def]
    rw [← observed]
    exact limit
  have limit := decoded.toReal (⟨none⟩ : app.Action)
  have silent := LateOpeningRuntimeEarlyResponseLaw.sequentially_rational_response_law
    weight nonnegative reward forfeit deposit forfeitNonnegative collateral
      assessment rational bit label 0 true (Or.inl rfl)
  rw [silent, PMF.pure_apply_self, ENNReal.toReal_one] at limit
  simpa only [earlySilenceProbability, LateOpeningRuntimeEarlyResponseLaw.observed,
    ↓reduceIte] using limit

end Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood

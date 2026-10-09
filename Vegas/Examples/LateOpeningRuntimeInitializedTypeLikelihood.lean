/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeInitializedPrefix
import Vegas.Examples.LateOpeningRuntimeFirstRetryComparison
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.EventSequentialTiming

/-! # Original initialized type factors in full receiver information groups -/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeInitializedPrefix
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeBindingObservation

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

def typedInformationEvent (information : BobInformation) (bit : Bool) (label : Fin 3) :
    Set app.ProtocolState :=
  {state | app.observe bob state =
      some information ∧
    initializedInputs state = some (setup.eventInputs (sourceInitial bit label))}

open Classical in
theorem typed_branch_probability (profile : Profile weight nonnegative)
    (information : BobInformation) (bit : Bool) (label : Fin 3) (parameter : Parameter) :
    ((originalLaw weight nonnegative profile parameter.1 parameter.2).toOuterMeasure
      {final | (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
        typedInformationEvent information bit label}).toReal =
      if (bit, label) = parameter then
        ((originalLaw weight nonnegative profile bit label).toOuterMeasure
          {final | bobInformation final = information}).toReal else 0 := by
  classical
  by_cases same : (bit, label) = parameter
  · subst parameter
    rw [ite_eq_left rfl, ← expect_indicator, ← expect_indicator]
    apply expect_congr_on_support
    intro final reached
    have inputs := original_inputs weight nonnegative profile bit label final reached
    have equal : (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
        typedInformationEvent information bit label ↔ bobInformation final = information := by
      change (some (LateOpeningRuntimeBindingObservation.bobInformation final) =
          some information ∧
        some final.application.config.inputs =
          some (setup.eventInputs (sourceInitial bit label))) ↔ _
      rw [inputs]
      simp only [Option.some.injEq, and_true]
    change (if (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
      typedInformationEvent information bit label then (1 : ℝ) else 0) = _
    rw [equal]
    rfl
  · rw [ite_eq_right same]
    have zero : (originalLaw weight nonnegative profile parameter.1 parameter.2).toOuterMeasure
        {final | (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
          typedInformationEvent information bit label} = 0 := by
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
    bob site.1) (execution : app.Execution)
  (current : representative.1.state = some ⟨14, some bob, execution⟩)
  (remembered : app.PlayerEntry) (member : remembered ∈ execution.recall bob)
  (later : 0 < remembered.beforeView.application.publicView.clock)
  (empty : remembered.beforeView.receipts = [])

include current in
theorem site_information : site.1 = some (bobInformation execution) := by
  have information := representative.2
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob
      representative.1.trace = site.1 at information
  rw [rawMenu.info, current] at information
  exact information.symm

include current member later empty in
/-- An actual complete receiver-information group with its initialized type
has the original prior-times-protected-silence weight. All later raw packet
representations and the original continuation policy remain in the law. -/
theorem initialized_information_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) :
    ((bindingPrefix weight nonnegative profile).toOuterMeasure
      (typedInformationEvent (bobInformation execution) bit label)).toReal =
        typeWeight weight nonnegative profile bit label *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            {final | bobInformation final = bobInformation execution}).toReal := by
  classical
  have information := site_information weight nonnegative site representative execution current
  have identity := clean_information_probability weight nonnegative site representative
    ⟨14, some bob, execution⟩ current rfl remembered member later empty profile
      (typedInformationEvent (bobInformation execution) bit label)
        (fun state filtered => filtered.1.trans information.symm)
  change ((bindingPrefix weight nonnegative profile).toOuterMeasure
      (typedInformationEvent (bobInformation execution) bit label)).toReal =
    expect prior (fun parameter =>
      (players weight nonnegative profile alice
        ((protectedDecision parameter.1 parameter.2).recall alice)
        ((protectedDecision parameter.1 parameter.2).observe app alice) ⟨none⟩).toReal *
      ((originalLaw weight nonnegative profile parameter.1 parameter.2).toOuterMeasure
        {final | (some ⟨14, some bob, final⟩ : app.ProtocolState) ∈
          typedInformationEvent (bobInformation execution) bit label}).toReal) at identity
  rw [identity]
  calc
    _ = expect prior (fun parameter => if (bit, label) = parameter then
        (players weight nonnegative profile alice
          ((protectedDecision bit label).recall alice)
          ((protectedDecision bit label).observe app alice) ⟨none⟩).toReal *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            {final | bobInformation final = bobInformation execution}).toReal else 0) := by
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

include current member later empty in
/-- The physical probability equals the sum over every real raw history in
the information class with the specified immutable initialized type. -/
theorem initialized_history_probability
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) :
    InformationModel.finiteHistoryReach profile bob site
        (readoutHistories weight nonnegative site initializedInputs
          (some (setup.eventInputs (sourceInitial bit label)))) =
      typeWeight weight nonnegative profile bit label *
        ((originalLaw weight nonnegative profile bit label).toOuterMeasure
          {final | bobInformation final = bobInformation execution}).toReal := by
  rw [initialized_type_reach_eq_prefix weight nonnegative site representative execution current
      ready,
    site_information weight nonnegative site representative execution current]
  exact initialized_information_probability weight nonnegative site representative execution
    current remembered member later empty profile bit label

end Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood

import Vegas.Examples.Refinement

/-!
# Composed refinement smoke examples

These examples exercise refinement/law-family composition end to end: trace
distribution projection, utility-distribution preservation, and Nash transport
through a composed backend relation.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

/-! ## Composed runtime adequacy smoke test -/

noncomputable def matchingPenniesAuditedMachine : Machine Player :=
  Machine.audited matchingPenniesMachine

noncomputable def matchingPenniesDoubleAuditedMachine : Machine Player :=
  Machine.audited matchingPenniesAuditedMachine

noncomputable def matchingPenniesAuditedRefinement :
    Machine.StochasticRefinement matchingPenniesAuditedMachine
      matchingPenniesMachine :=
  Machine.audited.refinement matchingPenniesMachine

noncomputable def matchingPenniesDoubleAuditedRefinement :
    Machine.StochasticRefinement matchingPenniesDoubleAuditedMachine
      matchingPenniesAuditedMachine :=
  Machine.audited.refinement matchingPenniesAuditedMachine

noncomputable def matchingPenniesDoubleAuditedComposedRefinement :
    Machine.StochasticRefinement matchingPenniesDoubleAuditedMachine
      matchingPenniesMachine :=
  matchingPenniesAuditedRefinement.compose
    matchingPenniesDoubleAuditedRefinement

noncomputable def matchingPenniesDoubleAuditedBehavioralAdequacy
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)) :
    WFProgram.RuntimeTraceAdequacy matchingPenniesChecked
      (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)
      matchingPenniesDoubleAuditedComposedRefinement :=
  WFProgram.RuntimeTraceAdequacy.lowerImpl
    (bridge := WFProgram.RuntimeTraceAdequacy.audited law)
    (Machine.audited.liftEventBatchLawFamily
      matchingPenniesAuditedMachine
      (WFProgram.RuntimeTraceAdequacy.audited law).impl)

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    (WFProgram.RuntimeTraceAdequacy.implTraceGame
      (matchingPenniesDoubleAuditedBehavioralAdequacy law)).udist
        profile =
      matchingPenniesChecked.behavioralFrontierGame.udist profile := by
  simpa [WFProgram.behavioralFrontierTraceSurface] using
    WFProgram.RuntimeTraceAdequacy.implTraceGame_udist_surface
      (matchingPenniesDoubleAuditedBehavioralAdequacy law) profile

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked))
    {CImpl CSpec CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility matchingPenniesDoubleAuditedMachine
            (fun _ => 0) trace player| ≤ CImpl player)
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility matchingPenniesMachine
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |(WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)
          |>.game.utility outcome player| ≤ CFrontier player)
    {profile : matchingPenniesChecked.BehavioralFrontierProfile}
    (hNash :
      (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)
        |>.game.IsNash profile) :
    (matchingPenniesDoubleAuditedBehavioralAdequacy law)
      |>.implTraceGame.IsNash profile := by
  exact
    (matchingPenniesDoubleAuditedBehavioralAdequacy law)
      |>.implTraceGame_nash_of_surface_nash
        hbdImpl hbdSpec hbdFrontier hNash

/-! ## Audited encoded-runtime composition -/

/-- Composition can put administrative audit ticks below a non-identity
encoded runtime refinement. -/
noncomputable def auditedEncodedRefinement :
    Machine.StochasticRefinement (Machine.audited encodedImplMachine)
      encodedImplMachine :=
  Machine.audited.refinement encodedImplMachine

noncomputable def auditedEncodedComposedRefinement :
    Machine.StochasticRefinement (Machine.audited encodedImplMachine)
      boolSpecMachine :=
  encodedRefinement.compose auditedEncodedRefinement

noncomputable def auditedEncodedLawLift :
    auditedEncodedComposedRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool) boolSpecLawFamily :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    encodedLawLift
    (Machine.audited.liftEventBatchLawFamily encodedImplMachine
      encodedLawLift.impl)

example (profile : ∀ _player : PUnit, Bool) :
    PMF.map auditedEncodedComposedRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            (Machine.audited encodedImplMachine) (fun _ : PUnit => Bool)
            auditedEncodedLawLift.impl (fun _ => 0) 3).outcomeKernel
          profile) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool)
          boolSpecLawFamily (fun _ => 0) 3).outcomeKernel profile) :=
  auditedEncodedComposedRefinement.eventBatchTraceKernelGame_projectTrace_eq
    auditedEncodedLawLift (fun _ => 0) 3 profile

theorem auditedEncodedTraceUtility_bound
    (player : PUnit)
    (trace : (Machine.audited encodedImplMachine).EventBatchTrace) :
    |Machine.eventBatchTraceUtility (Machine.audited encodedImplMachine)
        (fun _ => 0) trace player| ≤ 1 := by
  cases player
  rcases trace with ⟨batches, state⟩
  rcases state with ⟨encodedState, outerAudit⟩
  rcases encodedState with ⟨payload, innerAudit⟩
  cases payload with
  | none =>
      simp [Machine.eventBatchTraceUtility, Machine.audited,
        Machine.RoundView.optionOutcomeUtility, encodedImplMachine]
  | some value =>
      by_cases hdecode : decodeNat value
      · simp [Machine.eventBatchTraceUtility, Machine.audited,
          Machine.RoundView.optionOutcomeUtility, encodedImplMachine,
          hdecode]
      · simp [Machine.eventBatchTraceUtility, Machine.audited,
          Machine.RoundView.optionOutcomeUtility, encodedImplMachine,
          hdecode]

example (profile : ∀ _player : PUnit, Bool)
    (hNash :
      (Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool)
          boolSpecLawFamily (fun _ => 0) 3).IsNash profile) :
    (Machine.eventBatchTraceKernelGame
        (Machine.audited encodedImplMachine) (fun _ : PUnit => Bool)
        auditedEncodedLawLift.impl (fun _ => 0) 3).IsNash profile := by
  exact
    auditedEncodedComposedRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        auditedEncodedLawLift (fun _ => 0) 3
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedEncodedTraceUtility_bound boolSpecTraceUtility_bound hNash

end Refinement
end Examples
end Vegas

import Vegas.Core.Theorems.Claims
import Vegas.Examples.MatchingPennies

/-!
# Claim-surface smoke examples

These examples instantiate the paper-facing checked-program claims on a
concrete finite program. They are regression checks for theorem names and
dependent profile translations, not new Matching Pennies facts.
-/

namespace Vegas
namespace Examples
namespace Claims

open GameTheory

noncomputable example
    (profile : matchingPenniesChecked.PureFrontierProfile) :
    matchingPenniesChecked.frontierSemantics.pure.optionOutcomeKernel
        profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory
          matchingPenniesChecked.core)
        ((matchingPenniesChecked.frontierSemantics.pure.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile matchingPenniesChecked.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile matchingPenniesChecked.core))
          ((matchingPenniesChecked.frontierSemantics.pure.view)
            |>.legalPureToBehavioral
              (ToEventGraph.completionBound
                (ToEventGraph.compile matchingPenniesChecked.core))
              profile)) :=
  matchingPenniesChecked
    |>.claim_pure_frontier_outcome_kernel_is_source_projection profile

noncomputable example
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.frontierSemantics.behavioral.optionOutcomeKernel
        profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory
          matchingPenniesChecked.core)
        ((matchingPenniesChecked.frontierSemantics.behavioral.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile matchingPenniesChecked.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile matchingPenniesChecked.core))
          profile) :=
  matchingPenniesChecked
    |>.claim_behavioral_frontier_outcome_kernel_is_source_projection profile

noncomputable example
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  matchingPenniesChecked.claim_fosg_utility_distribution_adequacy profile

noncomputable example
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.frontierPlainEFGMachinePayoffKernelGame.udist
        (matchingPenniesChecked.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            matchingPenniesChecked.frontierSemantics.behavioral.view
            matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  matchingPenniesChecked.claim_efg_utility_distribution_adequacy profile

noncomputable example
    (profile :
      (Export.frontierPlainEFG
        matchingPenniesChecked).sourceFOSG.historyGame.Profile) :
      (Export.frontierPlainEFG matchingPenniesChecked).payoffGame.udist
        ((Export.frontierPlainEFG matchingPenniesChecked).translateProfile
          profile) =
      (Export.frontierPlainEFG
        matchingPenniesChecked).sourceFOSG.historyGame.udist profile :=
  Theorems.EFG.WFProgram.exported_frontier_plain_efg_payoff_udist_sourceFOSG
    matchingPenniesChecked profile

noncomputable example
    (profile :
      (Export.frontierPlainEFG
        matchingPenniesChecked).sourceFOSG.historyGame.Profile) :
    PMF.map (Export.frontierPlainEFG matchingPenniesChecked).efgOutcomeMap
        ((KernelGame.reindex
            (Export.frontierPlainEFG matchingPenniesChecked).playerEquiv
            (Export.frontierPlainEFG
              matchingPenniesChecked).efg.toKernelGame).outcomeKernel
          ((Export.frontierPlainEFG
            matchingPenniesChecked).efgTranslateProfile profile)) =
      (Export.frontierPlainEFG
        matchingPenniesChecked).sourceFOSG.historyGame.outcomeKernel
        profile :=
  Theorems.EFG.WFProgram.exported_frontier_plain_efg_outcomeKernel_sourceFOSG
    matchingPenniesChecked profile

noncomputable example
    (profile :
      (Export.frontierPlainEFG
        matchingPenniesChecked).sourceFOSG.historyGame.Profile) :
    (KernelGame.reindex
          (Export.frontierPlainEFG matchingPenniesChecked).playerEquiv
          (Export.frontierPlainEFG
            matchingPenniesChecked).efg.toKernelGame).udist
        ((Export.frontierPlainEFG
          matchingPenniesChecked).efgTranslateProfile profile) =
      (Export.frontierPlainEFG matchingPenniesChecked).payoffGame.udist
        ((Export.frontierPlainEFG matchingPenniesChecked).translateProfile
          profile) :=
  Theorems.EFG.WFProgram.exported_frontier_plain_efg_udist_payoffGame
    matchingPenniesChecked profile

noncomputable example
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.mixedPureFrontierGame.udist
        (matchingPenniesChecked.behavioralFrontierToMixedPure profile) =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  matchingPenniesChecked.claim_kuhn_behavioral_to_mixedPure_udist profile

example :
    matchingPenniesChecked.frontierSemantics.games.view.MenusObservable
      matchingPenniesChecked.frontierSemantics.horizon :=
  matchingPenniesChecked.claim_kuhn_uses_canonical_roundView_information

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    (WFProgram.RuntimeTraceAdequacy.implTraceGame
      (WFProgram.RuntimeTraceAdequacy.identity law)).udist
        profile =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  matchingPenniesChecked.claim_runtime_refinement_preserves_behavioral_udist
    (WFProgram.RuntimeTraceAdequacy.identity law) profile

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.pureFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.PureFrontierProfile) :
    (WFProgram.RuntimeTraceAdequacy.implTraceGame
      (WFProgram.RuntimeTraceAdequacy.identity law)).udist
        profile =
      matchingPenniesChecked.pureFrontierGame.udist profile :=
  matchingPenniesChecked.claim_runtime_refinement_preserves_pure_udist
    (WFProgram.RuntimeTraceAdequacy.identity law) profile

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.mixedPureFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.MixedPureFrontierProfile) :
    (WFProgram.RuntimeTraceAdequacy.implTraceGame
      (WFProgram.RuntimeTraceAdequacy.identity law)).udist
        profile =
      matchingPenniesChecked.mixedPureFrontierGame.udist profile :=
  matchingPenniesChecked.claim_runtime_refinement_preserves_mixed_pure_udist
    (WFProgram.RuntimeTraceAdequacy.identity law) profile

end Claims
end Examples
end Vegas

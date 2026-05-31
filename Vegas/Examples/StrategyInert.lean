import Vegas.Examples.BatchCanonicalization
import Vegas.Examples.RefinementComposition
import Vegas.Examples.BoolMessage

/-!
# Strategy-inert refinement examples

These examples isolate a small strategic-presentation step: enriching the
strategy space with payoff-irrelevant message coordinates, then reindexing
runtime law lifts through that enrichment.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

/-! The same stuttering trace game can expose an extra message coordinate in
the strategy space. Because the law ignores that coordinate, the enriched trace
game is an inert extension of the base trace game. -/

noncomputable def stutterMessageLawFamily :
    stutterMachine.EventBatchLawFamily (fun _ : PUnit => Bool × PUnit) where
  law := fun profile =>
    stutterSpecLawFamily.law (fun player => (profile player).2)
  legal := fun profile =>
    stutterSpecLawFamily.legal (fun player => (profile player).2)

noncomputable def stutterMessageInertLawFamily :
    Machine.StrategyInertLawFamily stutterMachine
      (fun _ : PUnit => PUnit) (fun _ : PUnit => Bool × PUnit)
      stutterSpecLawFamily where
  proj := fun _ strategy => strategy.2
  embed := fun _ strategy => (false, strategy)
  section_proj := by
    intro player strategy
    rfl
  enriched := stutterMessageLawFamily
  law_inert := by
    intro profile
    rfl

noncomputable def stutterMessageBatchLawLift :
    stutterBatchRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × PUnit)
      stutterMessageInertLawFamily.enriched :=
  stutterBatchLawLift.reindexInertSpec stutterMessageInertLawFamily

noncomputable def auditedStutterMessageBatchLawLift :
    auditedStutterBatchRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × PUnit)
      stutterMessageInertLawFamily.enriched :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    stutterMessageBatchLawLift
    (Machine.audited.liftEventBatchLawFamily stutterMachine
      stutterMessageBatchLawLift.impl)

example (profile : ∀ _player : PUnit, PUnit) :
    (stutterMessageInertLawFamily.enrichedTraceGame (fun _ => 0) 2).IsNash
      ((stutterMessageInertLawFamily.toInertExtension (fun _ => 0) 2)
        |>.embedProfile profile) :=
  stutterMessageInertLawFamily.nash_embedProfile (fun _ => 0) 2
    (stutterSpecGame_nash profile)

example (profile : ∀ _player : PUnit, Bool × PUnit) :
    (stutterMessageInertLawFamily.enrichedTraceGame (fun _ => 0) 2).IsNash
      profile := by
  exact
    stutterMessageInertLawFamily.nash_of_projected_nash (fun _ => 0) 2
      (stutterSpecGame_nash _)

example (profile : ∀ _player : PUnit, Bool × PUnit) :
    PMF.map auditedStutterBatchRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            (Machine.audited stutterMachine)
            (fun _ : PUnit => Bool × PUnit)
            auditedStutterMessageBatchLawLift.impl
            (fun _ => 0) 2).outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          stutterMachine (fun _ : PUnit => Bool × PUnit)
          stutterMessageInertLawFamily.enriched
          (fun _ => 0) 2).outcomeKernel profile) :=
  auditedStutterBatchRefinement.eventBatchTraceKernelGame_projectTrace_eq
    auditedStutterMessageBatchLawLift (fun _ => 0) 2 profile

example (profile : ∀ _player : PUnit, Bool × PUnit) :
    (Machine.eventBatchTraceKernelGame
        (Machine.audited stutterMachine)
        (fun _ : PUnit => Bool × PUnit)
        auditedStutterMessageBatchLawLift.impl (fun _ => 0) 2).IsNash
      profile := by
  exact
    auditedStutterBatchRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        stutterMessageInertLawFamily auditedStutterMessageBatchLawLift
        (fun _ => 0) 2
        (CImpl := fun _ => 0) (CSpec := fun _ => 0)
        auditedStutterTraceUtility_bound stutterTraceUtility_bound
        (stutterSpecGame_nash _)

/-! ## Nontrivial Bool-strategy inert enrichment over audited encoded runtime -/

noncomputable def auditedEncodedMessageLawLift :
    auditedEncodedComposedRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolMessageSpecInertLawFamily.enriched :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    encodedMessageLawLift
    (Machine.audited.liftEventBatchLawFamily encodedImplMachine
      encodedMessageLawLift.impl)

example (message : Bool) :
    PMF.map auditedEncodedComposedRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            (Machine.audited encodedImplMachine)
            (fun _ : PUnit => Bool × Bool)
            auditedEncodedMessageLawLift.impl
            (fun _ => 0) 3).outcomeKernel
          (fun _ : PUnit => (message, true))) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool × Bool)
          boolMessageSpecInertLawFamily.enriched
          (fun _ => 0) 3).outcomeKernel
        (fun _ : PUnit => (message, true))) :=
  auditedEncodedComposedRefinement.eventBatchTraceKernelGame_projectTrace_eq
    auditedEncodedMessageLawLift (fun _ => 0) 3
    (fun _ : PUnit => (message, true))

example (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        (Machine.audited encodedImplMachine)
        (fun _ : PUnit => Bool × Bool)
        auditedEncodedMessageLawLift.impl (fun _ => 0) 3).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    auditedEncodedComposedRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        boolMessageSpecInertLawFamily auditedEncodedMessageLawLift
        (fun _ => 0) 3
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedEncodedTraceUtility_bound boolSpecTraceUtility_bound
        boolSpecTraceGame_true_nash_three

end Refinement
end Examples
end Vegas

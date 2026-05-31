import Vegas.Examples.Refinement

/-!
# Bool message-strategy fixture

This module keeps the nontrivial `Bool × Bool` inert-strategy fixture separate
from the stutter/batch examples. The first coordinate is a payoff-irrelevant
message; the second is the real Bool action.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

noncomputable def boolMessageSpecLawFamily :
    boolSpecMachine.EventBatchLawFamily (fun _ : PUnit => Bool × Bool) where
  law := fun profile =>
    boolSpecLawFamily.law (fun player => (profile player).2)
  legal := fun profile =>
    boolSpecLawFamily.legal (fun player => (profile player).2)

noncomputable def encodedMessageImplLawFamily :
    encodedImplMachine.EventBatchLawFamily (fun _ : PUnit => Bool × Bool) where
  law := fun profile =>
    encodedImplLawFamily.law (fun player => (profile player).2)
  legal := fun profile =>
    encodedImplLawFamily.legal (fun player => (profile player).2)

noncomputable def boolMessageSpecInertLawFamily :
    Machine.StrategyInertLawFamily boolSpecMachine
      (fun _ : PUnit => Bool) (fun _ : PUnit => Bool × Bool)
      boolSpecLawFamily where
  proj := fun _ strategy => strategy.2
  embed := fun _ strategy => (false, strategy)
  section_proj := by
    intro player strategy
    rfl
  enriched := boolMessageSpecLawFamily
  law_inert := by
    intro profile
    rfl

noncomputable def encodedMessageImplInertLawFamily :
    Machine.StrategyInertLawFamily encodedImplMachine
      (fun _ : PUnit => Bool) (fun _ : PUnit => Bool × Bool)
      encodedLawLift.impl where
  proj := fun _ strategy => strategy.2
  embed := fun _ strategy => (false, strategy)
  section_proj := by
    intro player strategy
    rfl
  enriched := encodedMessageImplLawFamily
  law_inert := by
    intro profile
    rfl

noncomputable def encodedMessageLawLift :
    encodedRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolMessageSpecInertLawFamily.enriched :=
  encodedLawLift.reindexInert
    boolMessageSpecInertLawFamily
    encodedMessageImplInertLawFamily
    (by intro player strategy; rfl)

theorem boolSpecTraceGame_outcomeKernel_two
    (profile : ∀ _player : PUnit, Bool) :
    ((Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolSpecLawFamily (fun _ => 0) 2).outcomeKernel profile) =
      PMF.pure
        ([[.play PUnit.unit (profile PUnit.unit)]],
          some (profile PUnit.unit)) := by
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom, boolSpecLawFamily, boolSpecMachine,
    Machine.runEventBatchesFrom, Machine.runEventsFrom, Machine.step]

theorem boolSpecTraceGame_outcomeKernel_three
    (profile : ∀ _player : PUnit, Bool) :
    ((Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolSpecLawFamily (fun _ => 0) 3).outcomeKernel profile) =
      PMF.pure
        ([[.play PUnit.unit (profile PUnit.unit)]],
          some (profile PUnit.unit)) := by
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom, boolSpecLawFamily, boolSpecMachine,
    Machine.runEventBatchesFrom, Machine.runEventsFrom, Machine.step]

theorem boolSpecTraceGame_eu_two
    (profile : ∀ _player : PUnit, Bool) :
    (Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolSpecLawFamily (fun _ => 0) 2).eu profile PUnit.unit =
      if profile PUnit.unit then 1 else 0 := by
  unfold KernelGame.eu
  rw [boolSpecTraceGame_outcomeKernel_two]
  change
    Math.Probability.expect
        (PMF.pure
          (([[.play PUnit.unit (profile PUnit.unit)]],
            some (profile PUnit.unit)) :
            boolSpecMachine.EventBatchTrace))
        (fun trace =>
          Machine.eventBatchTraceUtility boolSpecMachine (fun _ => 0)
            trace PUnit.unit) =
      if profile PUnit.unit then 1 else 0
  simp [Machine.eventBatchTraceUtility, boolSpecMachine,
    Machine.RoundView.optionOutcomeUtility]

theorem boolSpecTraceGame_eu_three
    (profile : ∀ _player : PUnit, Bool) :
    (Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolSpecLawFamily (fun _ => 0) 3).eu profile PUnit.unit =
      if profile PUnit.unit then 1 else 0 := by
  unfold KernelGame.eu
  rw [boolSpecTraceGame_outcomeKernel_three]
  change
    Math.Probability.expect
        (PMF.pure
          (([[.play PUnit.unit (profile PUnit.unit)]],
            some (profile PUnit.unit)) :
            boolSpecMachine.EventBatchTrace))
        (fun trace =>
          Machine.eventBatchTraceUtility boolSpecMachine (fun _ => 0)
            trace PUnit.unit) =
      if profile PUnit.unit then 1 else 0
  simp [Machine.eventBatchTraceUtility, boolSpecMachine,
    Machine.RoundView.optionOutcomeUtility]

theorem boolSpecTraceGame_true_nash :
    (Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolSpecLawFamily (fun _ => 0) 2).IsNash
      (fun _ => true) := by
  intro player alternative
  cases player
  cases alternative <;>
    simp [boolSpecTraceGame_eu_two, Function.update]

theorem boolSpecTraceGame_true_nash_three :
    (Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolSpecLawFamily (fun _ => 0) 3).IsNash
      (fun _ => true) := by
  intro player alternative
  cases player
  cases alternative <;>
    simp [boolSpecTraceGame_eu_three, Function.update]

example (message : Bool) :
    (boolMessageSpecInertLawFamily.enrichedTraceGame (fun _ => 0) 2).IsNash
      (fun _ : PUnit => (message, true)) :=
  boolMessageSpecInertLawFamily.nash_of_projected_nash (fun _ => 0) 2
    boolSpecTraceGame_true_nash

example (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        encodedImplMachine (fun _ : PUnit => Bool × Bool)
        encodedMessageLawLift.impl (fun _ => 0) 2).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    encodedRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        boolMessageSpecInertLawFamily encodedMessageLawLift
        (fun _ => 0) 2
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        encodedImplTraceUtility_bound boolSpecTraceUtility_bound
        boolSpecTraceGame_true_nash

end Refinement
end Examples
end Vegas

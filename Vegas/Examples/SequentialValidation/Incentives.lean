/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SequentialValidation.Symmetry

/-! # Continuation payoffs of the validation source game -/

noncomputable section

namespace Vegas.Examples.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

/-- Only the private input and two public publication results affect utility. -/
def sourceUtility (matchBit : Bool) : sourceArena.State → Bool → ℝ
  | some (.inr (.inr (.inr (.inr config)))), true =>
      if (config.state.get (.there .here)).isFailure then
        if ((config.state.get .here).isSuccess ==
          config.state.get (.there (.there (.there (.there .here))))) = matchBit then 1 else 0
      else 0
  | _, _ => 0

def sourcePayoff (matchBit : Bool) (who : Bool) (history : sourceArena.History) : ℝ :=
  sourceUtility matchBit history.state who

def sourceGuessLaw (profile : Profile sourceModel.behavioralSignature)
    (info : sourceModel.InfoState true) : PMF Bool :=
  (sourceChoice profile true info).map OwnAction.disclosure

theorem source_bob_run (profile : Profile sourceModel.behavioralSignature)
    (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    (sourceModel.runBehavioralFrom profile 5
      (SourcePath.secretPublished bit dummy first second).history).map History.state =
        (sourceGuessLaw profile (sourceBobSite bit dummy first second).1).map
          (fun guess => (SourcePath.done bit dummy first second guess).state) := by
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    sourceModel sourceSingle, source_run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    SourcePath.history_state, SourcePath.state, sourceKernel, PMF.pure_bind,
    PMF.bind_map, PMF.bind_bind, sourceGuessLaw, PMF.map_comp, Function.comp_def]
  rw [← PMF.bind_pure_comp, Function.comp_def]
  simp only [sourceBobSite, InformationModel.informationSite, source_info]
  rfl

theorem source_payoff_done (matchBit bit : Bool) (dummy : PublicationResult Bool)
    (first second guess : Bool) :
    sourceUtility matchBit (SourcePath.done bit dummy first second guess).state true =
      if (first && dummy.isSuccess) || !second then
        if (guess == bit) = matchBit then 1 else 0 else 0 := by
  change (if ((secretConfig bit dummy first second).state.get .here).isFailure then
    if (((finalConfig bit dummy first second guess).state.get .here).isSuccess == bit) =
      matchBit then 1 else 0 else 0) = _
  rw [secret_publication, guess_publication]
  cases flag : (first && dummy.isSuccess) || !second <;>
    cases guess <;> simp [PublicationResult.isFailure, PublicationResult.isSuccess]

theorem source_bob_value (profile : Profile sourceModel.behavioralSignature)
    (matchBit bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    expect (sourceModel.runBehavioralFrom profile 5
      (SourcePath.secretPublished bit dummy first second).history)
        (sourcePayoff matchBit true) =
      expect (sourceGuessLaw profile (sourceBobSite bit dummy first second).1) fun guess =>
        if (first && dummy.isSuccess) || !second then
          if (guess == bit) = matchBit then 1 else 0 else 0 := by
  have same := congrArg (fun law => expect law (sourceUtility matchBit · true))
    (source_bob_run profile bit dummy first second)
  change expect (sourceModel.runBehavioralFrom profile 5 _)
    (fun history => sourceUtility matchBit history.state true) = _
  simpa only [expect_map, Function.comp_def, source_payoff_done] using same

theorem source_guess_pair (law : PMF Bool) (matchBit bit : Bool) :
    expect law (fun guess => if (guess == bit) = matchBit then (1 : ℝ) else 0) +
      expect law (fun guess => if (guess == !bit) = matchBit then (1 : ℝ) else 0) = 1 := by
  rw [← expect_add_of_finite]
  calc
    _ = expect law (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro guess _
      cases matchBit <;> cases bit <;> cases guess <;> norm_num
    _ = _ := expect_constant _ _

end Vegas.Examples.SequentialValidation

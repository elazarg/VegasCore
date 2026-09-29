/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SequentialValidation.Kernel
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Reach probabilities and source information in the validation example -/

noncomputable section

namespace Vegas.Examples.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def uniformPathKernel : SourcePath → PMF SourcePath
  | .root => (PMF.uniformOfFintype Bool).map .drawn
  | .drawn bit => (PMF.uniformOfFintype (PublicationResult Bool)).map (.bound bit)
  | .bound bit dummy => (PMF.uniformOfFintype Bool).map (.dummyPublished bit dummy)
  | .dummyPublished bit dummy first =>
      (PMF.uniformOfFintype Bool).map (.secretPublished bit dummy first)
  | .secretPublished bit dummy first second =>
      (PMF.uniformOfFintype Bool).map (.done bit dummy first second)
  | .done bit dummy first second guess => .pure (.done bit dummy first second guess)

theorem uniform_source_kernel (path : SourcePath) :
    sourceKernel uniformSourceProfile path.state =
      (uniformPathKernel path).map SourcePath.state := by
  cases path
  · simp only [SourcePath.state, sourceKernel, sourceSetup, uniformPathKernel,
      PMF.map_comp]
    rfl
  all_goals
    simp only [SourcePath.state, sourceKernel, sourceChoice, uniformSourceProfile,
      Setup.toProtocolBehavioralPolicy_map_val, Option.elim_some,
      uniformPathKernel, PMF.map_comp, PMF.pure_map]
  all_goals
    simp only [sourceSetup, sourceProgram, BehavioralPolicy.protocolAction,
      uniformSourcePolicy, Bool.false_eq_true, Bool.true_eq_false,
      Sum.elim_inl, Sum.elim_inr, dite_true, dite_false,
      PMF.map_comp, Function.comp_def, OwnAction.binding_commit, OwnAction.disclosure]
  all_goals rfl

theorem uniform_source_run (fuel : Nat) :
    (sourceModel.runBehavioral uniformSourceProfile fuel).map History.state =
      ((fun law => law.bind uniformPathKernel)^[fuel] (PMF.pure SourcePath.root)).map
        SourcePath.state := by
  change (sourceModel.runBehavioralFrom uniformSourceProfile fuel sourceArena.initHistory).map
    History.state = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    sourceModel sourceSingle, source_run_states]
  induction fuel with
  | zero => simp only [Function.iterate_zero_apply, PMF.pure_map]; rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun path _ => uniform_source_kernel path

theorem path_state_injective : Function.Injective SourcePath.state :=
  Function.LeftInverse.injective decodeSource_state

theorem source_path_length (path : SourcePath) : path.history.trace.length = path.depth := by
  cases path <;> simp [SourcePath.history, SourcePath.trace, SourcePath.depth, Trace.length]

theorem sum_publication_bool {A : Type*} [AddCommMonoid A] (f : PublicationResult Bool → A) :
    ∑ value, f value = f .failure + f (.success true) + f (.success false) := by
  rw [← PublicationResult.equivOption.symm.sum_comp]
  simp [Fintype.sum_option, PublicationResult.equivOption, add_assoc]

theorem card_publication_bool : Fintype.card (PublicationResult Bool) = 3 := by
  rw [Fintype.card_congr PublicationResult.equivOption]
  decide

theorem source_reach_secret (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    (sourceModel.historyReachWeight uniformSourceProfile (SourcePath.secretPublished bit dummy first second).history).toReal = 1 / 24 := by
  classical
  unfold ((InformationModel.historyReachWeight rw [source_path_length]).toReal)
  change ((sourceModel.runBehavioral uniformSourceProfile 4) _).toReal = _
  rw [← FinDist.prob_map_of_injective History.state source_state_injective,
    uniform_source_run, SourcePath.history_state,
    FinDist.prob_map_of_injective SourcePath.state path_state_injective]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    PMF.pure_bind, uniformPathKernel, PMF.bind_map, PMF.bind_bind]
  simp only [toReal_bind_apply, toReal_map_apply, expect_eq_sum,
    Fintype.sum_bool, sum_publication_bool, toReal_uniformOfFintype_apply,
    card_publication_bool, Fintype.card_bool]
  cases bit <;> cases dummy <;> cases first <;> cases second
  all_goals first
    | solve | norm_num
    | (rename_i value; cases value <;> norm_num)

end Vegas.Examples.SequentialValidation

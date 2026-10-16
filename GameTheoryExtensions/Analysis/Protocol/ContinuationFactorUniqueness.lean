/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Uniqueness of actual continuation factors -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] {E : ExecutionProtocol Player}
  (model : InformationModel E)

/-- The exact NEW own records and the common transition coefficient are
unique once their actual entry/final traces are fixed. A fully mixed test
profile witnesses strict positivity; it is not a likelihood premise on the
profile being analyzed. -/
theorem continuation_ownPlay_factor_unique
    (test : model.BehavioralAssessment) (mixed : test.IsFullyMixed)
    {first second : E.State} (entry : E.Trace first) (final : E.Trace second)
    (left right : ∀ who, List (model.InfoState who × E.Action who))
    (leftRecords : ∀ who, model.ownPlay who final = left who ++ model.ownPlay who entry)
    (rightRecords : ∀ who, model.ownPlay who final = right who ++ model.ownPlay who entry)
    (firstChance secondChance : ℝ)
    (firstFactor : ∀ profile : ∀ who, model.BehavioralPolicy who,
      ((model.runBehavioralFrom profile (final.length - entry.length)
        ⟨first, entry⟩) ⟨second, final⟩).toReal =
          firstChance * ∏ who, model.ownPlayReachProbability (profile who) (left who))
    (secondFactor : ∀ profile : ∀ who, model.BehavioralPolicy who,
      ((model.runBehavioralFrom profile (final.length - entry.length)
        ⟨first, entry⟩) ⟨second, final⟩).toReal =
          secondChance * ∏ who, model.ownPlayReachProbability (profile who) (right who)) :
    left = right ∧ firstChance = secondChance := by
  classical
  have sameRecords : left = right := by
    funext who
    exact List.append_cancel_right ((leftRecords who).symm.trans (rightRecords who))
  subst right
  have append (who : Player) (policy : model.BehavioralPolicy who)
      (before after : List (model.InfoState who × E.Action who)) :
      model.ownPlayReachProbability policy (before ++ after) =
        model.ownPlayReachProbability policy before *
          model.ownPlayReachProbability policy after := by
    induction before with
    | nil => simp only [List.nil_append, ownPlayReachProbability, one_mul]
    | cons record rest ih =>
        simp only [List.cons_append, ownPlayReachProbability, ih, mul_assoc]
  have eachPositive (who : Player) :
      0 < model.ownPlayReachProbability (test.strategy who) (left who) := by
    have positive := model.playerReachProbability_pos test.strategy mixed who final
    rw [model.playerReachProbability_eq_ownPlayReachProbability, leftRecords, append]
      at positive
    exact pos_of_mul_pos_left positive
      (model.ownPlayReachProbability_nonneg _ _)
  have positive : 0 < ∏ who, model.ownPlayReachProbability (test.strategy who) (left who) :=
    Finset.prod_pos fun who _ => eachPositive who
  exact ⟨rfl, mul_right_cancel₀ positive.ne'
    ((firstFactor test.strategy).symm.trans (secondFactor test.strategy))⟩

end GameTheory.Protocol.InformationModel

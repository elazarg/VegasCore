/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrefixEvidence
import VegasTests.SelectiveAssociationRestrictedProbability
import VegasTests.SelectiveAssociationRestrictedPrefixSymmetry

/-! # Probability comparison for hidden native binding flips

The tuple map preserves every raw choice of Bob and Carol. Alice's silent
prelude has equal probability after the flip; her nonprescribed binding action
can only gain probability. These inequalities use the complete bounded menus.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.Prefix

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability PrefixSymmetry

theorem related_true_false (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second)
    (successful : aliceBindingRef.get? first.application.config.store = some (.success true)) :
    aliceBindingRef.get? second.application.config.store = some (.success false) := by
  have flipped := related_aliceValue selected first second related
  change first.application.config.outputs aliceBinding = some (.success true) at successful
  change second.application.config.outputs aliceBinding = some (.success false)
  rw [flipped, successful]
  rfl

theorem carol_flip_probability (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (responses : CarolResponses)
    (different : responses.aliceBinding ≠ response alice
      ((aliceInput responses.alicePrelude responses.bobPrelude).observe app alice)) :
    (carolLaw (mixed weight nonnegative atMostOne)).prob responses ≤
      (carolLaw (mixed weight nonnegative atMostOne)).prob (flipCarol selected responses) := by
  have first := mixed_flip_silent weight nonnegative atMostOne selected alice
    (initial.recall alice) (initial.recall alice) (initial.observe app alice)
    (initial.observe app alice) rfl rfl rfl responses.alicePrelude
  have bobSame := related_guesser_input selected owner _ _
    (related_bobPrelude selected responses.alicePrelude) bob (Or.inl rfl)
    (bobPrelude_unobserved selected responses.alicePrelude)
  have recallSame := congrArg Prod.fst bobSame
  have viewSame := congrArg Prod.snd bobSame
  dsimp only at recallSame viewSame
  have ids := related_known_ids selected _ _
    (related_aliceInput selected owner responses.alicePrelude responses.bobPrelude) alice
    (aliceInput_inputRecall responses.alicePrelude responses.bobPrelude)
    (aliceInput_inputRecall (CandidateFlip.action selected responses.alicePrelude)
      responses.bobPrelude)
  have third := mixed_flip_le weight nonnegative atMostOne selected alice _ _ _ _ ids
    responses.aliceBinding different
  rw [carol_probability, carol_probability]
  dsimp only [flipCarol]
  rw [← first, recallSame, viewSame]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left third (FinDist.prob_nonneg _ _)) (FinDist.prob_nonneg _ _)

theorem bob_flip_probability (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (responses : BobResponses)
    (different : responses.beforeCarol.aliceBinding ≠ response alice
      ((aliceInput responses.beforeCarol.alicePrelude responses.beforeCarol.bobPrelude).observe
        app alice))
    (carolSame :
      ((carolInput (flipCarol selected responses.beforeCarol)).recall carol,
        (carolInput (flipCarol selected responses.beforeCarol)).observe app carol) =
      ((carolInput responses.beforeCarol).recall carol,
        (carolInput responses.beforeCarol).observe app carol)) :
    (bobLaw (mixed weight nonnegative atMostOne)).prob responses ≤
      (bobLaw (mixed weight nonnegative atMostOne)).prob (flipBob selected responses) := by
  have before := carol_flip_probability weight nonnegative atMostOne selected owner
    responses.beforeCarol different
  have recallSame := congrArg Prod.fst carolSame
  have viewSame := congrArg Prod.snd carolSame
  dsimp only at recallSame viewSame
  rw [bob_probability, bob_probability]
  dsimp only [flipBob]
  rw [recallSame, viewSame]
  exact mul_le_mul_of_nonneg_right before (FinDist.prob_nonneg _ _)

end VegasTests.SelectiveAssociation.Restricted.Prefix

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.SequentialBeliefs

/-! # Sequential equilibria with an unreachable decision information set

One common fully mixed sequence justifies the beliefs. Rationality is checked
against whole continuation policies, for both a strictly preferred response
and a hidden-bit guessing payoff where the posterior makes Bob indifferent.
-/

noncomputable section

namespace GameTheoryExtensionsTests.SequentialBeliefs

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol OffPathDisclosure SequentialCredibility

theorem rational_preferred_response : (assessment limitProfile).IsSequentiallyRationalWithin
    (fun who history => SequentialCredibility.payoff history who) 3 := by
  intro who site alternative _
  cases who
  · simp [InformationModel.BehavioralAssessment.continuationContext, Context.value,
      SequentialCredibility.payoff]
  · have siteEq := bob_site_eq site
    subst site
    change ((assessment limitProfile).continuationContext bobSite
      (fun history => reward history.state) 3).value alternative ≤
      ((assessment limitProfile).continuationContext bobSite
        (fun history => reward history.state) 3).value (choose false true true)
    rw [bob_value]
    apply FinDist.expect_le_of_forall
    intro history _
    change reward history.state ≤ 1
    cases history.state with
    | done bit guess => cases guess with
      | none => norm_num [reward]
      | some guess => cases guess <;> norm_num [reward]
    | _ => norm_num [reward]

theorem sequential_equilibrium_preferred_response :
    (assessment limitProfile).IsSequentialEquilibriumFor antichain (fun who site =>
      (assessment limitProfile).continuationContext site
        (fun history => SequentialCredibility.payoff history who) 3) :=
  ⟨rational_preferred_response, consistent⟩

theorem guessing_value (profile : Profile (model false).behavioralSignature)
    (matchBit : Bool) (alternative : (model false).BehavioralPolicy true) :
    ((assessment profile).continuationContext bobSite
      (fun history => OffPathDisclosure.payoff matchBit history true) 3).value alternative =
        1 / 2 := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value]
  change (((FinDist.uniformOfFintype (α := Bool)).map bobInformationHistory).bind _).expect _ = _
  rw [FinDist.expect_bind, FinDist.expect_map, FinDist.expect_eq_sum, Fintype.sum_bool]
  simp only [bobInformationHistory, assessment, OffPathDisclosure.payoff,
    ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model false) single,
    FinDist.prob_uniformOfFintype, Fintype.card_bool]
  rw [value_bob _ true (utility matchBit · true),
    value_bob _ false (utility matchBit · true)]
  simp only [resultLaw, FinDist.expect_map, Bool.false_eq_true, ↓reduceIte]
  have total :
      (choiceLaw (Profile.update profile true alternative) true (some false)).expect
          (fun guess => utility matchBit (.done true (some guess)) true) +
      (choiceLaw (Profile.update profile true alternative) true (some false)).expect
          (fun guess => utility matchBit (.done false (some guess)) true) = 1 := by
    rw [← FinDist.expect_add]
    calc
      _ = (choiceLaw (Profile.update profile true alternative) true (some false)).expect
          (fun _ => (1 : ℝ)) := by
        apply FinDist.expect_congr
        intro guess _
        cases matchBit <;> cases guess <;> norm_num [utility]
      _ = _ := FinDist.expect_const _ _
  norm_num only [Nat.cast_ofNat] at *
  linarith

theorem rational_guessing (matchBit : Bool) :
    (assessment limitProfile).IsSequentiallyRationalWithin
      (fun who history => OffPathDisclosure.payoff matchBit history who) 3 := by
  intro who site alternative _
  cases who
  · simp [InformationModel.BehavioralAssessment.continuationContext, Context.value,
      OffPathDisclosure.payoff, utility]
  · have siteEq := bob_site_eq site
    subst site
    change _ ≤ ((assessment limitProfile).continuationContext bobSite
      (fun history => OffPathDisclosure.payoff matchBit history true) 3).value
        ((assessment limitProfile).strategy true)
    rw [guessing_value, guessing_value]

/-- Both opposite guessing utilities share the same source assessment,
including its off-path beliefs and the single consistency witness. -/
theorem sequential_equilibrium_guessing (matchBit : Bool) :
    (assessment limitProfile).IsSequentialEquilibriumFor antichain (fun who site =>
      (assessment limitProfile).continuationContext site
        (fun history => OffPathDisclosure.payoff matchBit history who) 3) :=
  ⟨rational_guessing matchBit, consistent⟩

end GameTheoryExtensionsTests.SequentialBeliefs

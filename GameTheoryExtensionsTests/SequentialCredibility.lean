/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.OffPathDisclosureIncentives
import GameTheoryExtensions.Analysis.Protocol.Sequential

/-! # A hidden bit does not excuse an irrational off-path response

Alice observes a bit, then stops or asks Bob to choose. The bit is irrelevant
to payoffs: Alice receives zero, Bob receives one for choosing true and zero
otherwise. Alice stops and Bob prescribes false. This profile is SPE in the
hidden-bit game, but no belief system makes it sequentially rational. The
regression uses GameTheory's actual assessment-induced continuation contexts.
-/

noncomputable section

namespace GameTheoryExtensionsTests.SequentialCredibility

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol OffPathDisclosure

def reward : State → ℝ
  | .done _ (some true) => 1
  | _ => 0

def payoff (history : arena.History) (who : Bool) : ℝ :=
  if who then reward history.state else 0

theorem reward_bounded (state : State) : |reward state| ≤ 1 := by
  unfold reward
  split <;> norm_num

/-- Payoffs are bounded, so every law over histories integrates them. -/
theorem payoff_integrable (law : PMF arena.History) (who : Bool) :
    PayoffIntegrable law (payoff · who) :=
  payoffIntegrable_of_bounded _ _ (C := 1) fun history => by
    unfold payoff
    split
    · exact reward_bounded _
    · norm_num

theorem reward_integrable (law : PMF arena.History) :
    PayoffIntegrable law (fun history => reward history.state) :=
  payoffIntegrable_of_bounded _ _ (C := 1) fun _ => reward_bounded _

theorem initial_reward_zero (replacement : (model false).BehavioralPolicy true) :
    expect ((model false).runSingleMoverBehavioralFrom single
      (Profile.update (prescribed false) true replacement) 3 arena.initHistory)
      (fun history => reward history.state) = 0 := by
  rw [value_initial]
  simp [choiceLaw, Profile.update, prescribed, choose, reward, expect_bind_of_finite,
    expect_pure, expect_constant]

theorem prescribed_spe :
    (model false).IsSingleMoverBehavioralSubgamePerfect single bounded (prescribed false)
      payoff := by
  rw [InformationModel.isSingleMoverBehavioralSubgamePerfect_iff]
  intro history proper who alternative
  refine (euPreference_iff payoff who _ _ (payoff_integrable _ _) (payoff_integrable _ _)).mpr ?_
  rcases source_proper_initial_or_terminal history proper with rfl | stopped
  · cases who
    · simp [expectedUtility, payoff, expect_constant]
    · change expect ((model false).runSingleMoverBehavioralFrom single
        (Profile.update (prescribed false) true alternative) 3 arena.initHistory)
        (fun history => reward history.state) ≤
        expect ((model false).runSingleMoverBehavioralFrom single (prescribed false)
        3 arena.initHistory) (fun history => reward history.state)
      have baseline := initial_reward_zero (prescribed false true)
      rw [Profile.update_eq_self] at baseline
      rw [initial_reward_zero, baseline]
  · simp only [InformationModel.runSingleMoverBehavioralFrom,
      runRandomizedFor_of_terminal _ _ stopped]
    exact le_rfl

def bobSite : (model false).InformationSite true :=
  (model false).informationSite true (bobHistory false) false (by exact id) rfl

theorem history_at_bob (history : (model false).InformationHistory true bobSite.1) :
    ∃ bit, history.1 = bobHistory bit := by
  have info := history.2
  rw [info_state] at info
  have known : Classified history.1 := classified history.1.trace
  rcases known with same | ⟨bit, same⟩ | ⟨bit, same⟩ |
    ⟨bit, same⟩ | ⟨bit, guess, same⟩
  · rw [same] at info; cases info
  · rw [same] at info; cases info
  · exact ⟨bit, same⟩
  · rw [same] at info; cases info
  · rw [same] at info; cases info

theorem bob_value (assessment : (model false).BehavioralAssessment) (value : Bool) :
    (assessment.continuationContext bobSite (fun history => reward history.state) 3).value
      (choose false true value) = if value then 1 else 0 := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    expect_bind_tower _ _ _ (reward_integrable _)]
  calc
    _ = expect (assessment.belief true bobSite) (fun _ => if value then 1 else 0) := by
      apply expect_congr_on_support
      intro history _
      obtain ⟨bit, same⟩ := history_at_bob history
      rw [same, ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
        (model false) single, value_bob]
      cases value <;> simp [resultLaw, choiceLaw, Profile.update, choose, reward, PMF.pure_map,
        expect_pure]
    _ = _ := expect_constant _ _

/-- Even an arbitrarily chosen off-path belief cannot rationalize the threat. -/
theorem no_sequentially_rational_assessment
    (assessment : (model false).BehavioralAssessment)
    (strategy : assessment.strategy = prescribed false) :
    ¬ assessment.IsSequentiallyRationalWithin (fun who history => payoff history who) 3 := by
  intro rational
  have integrable (policy : (model false).BehavioralPolicy true) :
      (assessment.continuationContext bobSite (fun history => reward history.state) 3).IntegrableAt
        policy := reward_integrable _
  have inequality := (Context.isLocallyOptimal_iff_of_integrable (integrable _)
    fun policy _ => integrable policy).mp (rational true bobSite) (choose false true true)
      (Set.mem_univ _)
  change (assessment.continuationContext bobSite (fun history => reward history.state) 3).value
      (choose false true true) ≤
    (assessment.continuationContext bobSite (fun history => reward history.state) 3).value
      (assessment.strategy true) at inequality
  rw [strategy] at inequality
  change _ ≤ (assessment.continuationContext bobSite
    (fun history => reward history.state) 3).value (choose false true false) at inequality
  rw [bob_value, bob_value] at inequality
  norm_num at inequality

end GameTheoryExtensionsTests.SequentialCredibility

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

theorem initial_reward_zero (replacement : (model false).BehavioralPolicy true) :
    ((model false).runSingleMoverBehavioralFrom single
      (Profile.update (prescribed false) true replacement) 3 arena.initHistory).expect
      (fun history => reward history.state) = 0 := by
  rw [value_initial]
  simp [choiceLaw, Profile.update, prescribed, choose, reward, FinDist.expect_bind]

theorem prescribed_spe :
    (model false).IsBehavioralSubgamePerfect single bounded (prescribed false) payoff := by
  rw [InformationModel.isBehavioralSubgamePerfect_iff]
  intro history proper who alternative
  rcases source_proper_initial_or_terminal history proper with rfl | stopped
  · cases who
    · simp [payoff]
    · change ((model false).runSingleMoverBehavioralFrom single
        (Profile.update (prescribed false) true alternative) 3 arena.initHistory).expect
        (fun history => reward history.state) ≤
        ((model false).runSingleMoverBehavioralFrom single (prescribed false)
        3 arena.initHistory).expect (fun history => reward history.state)
      have baseline := initial_reward_zero (prescribed false true)
      rw [Profile.update_eq_self] at baseline
      rw [initial_reward_zero, baseline]
  · simp only [InformationModel.runSingleMoverBehavioralFrom,
      runRandomizedFor_of_terminal _ _ stopped, FinDist.expect_pure]
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
  rw [InformationModel.BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief true bobSite).expect (fun _ => if value then 1 else 0) := by
      apply FinDist.expect_congr
      intro history _
      obtain ⟨bit, same⟩ := history_at_bob history
      rw [same, ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
        (model false) single, value_bob]
      cases value <;> simp [resultLaw, choiceLaw, Profile.update, choose, reward]
    _ = _ := FinDist.expect_const _ _

/-- Even an arbitrarily chosen off-path belief cannot rationalize the threat. -/
theorem no_sequentially_rational_assessment
    (assessment : (model false).BehavioralAssessment)
    (strategy : assessment.strategy = prescribed false) :
    ¬ assessment.IsSequentiallyRationalWithin (fun who history => payoff history who) 3 := by
  intro rational
  have inequality := rational true bobSite (choose false true true) (Set.mem_univ _)
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

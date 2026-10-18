/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingProperSurvival
import Vegas.Examples.CommitSeedSignallingReceiptPayoff
import Vegas.Examples.CommitSeedSignallingUnilateralDelivery

/-! # Positive actual native payoff of a fixed proper late deviation -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Against any counted opponent who initially waits, an owner who waits and
uses its fixed proper late policy earns at least one quarter in the original
initialized runtime, including recovery, publication and actual audit charges. -/
theorem initialized_fixed_late_netPayoff_quarter
    (profile : ∀ who, countedModel.BehavioralPolicy who) (owner : Player)
    (selected : countedMenu.decodeProfile initial horizon scheduler profile owner =
      fixedLatePolicy owner)
    (aliceWait : countedMenu.decodeProfile initial horizon scheduler profile alice []
      (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : countedMenu.decodeProfile initial horizon scheduler profile bob []
      ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    (1 / 4 : ℝ) ≤ expect (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) horizon initialExecution)
        (fun final => netPayoff (app.finished final) owner) := by
  classical
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  let law := app.runRounds scheduler players horizon initialExecution
  let own : Set app.Execution := {final | PhaseService.BindingAccepted runtime leaks
    (originalCoordinate owner) owner final}
  let exclusive : Set app.Execution := {final | final ∈ own ∧
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate (opponent owner))
      (opponent owner) final}
  let rewarded : Set app.Execution := {final | owner ∉ final.application.current.excluded ∧
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate (opponent owner))
      (opponent owner) final}
  let excluded : Set app.Execution := {final | owner ∈ final.application.current.excluded}
  let weight (event : Set app.Execution) (final : app.Execution) : ℝ :=
    @ite ℝ (final ∈ event) (Classical.propDecidable _) 1 0
  have integrable (event : Set app.Execution) : PayoffIntegrable law (weight event) :=
    payoffIntegrable_ite_one_zero law _ (decide := fun _ => Classical.propDecidable _)
  have mean (event : Set app.Execution) : expect law (weight event) =
      (law.toOuterMeasure event).toReal := expect_indicator law event
  have contained (final : app.Execution) (reached : final ∈ law.support)
      (member : final ∈ exclusive) : final ∈ rewarded := by
    exact ⟨initialized_fixed_late_original_binding_survives profile owner selected final reached
      member.1, member.2⟩
  have rewardBound : expect law (weight exclusive) ≤ expect law (weight rewarded) := by
    apply expect_mono
    · intro final reached
      by_cases member : final ∈ exclusive
      · simp only [weight, member, contained final reached member, ite_true, le_refl]
      · simp only [weight, member, ite_false]
        split_ifs <;> norm_num
    · exact integrable exclusive
    · exact integrable rewarded
  rw [mean, mean] at rewardBound
  have exclusionBound : expect law (weight excluded) ≤
      expect law (fun final => 1 - weight own final) := by
    apply expect_mono
    · intro final reached
      by_cases accepted : final ∈ own
      · have live : final ∉ excluded :=
          initialized_fixed_late_original_binding_survives profile owner selected final reached
            accepted
        simp only [weight, live, accepted, ite_false, ite_true, sub_self, le_refl]
      · simp only [weight, accepted, ite_false, sub_zero]
        split_ifs <;> norm_num
    · exact integrable excluded
    · exact payoffIntegrable_sub (payoffIntegrable_constant law 1) (integrable own)
  rw [mean, expect_sub (payoffIntegrable_constant law 1) (integrable own), expect_constant,
    mean] at exclusionBound
  have positive := fixed_late_acceptance_probability profile owner selected aliceWait bobWait
  have quarter : (1 / 4 : ℝ) ≤ (law.toOuterMeasure exclusive).toReal := by
    by_cases left : owner = alice
    · subst owner
      have opponentEq : opponent alice = bob := by simp [opponent]
      simpa only [law, players, exclusive, own, opponentEq, Set.mem_ofPred_eq] using
        alice_fixed_late_exclusive_acceptance_quarter profile selected aliceWait bobWait
    · have right : owner = bob := by
        fin_cases owner
        · exact (left rfl).elim
        · rfl
      subst owner
      have different : bob ≠ alice := by decide
      have opponentEq : opponent bob = alice := by simp [opponent, different]
      simpa only [law, players, exclusive, own, opponentEq, Set.mem_ofPred_eq] using
        bob_fixed_late_exclusive_acceptance_quarter profile selected aliceWait bobWait
  have native := initialized_counted_netPayoff_receipt_lower_bound profile owner
  dsimp only at native
  dsimp only [law, players, own, exclusive, rewarded] at rewardBound
  dsimp only [law, players, own, excluded] at exclusionBound
  dsimp only [law, players, own, exclusive] at quarter
  linarith

end Vegas.Examples.CommitSeedSignalling

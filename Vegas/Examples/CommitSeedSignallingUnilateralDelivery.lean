/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingJointAcceptance
import Vegas.Examples.CommitSeedSignallingCorrectSeedProbability
import Vegas.Examples.CommitSeedSignallingAliceInitializedHalf

/-! # Actual unilateral delivery probabilities under fixed late play -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

/-- Alice's fixed proper late packet lands while Bob's original binding does
not with probability at least one quarter, retaining their full correlation. -/
theorem alice_fixed_late_exclusive_acceptance_quarter
    (selected : players alice = fixedLatePolicy alice)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    (1 / 4 : ℝ) ≤
      ((app.runRounds scheduler players horizon initialExecution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate alice)
          alice final ∧ ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate bob)
            bob final}).toReal := by
  classical
  let law := app.runRounds scheduler players horizon initialExecution
  let own : Set app.Execution := {final | PhaseService.BindingAccepted runtime leaks
    (originalCoordinate alice) alice final}
  let foreign : Set app.Execution := {final | PhaseService.BindingAccepted runtime leaks
    (originalCoordinate bob) bob final}
  have partition : (law.toOuterMeasure own).toReal =
      (law.toOuterMeasure {final | final ∈ own ∧ final ∉ foreign}).toReal +
        (law.toOuterMeasure {final | final ∈ own ∧ final ∈ foreign}).toReal := by
    rw [← expect_indicator law own,
      ← expect_indicator law {final | final ∈ own ∧ final ∉ foreign},
      ← expect_indicator law {final | final ∈ own ∧ final ∈ foreign},
      ← expect_add
        (payoffIntegrable_ite_one_zero law
          (fun final => final ∈ {final | final ∈ own ∧ final ∉ foreign})
          (decide := fun _ => Classical.propDecidable _))
        (payoffIntegrable_ite_one_zero law
          (fun final => final ∈ {final | final ∈ own ∧ final ∈ foreign})
          (decide := fun _ => Classical.propDecidable _))]
    apply expect_congr_on_support
    intro final _
    by_cases a : final ∈ own <;> by_cases b : final ∈ foreign <;> simp [a, b]
  have half := fixed_late_acceptance_probability profile alice selected aliceWait bobWait
  have joint := initialized_joint_acceptance_half profile aliceWait bobWait
  change (1 / 2 : ℝ) ≤ (law.toOuterMeasure own).toReal at half
  change (law.toOuterMeasure {final | final ∈ own ∧ final ∈ foreign}).toReal ≤
    (1 / 2) * (law.toOuterMeasure own).toReal at joint
  change (1 / 4 : ℝ) ≤
    (law.toOuterMeasure {final | final ∈ own ∧ final ∉ foreign}).toReal
  linarith

/-- Bob's fixed proper late packet lands while Alice's original binding does
not with probability at least one quarter. His seed stays independent of the
complete earlier physical prefix, including Alice's acceptance event. -/
theorem bob_fixed_late_exclusive_acceptance_quarter
    (selected : players bob = fixedLatePolicy bob)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    (1 / 4 : ℝ) ≤
      ((app.runRounds scheduler players horizon initialExecution).toOuterMeasure
        {final | PhaseService.BindingAccepted runtime leaks (originalCoordinate bob)
          bob final ∧ ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate alice)
            alice final}).toReal := by
  classical
  let law := app.runRounds scheduler players horizon initialExecution
  let prefixes := app.runRounds scheduler players 12 initialExecution
  let joint := bindPairLaw prefixes (app.runRounds scheduler players 52)
  let a : Set app.Execution := {final | PhaseService.BindingAccepted runtime leaks
    (originalCoordinate alice) alice final}
  let missing : Set app.Execution := {final | final ∉ a}
  let b : Set app.Execution := {final | PhaseService.BindingAccepted runtime leaks
    (originalCoordinate bob) bob final}
  have finalLaw : joint.map Prod.snd = law := by
    rw [bindPairLaw_map_snd, ← app.runRounds_add]
  have firstLaw : joint.map Prod.fst = prefixes := bindPairLaw_map_fst _ _
  have missingMass : law.toOuterMeasure missing = prefixes.toOuterMeasure missing := by
    rw [← finalLaw, ← firstLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
    ext pair
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨absent, supported⟩
      exact ⟨fun present => absent
        ((alice_acceptance_physical_joint profile aliceWait bobWait pair supported).mpr present),
        supported⟩
    · rintro ⟨absent, supported⟩
      exact ⟨fun present => absent
        ((alice_acceptance_physical_joint profile aliceWait bobWait pair supported).mp present),
        supported⟩
  have partition : (1 : ℝ) = (law.toOuterMeasure a).toReal +
      (law.toOuterMeasure missing).toReal := by
    rw [← expect_indicator law a, ← expect_indicator law missing,
      ← expect_add
        (payoffIntegrable_ite_one_zero law (fun final => final ∈ a)
          (decide := fun _ => Classical.propDecidable _))
        (payoffIntegrable_ite_one_zero law (fun final => final ∈ missing)
          (decide := fun _ => Classical.propDecidable _))]
    conv_lhs => rw [← expect_constant law 1]
    apply expect_congr_on_support
    intro final _
    by_cases present : final ∈ a <;> simp [missing, present]
  have aHalf := alice_initialized_half profile aliceWait bobWait
  change (law.toOuterMeasure a).toReal ≤ 1 / 2 at aHalf
  have missingHalf : (1 / 2 : ℝ) ≤ (prefixes.toOuterMeasure missing).toReal := by
    rw [← missingMass]
    linarith
  have weighted := bob_fixed_late_weighted_acceptance_probability profile selected
    aliceWait bobWait missing
  change (1 / 2) * (prefixes.toOuterMeasure missing).toReal ≤
    (joint.toOuterMeasure {pair | pair.1 ∈ missing ∧ pair.2 ∈ b}).toReal at weighted
  have exclusiveMass : law.toOuterMeasure {final | final ∈ b ∧ final ∈ missing} =
      joint.toOuterMeasure {pair | pair.1 ∈ missing ∧ pair.2 ∈ b} := by
    rw [← finalLaw, PMF.toOuterMeasure_map_apply]
    apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
    ext pair
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨accepted, absent⟩, supported⟩
      exact ⟨⟨fun present => absent
        ((alice_acceptance_physical_joint profile aliceWait bobWait pair supported).mpr present),
        accepted⟩, supported⟩
    · rintro ⟨⟨absent, accepted⟩, supported⟩
      exact ⟨⟨accepted, fun present => absent
        ((alice_acceptance_physical_joint profile aliceWait bobWait pair supported).mp present)⟩,
        supported⟩
  change (1 / 4 : ℝ) ≤ (law.toOuterMeasure {final | final ∈ b ∧ final ∈ missing}).toReal
  rw [exclusiveMass]
  linarith

end Counted

end Vegas.Examples.CommitSeedSignalling

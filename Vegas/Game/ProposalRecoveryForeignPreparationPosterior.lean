/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPreparationPosterior

/-! # The union of all foreign generated source-preparation failures -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

local notation "protocol" => Setup.proposalRecoveryProtocol setup
local notation "model" => Setup.proposalRecoveryModel setup

open Classical in
/-- The response floor precedes the bad rate, source pins and free weights.
The conclusion is uniform at every positive FULL genuine source input. -/
theorem exists_proposalRecovery_foreignPreparation_posterior_bound
    (finite : setup.program.FiniteBindingTypes) :
    ∃ (chance : ℝ) (length : Nat), 0 < chance ∧ chance ≤ 1 ∧
      ∀ (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1),
      ∀ (omission delivery : Set.Icc (0 : ℝ) 1),
        0 < omission.val → omission.val < 1 → 0 < delivery.val → delivery.val < 1 →
      ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
        ∀ (bad : Set.Icc (0 : ℝ) 1), 0 < bad.val → bad.val ≤ 1 / 2 →
        ∀ (pins : (pool : setup.ProposalRecoveryValuePool) →
            Option (PMF (setup.ProposalRecoveryPoolPart pool)))
          (weights : (pool : setup.ProposalRecoveryValuePool) →
            PMF (setup.ProposalRecoveryPoolPart pool))
          (assessment : (model).BehavioralAssessment),
          (∀ who (history : (protocol).History) (_running : ¬ (protocol).terminal history.state),
            assessment.strategy who ((model).infoOf who history.trace) =
              setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
                omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
                delivery.property.1 delivery.property.2
                (setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
                  pins weights) who ((model).infoOf who history.trace)) →
          InformationModel.BehavioralAssessment.IsBayesConsistent (model) assessment
            setup.proposalRecoveryModel_decisionAntichain →
        ∀ (observer : Player),
        ∀ (site : (model).InformationSite observer),
          0 < (model).informationMass assessment.strategy observer site →
          (∑ history : (model).InformationHistory observer site.1 with
            (∃ owner : Player, observer ≠ owner ∧
              setup.GeneratedPreparationHistory owner history.val),
            (assessment.belief observer site history).toReal) ≤
            (Fintype.card Player : ℝ) *
              ((Fintype.card (protocol).History : ℝ) * bad.val /
              (chance * lower ^ length)) := by
  classical
  obtain ⟨chance, length, chancePositive, chanceBounded, designated⟩ :=
    setup.exists_proposalRecovery_generatedPreparation_posterior_bound finite
  refine ⟨chance, length, chancePositive, chanceBounded, ?_⟩
  intro floor floorPositive floorBounded omission delivery omissionPositive omissionSmall
    deliveryPositive deliverySmall
  obtain ⟨lower, lowerPositive, lowerBounded, designated⟩ :=
    designated floor floorPositive floorBounded omission delivery omissionPositive omissionSmall
      deliveryPositive deliverySmall
  refine ⟨lower, lowerPositive, lowerBounded, ?_⟩
  intro bad badPositive badSmall pins weights assessment prescribed bayes observer site positive
  let cost := (Fintype.card (protocol).History : ℝ) * bad.val /
    (chance * lower ^ length)
  have costNonnegative : 0 ≤ cost := by
    dsimp only [cost]
    positivity
  let badAt (owner : Player) (history : (model).InformationHistory observer site.1) : Prop :=
    observer ≠ owner ∧ setup.GeneratedPreparationHistory owner history.val
  let mass (history : (model).InformationHistory observer site.1) :=
    (assessment.belief observer site history).toReal
  have ownerBound (owner : Player) :
      (∑ history : (model).InformationHistory observer site.1 with badAt owner history,
        mass history) ≤ cost := by
    by_cases different : observer ≠ owner
    · have filters :
          (Finset.univ.filter fun history : (model).InformationHistory observer site.1 =>
            badAt owner history) =
          (Finset.univ.filter fun history : (model).InformationHistory observer site.1 =>
            setup.GeneratedPreparationHistory owner history.val) := by
        apply Finset.filter_congr
        intro history _
        exact ⟨fun present => present.2, fun present => ⟨different, present⟩⟩
      rw [filters]
      exact designated bad badPositive badSmall pins weights assessment prescribed bayes observer
        owner different site positive
    · simpa only [badAt, different, false_and, Finset.filter_false, Finset.sum_empty] using
        costNonnegative
  have coveredAt (history : (model).InformationHistory observer site.1) :
      (if ∃ owner : Player, badAt owner history then mass history else 0) ≤
        ∑ owner : Player, if badAt owner history then mass history else 0 := by
    by_cases existsOwner : ∃ owner : Player, badAt owner history
    · obtain ⟨owner, witnessed⟩ := existsOwner
      rw [ite_eq_left ⟨owner, witnessed⟩]
      have selected := Finset.single_le_sum
        (f := fun player : Player => if badAt player history then mass history else 0)
        (s := Finset.univ) (a := owner)
        (fun player _ => by split_ifs <;> positivity) (Finset.mem_univ owner)
      simpa only [ite_eq_left witnessed] using selected
    · rw [ite_eq_right existsOwner]
      exact Finset.sum_nonneg fun owner _ => by
        split_ifs <;> positivity
  calc
    _ = ∑ history : (model).InformationHistory observer site.1,
        if ∃ owner : Player, badAt owner history then mass history else 0 := by
      exact Finset.sum_filter _ _
    _ ≤ ∑ history : (model).InformationHistory observer site.1,
        ∑ owner : Player, if badAt owner history then mass history else 0 :=
      Finset.sum_le_sum fun history _ => coveredAt history
    _ = ∑ owner : Player,
        ∑ history : (model).InformationHistory observer site.1 with badAt owner history,
          mass history := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun owner _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ _owner : Player, cost := Finset.sum_le_sum fun owner _ => ownerBound owner
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

end Vegas.SourceProgram.Setup

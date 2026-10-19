/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPreparationChance
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach
import GameTheoryExtensions.Analysis.Protocol.ProjectedBeliefTransport

/-! # Source reach accounting for an actual designated-owner repair -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

local notation "protocol" => Setup.proposalRecoveryProtocol setup
local notation "model" => Setup.proposalRecoveryModel setup

/-- Only the designated owner's word needs a floor. All other behavioral
factors cancel literally, including their arbitrarily small bad atoms. The
intrinsic chance floor concerns the fixed original initialized game. -/
theorem proposalRecovery_historyReach_le_of_designated_word
    (profile : ∀ who, (model).BehavioralPolicy who) (owner : Player)
    (original image : (protocol).History)
    (words : ∀ who, who ≠ owner →
      (model).ownPlay who original.trace = (model).ownPlay who image.trace)
    (chance : ℝ) (chancePositive : 0 < chance)
    (chanceLower : chance ≤ image.trace.transitionMass)
    (bad : ℝ) (badNonnegative : 0 ≤ bad)
    (originalWord : (model).ownPlayReachProbability (profile owner)
      ((model).ownPlay owner original.trace) ≤ bad)
    (lower : ℝ) (lowerPositive : 0 < lower) (length : Nat)
    (imageWord : lower ^ length ≤ (model).ownPlayReachProbability (profile owner)
      ((model).ownPlay owner image.trace)) :
    ((model).historyReachWeight profile original).toReal ≤
      (bad / (chance * lower ^ length)) *
        ((model).historyReachWeight profile image).toReal := by
  classical
  let common : ℝ := ∏ who ∈ Finset.univ.erase owner,
    (model).ownPlayReachProbability (profile who) ((model).ownPlay who original.trace)
  have commonNonnegative : 0 ≤ common :=
    Finset.prod_nonneg fun who _ => (model).ownPlayReachProbability_nonneg _ _
  have sameCommon : common = ∏ who ∈ Finset.univ.erase owner,
      (model).ownPlayReachProbability (profile who) ((model).ownPlay who image.trace) := by
    apply Finset.prod_congr rfl
    intro who included
    rw [words who (Finset.mem_erase.mp included).1]
  have originalFactor := proposalRecovery_historyReach_eq_transitionMass_mul_ownPlay setup profile
    original
  have imageFactor := proposalRecovery_historyReach_eq_transitionMass_mul_ownPlay setup profile
    image
  rw [← Finset.mul_prod_erase Finset.univ
    (fun who => (model).ownPlayReachProbability (profile who)
      ((model).ownPlay who original.trace)) (Finset.mem_univ owner)] at originalFactor
  rw [← Finset.mul_prod_erase Finset.univ
    (fun who => (model).ownPlayReachProbability (profile who)
      ((model).ownPlay who image.trace)) (Finset.mem_univ owner), ← sameCommon] at imageFactor
  have upper : ((model).historyReachWeight profile original).toReal ≤ bad * common := by
    rw [originalFactor]
    calc
      _ ≤ 1 * ((model).ownPlayReachProbability (profile owner)
          ((model).ownPlay owner original.trace) * common) :=
        mul_le_mul_of_nonneg_right
          (proposalRecovery_transitionMass_le_one setup original.trace)
          (mul_nonneg ((model).ownPlayReachProbability_nonneg _ _) commonNonnegative)
      _ ≤ _ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right originalWord commonNonnegative
  have imageLower : (chance * lower ^ length) * common ≤
      ((model).historyReachWeight profile image).toReal := by
    rw [imageFactor]
    calc
      _ = chance * (lower ^ length * common) := by ring
      _ ≤ image.trace.transitionMass * ((model).ownPlayReachProbability (profile owner)
          ((model).ownPlay owner image.trace) * common) :=
        mul_le_mul chanceLower (mul_le_mul_of_nonneg_right imageWord commonNonnegative)
          (mul_nonneg (pow_nonneg lowerPositive.le _) commonNonnegative)
          (le_of_lt image.trace.transitionMass_pos)
  have denominatorPositive : 0 < chance * lower ^ length :=
    mul_pos chancePositive (pow_pos lowerPositive _)
  have first := mul_le_mul_of_nonneg_left upper denominatorPositive.le
  have second := mul_le_mul_of_nonneg_left imageLower badNonnegative
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ denominatorPositive).mpr
  nlinarith [first, second]

end Vegas.SourceProgram.Setup

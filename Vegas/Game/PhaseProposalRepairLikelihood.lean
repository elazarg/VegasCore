/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalGeneratedPreparation
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach
import Vegas.Game.PhaseProposalRepairChance

/-! # Reach accounting for an actual designated-owner native repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "protocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Only the designated owner's word needs a floor. All other behavioral
factors cancel literally, including their arbitrarily small bad atoms. The
intrinsic chance floor concerns the fixed original initialized game. -/
theorem historyReach_le_of_designated_word
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
  have originalFactor := historyReach_eq_transitionMass_mul_ownPlay runtime leaks bounds initial
    horizon scheduler profile original
  have imageFactor := historyReach_eq_transitionMass_mul_ownPlay runtime leaks bounds initial
    horizon scheduler profile image
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
          (transitionMass_le_one runtime leaks bounds initial horizon scheduler original.trace)
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

end Vegas.EventGraphRuntime.PhaseProposal

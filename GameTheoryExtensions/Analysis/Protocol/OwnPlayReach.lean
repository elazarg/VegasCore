/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualRegret

/-! # Legality and support of recorded own actions -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type*} {E : ExecutionProtocol Player} (M : InformationModel E)

theorem ownPlay_mem_menu (who : Player) {state} (trace : E.Trace state)
    {observed : M.InfoState who} {action : E.Action who}
    (member : (observed, action) ∈ M.ownPlay who trace) :
    some action ∈ M.menu who observed := by
  induction trace with
  | start => cases member
  | extend prior joint legal realized ih =>
      rw [InfoSignals.ownPlay_extend] at member
      cases chosen : joint who with
      | none => rw [chosen] at member; exact ih member
      | some response =>
          rw [chosen, List.mem_cons] at member
          rcases member with same | earlier
          · cases same
            apply (M.menu_adequate who prior (some action)).mpr
            simpa only [chosen] using E.legalOption_of_legal legal who
          · exact ih earlier

theorem ownPlayReachProbability_nonneg {who : Player} (policy : M.BehavioralPolicy who)
    (record : List (M.InfoState who × E.Action who)) :
    0 ≤ M.ownPlayReachProbability policy record := by
  induction record with
  | nil => exact zero_le_one
  | cons entry prior ih => exact mul_nonneg (FinDist.prob_nonneg _ _) ih

theorem ownPlayReachProbability_pos_support {who : Player} (policy : M.BehavioralPolicy who)
    (record : List (M.InfoState who × E.Action who))
    (positive : 0 < M.ownPlayReachProbability policy record)
    {observed : M.InfoState who} {action : E.Action who}
    (member : (observed, action) ∈ record) :
    some action ∈ ((policy observed).map Subtype.val).support := by
  induction record with
  | nil => cases member
  | cons entry prior ih =>
      have first := pos_of_mul_pos_left positive
        (M.ownPlayReachProbability_nonneg policy prior)
      have rest := pos_of_mul_pos_right positive (FinDist.prob_nonneg _ _)
      rcases List.mem_cons.mp member with same | earlier
      · cases same
        exact FinDist.prob_pos_iff.mp first
      · exact ih rest earlier

variable [Fintype Player]

/-- Every own action on a positive-probability history has positive probability
under the player's behavioral policy at its recorded information state. -/
theorem ownPlay_supported_of_historyReach_pos
    (profile : ∀ who, M.BehavioralPolicy who) (who : Player)
    {state} (trace : E.Trace state)
    (positive : 0 < M.historyReachProbability profile ⟨state, trace⟩)
    {observed : M.InfoState who} {action : E.Action who}
    (member : (observed, action) ∈ M.ownPlay who trace) :
    some action ∈ ((profile who observed).map Subtype.val).support := by
  classical
  rw [M.historyReachProbability_eq_player_mul_counterfactual profile who trace,
    M.playerReachProbability_eq_ownPlayReachProbability] at positive
  have ownPositive := pos_of_mul_pos_left positive
    (M.counterfactualReachProbability_nonneg profile who trace)
  exact M.ownPlayReachProbability_pos_support (profile who) _ ownPositive member

end GameTheory.Protocol.InformationModel

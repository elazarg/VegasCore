/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Counterfactual reach at single-mover steps

A player that chooses nothing at a legal joint is inactive there, its only
local choice is nothing, and that choice has mass one under every policy
(`GameTheory.Protocol.InformationModel.choicesOfLegal_mass_eq_one_of_none`). So
at a joint where at most one player moves, the other players' factor of a focal
player is one when the mover is the focal player, and the mover's mass
otherwise (`GameTheory.Protocol.InformationModel.opponentsStepProb_eq_of_single`).
Under fully mixed play a player's own reach is positive
(`GameTheory.Protocol.InformationModel.playerReachProbability_pos`).
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)

/-- **Nothing is chosen with mass one.** A player choosing nothing at a legal
joint is inactive, so its local choice is forced. -/
theorem choicesOfLegal_mass_eq_one_of_none (policies : (player : ι) → M.BehavioralPolicy player)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) {player : ι}
    (nothing : joint.1 player = none) :
    ((policies player (M.infoOf player trace)) (M.choicesOfLegal trace joint player)).toReal =
      1 := by
  classical
  have inactive : ¬ E.active state player := by
    have legal := E.legalOption_of_legal joint.2 player
    simpa [nothing, LegalOption] using legal
  let : Subsingleton (M.Choice player (M.infoOf player trace)) :=
    ⟨fun first second => by
      apply Subtype.ext
      have firstLegal := (M.menu_adequate player trace first.1).mp first.2
      have secondLegal := (M.menu_adequate player trace second.1).mp second.2
      rw [LegalOption.eq_none_of_inactive first.1 firstLegal inactive,
        LegalOption.eq_none_of_inactive second.1 secondLegal inactive]⟩
  rw [eq_pure_of_subsingleton (policies player (M.infoOf player trace))
    (M.choicesOfLegal trace joint player)]
  simp

/-- **The other players' factor at a single-mover joint.** If every player but
`mover` chooses nothing, the factor of the players other than `who` is one when
`mover` is `who`, and `mover`'s mass otherwise. -/
theorem opponentsStepProb_eq_of_single [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player) (who : ι) {state : E.State}
    (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) (mover : ι)
    (others : ∀ player, player ≠ mover → joint.1 player = none) :
    M.opponentsStepProb policies who trace joint =
      if mover = who then 1 else
        ((policies mover (M.infoOf mover trace)) (M.choicesOfLegal trace joint mover)).toReal := by
  unfold opponentsStepProb
  split_ifs with same
  · refine Finset.prod_eq_one fun player member => ?_
    exact M.choicesOfLegal_mass_eq_one_of_none policies trace joint
      (others player (same ▸ Finset.ne_of_mem_erase member))
  · rw [Finset.prod_eq_single mover]
    · intro player _ different
      exact M.choicesOfLegal_mass_eq_one_of_none policies trace joint (others player different)
    · intro absent
      exact (absent (Finset.mem_erase.mpr ⟨same, Finset.mem_univ _⟩)).elim

/-- At a joint where nobody chooses anything, the other players' factor is
one. -/
theorem opponentsStepProb_eq_one_of_none [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player) (who : ι) {state : E.State}
    (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (nothing : ∀ player, joint.1 player = none) :
    M.opponentsStepProb policies who trace joint = 1 :=
  Finset.prod_eq_one fun player _ =>
    M.choicesOfLegal_mass_eq_one_of_none policies trace joint (nothing player)

/-- **Own reach is positive under fully mixed play.** A player choosing an
action chooses it at a decision information state, where a fully mixed policy
gives it positive mass. -/
theorem playerReachProbability_pos (strategy : (player : ι) → M.BehavioralPolicy player)
    (mixed : ∀ player (site : M.InformationSite player) choice,
      choice ∈ (strategy player site.1).support)
    (who : ι) : ∀ {state : E.State} (trace : E.Trace state),
      0 < M.playerReachProbability strategy who trace
  | _, .start => zero_lt_one
  | _, .extend (source := source) prior joint isLegal realized => by
      refine mul_pos (playerReachProbability_pos strategy mixed who prior) ?_
      unfold playerStepProb
      cases chosen : joint who with
      | none =>
          rw [M.choicesOfLegal_mass_eq_one_of_none strategy prior ⟨joint, isLegal⟩ chosen]
          exact zero_lt_one
      | some action =>
          have offered : some action ∈ M.menu who (M.infoOf who prior) := by
            have member := (M.choicesOfLegal prior ⟨joint, isLegal⟩ who).2
            change joint who ∈ _ at member
            rwa [chosen] at member
          let site : M.InformationSite who :=
            ⟨M.infoOf who prior, ⟨⟨source, prior⟩, rfl⟩, isLegal.1, action, offered⟩
          exact ENNReal.toReal_pos
            ((PMF.mem_support_iff _ _).mp (mixed who site _)) (PMF.apply_ne_top _ _)

end GameTheory.Protocol.InformationModel

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Counterfactual reach at single-mover steps

A player that chooses nothing at a legal joint is inactive there, its only
local choice is nothing, and that choice has mass one under every policy
(`GameTheory.Protocol.InformationModel.choicesOfLegal_mass_eq_one_of_none`). A
player choosing an action has the mass its policy gives that action
(`GameTheory.Protocol.InformationModel.choicesOfLegal_mass_eq_of_some`). So at a
joint where at most one player moves, the other players' factor of a focal
player is one when the mover is the focal player, and the mover's mass
otherwise (`GameTheory.Protocol.InformationModel.opponentsStepProb_eq_of_single`).
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

/-- A player choosing an action at a legal joint has the mass its policy gives
that action. -/
theorem choicesOfLegal_mass_eq_of_some (policies : (player : ι) → M.BehavioralPolicy player)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) {player : ι}
    {action : E.Action player} (chosen : joint.1 player = some action) :
    ((policies player (M.infoOf player trace)) (M.choicesOfLegal trace joint player)).toReal =
      ((PMF.map (fun choice => choice.1) (policies player (M.infoOf player trace)))
        (some action)).toReal := by
  have value : (M.choicesOfLegal trace joint player).1 = some action := chosen
  have mass := pmf_map_apply_of_injective
    (f := fun choice : M.Choice player (M.infoOf player trace) => choice.1)
    (policies player (M.infoOf player trace)) Subtype.val_injective
    (M.choicesOfLegal trace joint player)
  rw [value] at mass
  exact congrArg ENNReal.toReal mass.symm

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

end GameTheory.Protocol.InformationModel

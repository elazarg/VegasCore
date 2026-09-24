/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveRoundReachability
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Response laws of finite behavioral perturbations

The canonical finite-menu choices represent exactly the available responses.
Decoding a uniform choice is uniform on those responses, and decoding a common
behavioral perturbation gives the corresponding mixture of response laws.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def responseChoiceEquiv (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    (menu.information initial horizon scheduler).Choice who (some (past, view)) ≃
      menu.actions who past view where
  toFun choice := ⟨choice.1.getD ⟨none⟩, by
    obtain ⟨action, member, same⟩ := choice.2
    simpa only [same, Option.getD_some] using member⟩
  invFun action := ⟨some action.1, action.1, action.2, rfl⟩
  left_inv choice := by
    apply Subtype.ext
    obtain ⟨action, _, same⟩ := choice.2
    simp only [same, Option.getD_some]
  right_inv action := rfl

theorem decode_uniformPolicy (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    app.decodePolicy (menu.embedPolicy initial horizon scheduler who
      (menu.uniformPolicy initial horizon scheduler who)) past view =
        menu.uniformResponses who past view := by
  classical
  let choices := (menu.information initial horizon scheduler).Choice who (some (past, view))
  let : Fintype choices := Fintype.ofFinite _
  let : Nonempty (menu.actions who past view) :=
    ⟨⟨(menu.nonempty who past view).choose, (menu.nonempty who past view).choose_spec⟩⟩
  let equiv := menu.responseChoiceEquiv initial horizon scheduler who past view
  have uniform : (FinDist.uniformOfFintype : FinDist choices).map equiv =
      FinDist.uniformOfFintype := by
    apply FinDist.ext_of_prob
    intro action
    obtain ⟨before, rfl⟩ := equiv.surjective action
    rw [FinDist.prob_map_of_injective equiv equiv.injective]
    simp only [FinDist.prob_uniformOfFintype, Fintype.card_congr equiv]
  simp only [decodePolicy, embedPolicy, uniformPolicy, FinDist.map_comp]
  change (FinDist.uniformOfFintype : FinDist choices).map
    (fun choice => (equiv choice).1) = _
  calc
    _ = ((FinDist.uniformOfFintype : FinDist choices).map equiv).map Subtype.val :=
      (FinDist.map_comp _ _ _).symm
    _ = _ := by rw [uniform]; rfl

variable [Fintype Principal]

theorem decode_perturbedAssessment
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView) :
    menu.decodeProfile initial horizon scheduler
        (menu.perturbedAssessment initial horizon scheduler profile weight positive
          atMostOne).strategy
        who past view =
      FinDist.mix weight positive.le atMostOne (menu.uniformResponses who past view)
        (menu.decodeProfile initial horizon scheduler profile who past view) := by
  change ((FinDist.mix weight positive.le atMostOne
    (menu.uniformPolicy initial horizon scheduler who (some (past, view)))
    (profile who (some (past, view)))).map
      (menu.rawChoice initial horizon scheduler who (some (past, view)))).map _ = _
  rw [FinDist.map_mix, FinDist.map_mix]
  rw [show ((menu.uniformPolicy initial horizon scheduler who (some (past, view))).map
      (menu.rawChoice initial horizon scheduler who (some (past, view)))).map _ =
        menu.uniformResponses who past view from
    menu.decode_uniformPolicy initial horizon scheduler who past view]
  rfl

end Interaction.ReactiveApplication.ResponseMenu

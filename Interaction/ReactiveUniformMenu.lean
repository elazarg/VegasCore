/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveFiniteAssessment

/-! # Uniform finite response laws at equal raw menus -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {app : ReactiveApplication Player}
  (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Equality of the complete finite response sets gives equality of uniform
raw laws, independently of the subtype witnesses and their Fintype instances. -/
theorem uniformPolicy_map_eq_of_actions (who : Player)
    (firstPast secondPast : List app.PlayerEntry) (firstView secondView : app.PlayerView)
    (same : menu.actions who firstPast firstView = menu.actions who secondPast secondView) :
    ((menu.uniformPolicy initial horizon scheduler who (some (firstPast, firstView))).map
        Subtype.val) =
      ((menu.uniformPolicy initial horizon scheduler who (some (secondPast, secondView))).map
        Subtype.val) := by
  classical
  let N := menu.information initial horizon scheduler
  have menus : N.menu who (some (firstPast, firstView)) =
      N.menu who (some (secondPast, secondView)) := by
    change {choice | ∃ action ∈ menu.actions who firstPast firstView, choice = some action} =
      {choice | ∃ action ∈ menu.actions who secondPast secondView, choice = some action}
    rw [same]
  let := Fintype.ofFinite (N.Choice who (some (firstPast, firstView)))
  let := Fintype.ofFinite (N.Choice who (some (secondPast, secondView)))
  let equivalence : N.Choice who (some (firstPast, firstView)) ≃
      N.Choice who (some (secondPast, secondView)) :=
    Equiv.subtypeEquivRight fun choice => by rw [menus]
  have uniform : (PMF.uniformOfFintype _).map equivalence = PMF.uniformOfFintype _ := by
    ext choice
    obtain ⟨prior, rfl⟩ := equivalence.surjective choice
    rw [pmf_map_apply_of_injective _ equivalence.injective]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_congr equivalence]
  change (PMF.uniformOfFintype _).map Subtype.val =
    (PMF.uniformOfFintype _).map Subtype.val
  rw [← uniform, PMF.map_comp]
  rfl

end Interaction.ReactiveApplication.ResponseMenu

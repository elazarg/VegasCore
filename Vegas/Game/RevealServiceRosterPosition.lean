/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRoster

/-! # Locating activations within the actual roster plan -/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Locate an actual command in its expanded block and retain its exact
position after all preceding blocks. -/
theorem flatMap_position {α β : Type} (items : List α) (expand : α → List β)
    (index : Nat) (value : β) (found : (items.flatMap expand)[index]? = some value) :
    ∃ rank item offset, items[rank]? = some item ∧ (expand item)[offset]? = some value ∧
      index = ((items.take rank).flatMap expand).length + offset := by
  induction items generalizing index with
  | nil => simp at found
  | cons head rest ih =>
      simp only [List.flatMap_cons] at found
      by_cases inside : index < (expand head).length
      · rw [List.getElem?_append_left inside] at found
        exact ⟨0, head, index, rfl, found, by simp⟩
      · have outside : (expand head).length ≤ index := by omega
        rw [List.getElem?_append_right outside] at found
        obtain ⟨rank, item, offset, selected, located, position⟩ :=
          ih (index - (expand head).length) found
        refine ⟨rank + 1, item, offset, selected, located, ?_⟩
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
        omega

private theorem rosterBlock_player (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (index : Nat) (who : Player)
    (found : (rosterBlock setup rosters event)[index]? = some (.player who)) :
    ∃ slot, index = slot + 1 ∧ (rosters event)[slot]? = some who := by
  simp only [rosterBlock, List.append_assoc, List.cons_append, List.nil_append] at found
  cases index with
  | zero => cases found
  | succ index =>
      simp only [List.getElem?_cons_succ] at found
      by_cases inside : index < (rosters event).length
      · rw [List.getElem?_append_left (by simpa only [List.length_map] using inside),
          List.getElem?_map] at found
        obtain ⟨owner, selected, same⟩ := Option.map_eq_some_iff.mp found
        cases ServiceInstruction.player.inj same
        exact ⟨index, rfl, selected⟩
      · rw [List.getElem?_append_right (by simp only [List.length_map]; omega)] at found
        have member := List.mem_of_getElem? found
        cases ownership : (graph setup).actor? event <;> simp [ownership] at member

/-- A selected player response has one concrete phase and roster position.
The preceding plan contains exactly the completed phases, grant and earlier
responses of this phase. -/
theorem roster_activation_prefix (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (index : Nat) (who : Player)
    (found : (rosterPlan setup rosters)[index]? = some (.player who)) :
    ∃ event : (graph setup).EventId, ∃ slot,
      (rosters event)[slot]? = some who ∧
      index = (rosterPlanPrefix setup rosters event.val).length + 1 + slot ∧
      (rosterPlan setup rosters).take index =
        rosterPlanPrefix setup rosters event.val ++
          [.grant event] ++ ((rosters event).take slot).map ServiceInstruction.player := by
  obtain ⟨rank, event, offset, selected, located, position⟩ := flatMap_position
    (List.finRange (graph setup).order.eventCount) (rosterBlock setup rosters) index
      (.player who) found
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.getElem?_eq_getElem bound, List.getElem_finRange] at selected
  have rankEq : rank = event.val := congrArg Fin.val (Option.some.inj selected)
  obtain ⟨slot, offsetEq, player⟩ := rosterBlock_player setup rosters event offset who located
  have slotBound : slot < (rosters event).length := (List.getElem?_eq_some_iff.mp player).1
  have indexEq : index = (rosterPlanPrefix setup rosters event.val).length + 1 + slot := by
    change index = (rosterPlanPrefix setup rosters rank).length + offset at position
    rw [rankEq, offsetEq] at position
    omega
  refine ⟨event, slot, player, indexEq, ?_⟩
  obtain ⟨after, split⟩ := rosterPlan_split setup rosters event
  rw [indexEq, split, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega), show
      (rosterPlanPrefix setup rosters event.val).length + 1 + slot -
        (rosterPlanPrefix setup rosters event.val).length = slot + 1 by omega]
  simp only [rosterBlock, List.append_assoc, List.singleton_append]
  rw [List.take_append_of_le_length (by
    simp only [List.length_cons, List.length_map]; omega), List.take_succ_cons, List.map_take]

end Vegas.SourceProgram.RevealService

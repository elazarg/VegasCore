/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Each recalled response was legal and supported at its recorded view -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

theorem ownPlayFrom_concat (earlier before after : List app.PlayerEntry) :
    app.ownPlayFrom earlier (before ++ after) =
      app.ownPlayFrom (earlier ++ before) after ++ app.ownPlayFrom earlier before := by
  induction before generalizing earlier with
  | nil => simp only [List.nil_append, ownPlayFrom, List.append_nil]
  | cons entry rest ih =>
      simp only [List.cons_append, ownPlayFrom, ih, List.append_assoc, List.nil_append]

theorem recallOwnPlay_entry_mem (past : List app.PlayerEntry) (index : Nat)
    (inside : index < past.length) :
    (some (past.take index, past[index].beforeView), past[index].action) ∈
      app.recallOwnPlay past := by
  have split := List.take_append_drop index past
  rw [List.drop_eq_getElem_cons inside] at split
  unfold recallOwnPlay
  have transformed := congrArg (app.ownPlayFrom []) split
  rw [app.ownPlayFrom_concat] at transformed
  rw [← transformed]
  apply List.mem_append_left
  simp only [List.nil_append, ownPlayFrom, List.mem_append, List.mem_singleton]
  exact Or.inr trivial

namespace ResponseMenu

variable [DecidableEq Principal] {app} (menu : app.ResponseMenu)

theorem recall_entry_legal (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal)
    (history : (menu.protocol initial horizon scheduler).History)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace =
      some (past, view)) (index : Nat) (inside : index < past.length) :
    past[index].action ∈ menu.actions who (past.take index) past[index].beforeView := by
  have member := app.recallOwnPlay_entry_mem past index inside
  rw [← menu.ownPlay_of_info_some initial horizon scheduler who history past view observed]
    at member
  have legal := (menu.information initial horizon scheduler).ownPlay_mem_menu who history.trace
    member
  obtain ⟨action, legal, same⟩ := legal
  cases Option.some.inj same
  exact legal

theorem recall_entry_supported [Fintype Principal]
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) (history : (menu.protocol initial horizon scheduler).History)
    (positive : 0 < (menu.information initial horizon scheduler).historyReachProbability
      profile history)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace =
      some (past, view)) (index : Nat) (inside : index < past.length) :
    some past[index].action ∈
      ((profile who (some (past.take index, past[index].beforeView))).map Subtype.val).support := by
  have member := app.recallOwnPlay_entry_mem past index inside
  rw [← menu.ownPlay_of_info_some initial horizon scheduler who history past view observed]
    at member
  exact (menu.information initial horizon scheduler).ownPlay_supported_of_historyReach_pos
    profile who history.trace positive member

end ResponseMenu
end Interaction.ReactiveApplication

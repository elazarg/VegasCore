/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Actual history witnesses for recorded responses

Each entry of native recall identifies its original decision history, response,
and the remaining path to the current history. This includes decisions off the
support of a particular strategy; witnesses come from the legal trace itself.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

theorem ownPlayFrom_getElem (earlier past : List app.PlayerEntry) (index : Nat)
    (entry : app.PlayerEntry) (recorded : past[index]? = some entry) :
    (some (earlier ++ past.take index, entry.beforeView), entry.action) ∈
      app.ownPlayFrom earlier past := by
  induction past generalizing earlier index with
  | nil => simp only [List.getElem?_nil] at recorded; cases recorded
  | cons first rest ih =>
      cases index with
      | zero =>
          cases Option.some.inj recorded
          simp only [List.take_zero, List.append_nil, ownPlayFrom, List.mem_append,
            List.mem_singleton, or_true]
      | succ index =>
          have current := ih (earlier ++ [first]) index (by simpa using recorded)
          apply List.mem_append_left _
          simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using current

theorem recallOwnPlay_getElem (past : List app.PlayerEntry) (index : Nat)
    (entry : app.PlayerEntry) (recorded : past[index]? = some entry) :
    (some (past.take index, entry.beforeView), entry.action) ∈ app.recallOwnPlay past := by
  simpa only [recallOwnPlay, List.nil_append] using
    app.ownPlayFrom_getElem [] past index entry recorded

namespace ResponseMenu

variable {app} [DecidableEq Principal] (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- A raw recall entry is witnessed by an earlier legal decision in the same
menu game, with the exact recorded local input and selected physical response. -/
theorem recorded_response_prefix (who : Principal)
    (history : (menu.protocol initial horizon scheduler).History)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace =
      some (past, view))
    (index : Nat) (entry : app.PlayerEntry) (recorded : past[index]? = some entry) :
    ∃ (prior : (menu.protocol initial horizon scheduler).History)
      (joint : Principal → Option app.Action)
      (legal : (menu.protocol initial horizon scheduler).Legal prior.state joint)
      (next : app.ProtocolState)
      (reached : next ∈
        ((menu.protocol initial horizon scheduler).step prior.state ⟨joint, legal⟩).support)
      (fuel : Nat),
      (menu.information initial horizon scheduler).infoOf who prior.trace =
          some (past.take index, entry.beforeView) ∧
        joint who = some entry.action ∧
        (menu.protocol initial horizon scheduler).ReachesWithin fuel
          (prior.extend legal reached) history := by
  have member := app.recallOwnPlay_getElem past index entry recorded
  rw [← menu.ownPlay_of_info_some initial horizon scheduler who history past view observed]
    at member
  exact (menu.information initial horizon scheduler).ownPlay_prefix who history.trace member

/-- The recorded response is legal at precisely its recorded input; its
admissibility is independent of any selected equilibrium profile. -/
theorem recorded_response_mem (who : Principal)
    (history : (menu.protocol initial horizon scheduler).History)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace =
      some (past, view))
    (index : Nat) (entry : app.PlayerEntry) (recorded : past[index]? = some entry) :
    entry.action ∈ menu.actions who (past.take index) entry.beforeView := by
  have member := app.recallOwnPlay_getElem past index entry recorded
  rw [← menu.ownPlay_of_info_some initial horizon scheduler who history past view observed]
    at member
  have permitted := (menu.information initial horizon scheduler).ownPlay_mem_menu
    who history.trace member
  obtain ⟨response, allowed, same⟩ := permitted
  cases Option.some.inj same
  exact allowed

end ResponseMenu

end Interaction.ReactiveApplication

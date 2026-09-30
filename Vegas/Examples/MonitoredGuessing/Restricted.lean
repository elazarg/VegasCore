/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResponses
import Interaction.ReactiveMenuRestriction
import Interaction.ReactiveOwnPlay

/-! # Nested menus on the actual monitored two-publication runtime

The restricted game offers silence or the initialized matching opening at each
ordinary source decision. Early Alice must remain silent. Watcher follows its
existing response at every possible local input, including inputs reached after
ordinary deviations. The watched game restores all effective ordinary responses;
the effective game also restores Watcher's responses. All three games use the
same application, observation rule, calendar and transition function.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Protocol GameTheory.Math.Probability

abbrev normalization := nativeRuntime.reactiveNormalization nativeLeaks

abbrev effectiveMenu := nativeBounds.menu nativeRuntime nativeLeaks

def opening (who : Player) (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (event : nativeGraph.EventId) (handle : Handle nativeGraph) (value : Bool) : nativeApp.Action :=
  normalization.action who past view (nativeOpeningAction event handle value)

theorem silent_effective (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) : nativeSilent ∈ effectiveMenu.actions who past view := by
  apply (normalization.menu_mem nativeMenu who past view nativeSilent).mpr
  exact ⟨nativeSilent, native_silent_available who past view, rfl⟩

theorem opening_effective (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (event : nativeGraph.EventId) (handle : Handle nativeGraph)
    (allowed : nativeBounds.AllowsHandle handle) (value : Bool) :
    opening who past view event handle value ∈ effectiveMenu.actions who past view := by
  apply (normalization.menu_mem nativeMenu who past view _).mpr
  exact ⟨nativeOpeningAction event handle value,
    native_opening_available who past view event handle allowed value, rfl⟩

theorem watcher_effective (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) :
    nativeWatcherResponse view ∈ effectiveMenu.actions watcher past view := by
  unfold nativeWatcherResponse
  split
  · exact silent_effective watcher past view
  · rename_i message found
    apply nativeBounds.known_replay_available nativeRuntime nativeLeaks watcher past view
    refine ⟨message, ?_, rfl⟩
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_of_find?_eq_some found))

open Classical in
def ordinaryActions (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) : Finset nativeApp.Action :=
  if who = bob ∧ view.application.publicView.ownTurn? bob = some bobPublication then
    {nativeSilent, opening who past view bobPublication bobHandle true}
  else if who = alice ∧
      view.application.publicView.ownTurn? alice = some alicePublication then
    {nativeSilent, opening who past view alicePublication aliceHandle (observedAliceBit view)}
  else {nativeSilent}

theorem silent_ordinary (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) : nativeSilent ∈ ordinaryActions who past view := by
  classical
  unfold ordinaryActions
  split
  · simp
  · split <;> simp

theorem ordinary_effective (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) :
    ordinaryActions who past view ⊆ effectiveMenu.actions who past view := by
  classical
  intro action member
  unfold ordinaryActions at member
  split at member
  · rcases Finset.mem_insert.mp member with rfl | member
    · exact silent_effective who past view
    · rw [Finset.mem_singleton] at member
      subst action
      exact opening_effective who past view bobPublication bobHandle trivial true
  · split at member
    · rcases Finset.mem_insert.mp member with rfl | member
      · exact silent_effective who past view
      · rw [Finset.mem_singleton] at member
        subst action
        exact opening_effective who past view alicePublication aliceHandle trivial _
    · rw [Finset.mem_singleton] at member
      subst action
      exact silent_effective who past view

open Classical in
def restrictedMenu : nativeApp.ResponseMenu where
  actions who past view := if who = watcher then {nativeWatcherResponse view}
    else ordinaryActions who past view
  nonempty who past view := by
    split
    · exact Finset.singleton_nonempty _
    · exact ⟨nativeSilent, silent_ordinary who past view⟩

open Classical in
def watchedMenu : nativeApp.ResponseMenu where
  actions who past view := if who = watcher then {nativeWatcherResponse view}
    else effectiveMenu.actions who past view
  nonempty who past view := by
    split
    · exact Finset.singleton_nonempty _
    · exact effectiveMenu.nonempty who past view

theorem restricted_in_watched : restrictedMenu.IncludedIn watchedMenu := by
  intro who past view
  simp only [restrictedMenu, watchedMenu]
  split
  · exact fun _ member => member
  · exact ordinary_effective who past view

theorem watched_in_effective : watchedMenu.IncludedIn effectiveMenu := by
  classical
  intro who past view action member
  change action ∈ (if who = watcher then _ else _) at member
  split at member
  · rename_i same
    subst who
    rw [Finset.mem_singleton] at member
    subst action
    exact watcher_effective past view
  · exact member

abbrev restrictedArena := restrictedMenu.protocol nativeInitialLaw nativeHorizon nativeScheduler
abbrev restrictedModel := restrictedMenu.information nativeInitialLaw nativeHorizon nativeScheduler
abbrev watchedArena := watchedMenu.protocol nativeInitialLaw nativeHorizon nativeScheduler
abbrev watchedModel := watchedMenu.information nativeInitialLaw nativeHorizon nativeScheduler
abbrev effectiveArena := effectiveMenu.protocol nativeInitialLaw nativeHorizon nativeScheduler
abbrev effectiveModel := effectiveMenu.information nativeInitialLaw nativeHorizon nativeScheduler

def ordinaryRestriction : restrictedModel.ActionRestriction watchedModel :=
  restricted_in_watched.actionRestriction nativeInitialLaw nativeHorizon nativeScheduler

def watcherRestriction : watchedModel.ActionRestriction effectiveModel :=
  watched_in_effective.actionRestriction nativeInitialLaw nativeHorizon nativeScheduler

theorem restricted_decisionRecall : restrictedModel.DecisionRecall :=
  restrictedMenu.decisionRecall nativeInitialLaw nativeHorizon nativeScheduler

theorem watched_decisionRecall : watchedModel.DecisionRecall :=
  watchedMenu.decisionRecall nativeInitialLaw nativeHorizon nativeScheduler

theorem effective_decisionRecall : effectiveModel.DecisionRecall :=
  effectiveMenu.decisionRecall nativeInitialLaw nativeHorizon nativeScheduler

end Vegas.Examples.MonitoredGuessing.Restricted

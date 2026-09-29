/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService

/-! # Published watcher replays in the retained proof menu

This enlarges the finite response menu of the existing service. It adds no
runtime stage or observation. The reporting player's published-ID replays are
included alongside its prescribed response; ordinary players keep exactly the
same choices. At a clean checkpoint the prescribed response is silence.

Published replays are not yet identified with silence here. Their continuation
comparison must retain the changed private recall and wire input history.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)

open Classical in
def replayMenu : (application setup leaks).ResponseMenu where
  actions who past view :=
    (menu setup leaks bounds watcher).actions who past view ∪
      if who = watcher then publishedReplays setup leaks view else ∅
  nonempty who past view :=
    ((menu setup leaks bounds watcher).nonempty who past view).mono Finset.subset_union_left

theorem menu_in_replay :
    (menu setup leaks bounds watcher).IncludedIn (replayMenu setup leaks bounds watcher) := by
  classical
  intro who past view
  exact Finset.subset_union_left

theorem replay_in_effective :
    (replayMenu setup leaks bounds watcher).IncludedIn
      (bounds.menu (runtime setup) leaks) := by
  classical
  intro who past view response member
  rcases Finset.mem_union.mp member with original | replayed
  · exact menu_in_effective setup leaks bounds watcher who past view original
  · split at replayed
    · obtain ⟨message, published, rfl⟩ :=
        (mem_publishedReplays setup leaks view response).mp replayed
      exact ordinary_effective setup leaks bounds who past view
        (published_replay_ordinary setup leaks bounds who past view message published)
    · exact (Finset.notMem_empty _ replayed).elim

theorem replay_menu_ordinary (who : Player) (ordinary : who ≠ watcher)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (replayMenu setup leaks bounds watcher).actions who past view =
      ordinaryActions setup leaks bounds who past view := by
  classical
  simp only [replayMenu, menu, ite_eq_right ordinary, Finset.union_empty]

open Classical in
theorem replay_menu_watcher
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (replayMenu setup leaks bounds watcher).actions watcher past view =
      ((application setup leaks).reportFirstUnpublished_support_finite past view).toFinset ∪
        publishedReplays setup leaks view := by
  classical
  simp only [replayMenu, menu, ↓reduceIte]

/-- Any newly admitted physical response is an actual published replay by
the watcher. The statement also holds at unreachable local inputs. -/
theorem replay_extra_response (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (allowed : response ∈ (replayMenu setup leaks bounds watcher).actions who past view)
    (extra : response ∉ (menu setup leaks bounds watcher).actions who past view) :
    who = watcher ∧ ∃ message ∈ view.messages.ledger,
      response = ⟨some (.replay message.id)⟩ := by
  classical
  rcases Finset.mem_union.mp allowed with original | replayed
  · exact (extra original).elim
  · split at replayed
    · rename_i same
      exact ⟨same, (mem_publishedReplays setup leaks view response).mp replayed⟩
    · exact (Finset.notMem_empty _ replayed).elim

end Vegas

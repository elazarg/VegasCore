/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionLaws

/-! # Nullable continuation and deadline boundary regressions

Two sequential commit/reveal pairs suffice to check that a missing first
commitment resolves, that its reveal becomes null, and that a later player's
valid messages still execute. A separate run locks a non-null value and then
misses its reveal: public resolution changes, private storage does not.
-/

namespace InteractionTests.SealedResolution

open Interaction

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.reveal false 0, [0]⟩,
      ⟨.commit true, [0, 1]⟩, ⟨.reveal true 2, [0, 1, 2]⟩]⟩, none, 2⟩

private def missedCommit := runtime.tick (runtime.tick runtime.initial)

theorem initial_readiness :
    runtime.initial.visible.firstReady? 0 = some 0 ∧
      runtime.initial.visible.firstReady? 1 = none ∧
      runtime.initial.visible.firstReady? 2 = none := by decide

theorem deadline_not_before_boundary :
    (runtime.tick runtime.initial).visible.timeouts = [] := by decide

theorem missing_commit_resolves_without_registration :
    missedCommit.visible.timeouts = [0] ∧
      missedCommit.service.lookup (false, 0) = none ∧
      SealedProgram.accepted? missedCommit.visible.events 0 = none ∧
      missedCommit.visible.published? 1 = some none ∧
      missedCommit.visible.firstReady? 2 = some 2 := by decide

private def registerLater : SealedResolution.ApplicationState Bool (Option Bool) :=
  { missedCommit with service := (missedCommit.service.sealValue true 2 (some true)).state }

private def laterAccepted :=
  runtime.handle registerLater ⟨(true, 0), .commitment 2 (true, 2)⟩

private def laterOpened := laterAccepted.bind fun state =>
  runtime.handle state ⟨(true, 1), .opening 3 (true, 2) (some true)⟩

theorem later_play_survives_default :
    (laterOpened.map fun state =>
      (state.visible.published? 1, state.visible.published? 3, state.visible.timeouts)) =
        some (some none, some (some true), [0]) := by decide

theorem late_commit_rejected :
    (runtime.handle missedCommit ⟨(false, 1), .commitment 0 (false, 0)⟩).isNone = true := by
  decide

private def registered : SealedResolution.ApplicationState Bool (Option Bool) :=
  { runtime.initial with
    service := (runtime.initial.service.sealValue false 0 (some true)).state }

private def accepted := runtime.handle registered ⟨(false, 0), .commitment 0 (false, 0)⟩

private def missedOpening := accepted.map fun state => runtime.tick (runtime.tick state)

theorem missing_opening_preserves_locked_value :
    (missedOpening.map fun state =>
      (state.service.lookup (false, 0), state.visible.published? 1, state.visible.timeouts)) =
        some (some (some true), some none, [1]) := by decide

theorem late_opening_rejected :
    (missedOpening.bind fun state =>
      runtime.handle state ⟨(false, 1), .opening 1 (false, 0) (some true)⟩).isNone = true := by
  decide

private def sealedNull : SealedResolution.ApplicationState Bool (Option Bool) :=
  { runtime.initial with service := (runtime.initial.service.sealValue false 0 none).state }

theorem sealed_null_is_occupied_not_absent :
    sealedNull.service.lookup (false, 0) = some none ∧
      (runtime.handle sealedNull ⟨(false, 0), .commitment 0 (false, 0)⟩).isSome = true ∧
      (runtime.handle sealedNull ⟨(false, 0), .cleartext 0 none⟩).isNone = true := by decide

end InteractionTests.SealedResolution

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveNormalRecall
import Vegas.Pending.ExclusionCountMenu

/-! # Recovery menus ignore ineffective private response distinctions

Readiness-token masking does not change which raw submissions are bounded.
Their menus depend on recalled signed outputs, so normalizing private response
names preserves all future raw menus.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph)

theorem rawMenu_eq_of_outputs (who : Player)
    (first second : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (same : (runtime.recoveryApplication leaks).outputs first =
      (runtime.recoveryApplication leaks).outputs second) :
    (rawMenu runtime leaks bounds).actions who first view =
      (rawMenu runtime leaks bounds).actions who second view := by
  classical
  have known : ReactiveApplication.ResponseMenu.knownPackets
      (app := runtime.recoveryApplication leaks) first view =
      ReactiveApplication.ResponseMenu.knownPackets
        (app := runtime.recoveryApplication leaks) second view := by
    simp only [ReactiveApplication.ResponseMenu.knownPackets, same]
  ext response
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  cases response.transmission with
  | none => rfl
  | some submission => simp only [known]

theorem rawMenu_recall (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView) :
    (rawMenu runtime leaks bounds).actions who
        ((normalization runtime leaks).recall who past) view =
      (rawMenu runtime leaks bounds).actions who past view :=
  rawMenu_eq_of_outputs runtime leaks bounds who _ _ view
    ((normalization runtime leaks).recall_outputs who past)

end Vegas.EventGraphRuntime.Recovery

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveNormalRecall
import Vegas.Pending.ReactiveFiniteResponses

/-! # The finite native menus ignore private response aliases

The raw menu depends on remembered outputs, leaked packets and the ledger.
Replacing earlier responses by their normal forms therefore changes neither
the current raw menu nor its normal forms. Distinct emitted packets remain
distinct: this only removes ineffective private submission metadata.

These are the operational premises for lifting a sequential equilibrium through
private action splitting. They do not themselves prove equilibrium transport.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem rawMenu_eq_of_outputs (who : Player)
    (first second : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (same : (runtime.reactiveApplication leaks).outputs first =
      (runtime.reactiveApplication leaks).outputs second) :
    (bounds.rawMenu runtime leaks).actions who first view =
      (bounds.rawMenu runtime leaks).actions who second view := by
  classical
  have known : ReactiveApplication.ResponseMenu.knownPackets
      (app := runtime.reactiveApplication leaks) first view =
      ReactiveApplication.ResponseMenu.knownPackets
        (app := runtime.reactiveApplication leaks) second view := by
    simp only [ReactiveApplication.ResponseMenu.knownPackets, same]
  ext response
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  cases response.transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => simp only [known]
      | replay id =>
          change (∃ message ∈ ReactiveApplication.ResponseMenu.knownPackets
            (app := runtime.reactiveApplication leaks) first view, message.id = id) ↔ _
          rw [known]
          rfl

theorem rawMenu_recall (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.rawMenu runtime leaks).actions who
        ((runtime.reactiveNormalization leaks).recall who past) view =
      (bounds.rawMenu runtime leaks).actions who past view :=
  bounds.rawMenu_eq_of_outputs runtime leaks who _ _ view
    ((runtime.reactiveNormalization leaks).recall_outputs who past)

theorem menu_recall (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.menu runtime leaks).actions who
        ((runtime.reactiveNormalization leaks).recall who past) view =
      (bounds.menu runtime leaks).actions who past view := by
  classical
  change ((bounds.rawMenu runtime leaks).actions who
      ((runtime.reactiveNormalization leaks).recall who past) view).image _ = _
  rw [bounds.rawMenu_recall]
  congr 1
  funext response
  exact (runtime.reactiveNormalization leaks).action_recall who past view response

end Vegas.EventGraphRuntime.MessageBounds

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveNormalRecall
import Vegas.Pending.ReactiveFiniteResponses

/-! # The finite native menus ignore private response aliases

The raw menu depends on remembered outputs, leaked packets and the ledger.
Replacing earlier responses by their normal forms therefore changes neither
the current raw menu nor its normal forms. Distinct emitted packets remain
distinct: only private submission representations with equal effects are merged.

These are the operational premises for lifting a sequential equilibrium through
private action splitting. They do not themselves prove equilibrium transport.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem rawMenu_eq_of_outputs (who : Player)
    (first second : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (same : ((reactiveApplication timeouts) leaks).outputs first =
      ((reactiveApplication timeouts) leaks).outputs second) :
    (bounds.rawMenu timeouts leaks).actions who first view =
      (bounds.rawMenu timeouts leaks).actions who second view := by
  classical
  have known : ReactiveApplication.ResponseMenu.knownPackets
      (app := (reactiveApplication timeouts) leaks) first view =
      ReactiveApplication.ResponseMenu.knownPackets
        (app := (reactiveApplication timeouts) leaks) second view := by
    simp only [ReactiveApplication.ResponseMenu.knownPackets, same]
  ext response
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  cases response.transmission with
  | none => rfl
  | some submission => simp only [known]

theorem rawMenu_recall (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (bounds.rawMenu timeouts leaks).actions who
        (((reactiveNormalization timeouts) leaks).logs who past) view =
      (bounds.rawMenu timeouts leaks).actions who past view :=
  bounds.rawMenu_eq_of_outputs timeouts leaks who _ _ view
    (((reactiveNormalization timeouts) leaks).recall_outputs who past)

end Vegas.EventGraphRuntime.MessageBounds

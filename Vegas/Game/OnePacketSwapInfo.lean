/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapRecord

/-! # The information state of a swapped history

A hidden swap acts on an information state of the one-packet game entry by entry
on the recall and on the current view (`Vegas.EventGraphRuntime.HiddenSwap.info`).
The image of a history under the swap symmetry is in the swapped information
state of the history, for every player (`Vegas.infoOf_mapTrace`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **The swap of an information state**: the recall entry by entry, and the
current view. -/
def EventGraphRuntime.HiddenSwap.info (swap : HiddenSwap (graph setup)) :
    (application setup timeouts leaks).Info → (application setup timeouts leaks).Info :=
  Option.map fun current => (current.1.map swap.entry, swap.view current.2)

/-- Swapping an information state twice gives it back. -/
theorem EventGraphRuntime.HiddenSwap.info_involutive (swap : HiddenSwap (graph setup)) :
    Function.Involutive (swap.info (timeouts := timeouts) (leaks := leaks)) := by
  rintro (_ | ⟨past, observed⟩)
  · rfl
  · change some ((past.map swap.entry).map swap.entry, swap.view (swap.view observed)) = _
    rw [List.map_map, swap.view_involutive]
    congr
    conv_rhs => rw [← List.map_id past]
    exact List.map_congr_left fun entry _ => swap.entry_involutive entry

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (application setup timeouts leaks).State} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler} {allowed : Set (graph setup).Inputs}

/-- **The image of a history is in the swapped information state** of every
player. -/
theorem infoOf_mapTrace (swap : HiddenSwap (graph setup))
    [InitialAcceptedCompleted (timeouts := timeouts) (leaks := leaks) initial]
    (initialClosed : ∀ state ∈ initial.support, state.config.inputs ∈ allowed →
      state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (failures : ∀ event, swap.values.ExpiryFixed event)
    (who : Player) {state : (application setup timeouts leaks).ProtocolState}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol initial horizon
      scheduler).Trace state) (guarded : SwapGuardState setup timeouts swap allowed state) :
    ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).infoOf who
      ((onePacketSwapSymmetry (timeouts := timeouts) bounds initial horizon scheduler swap
        initialClosed
        bounded failures).mapTrace trace guarded) =
      swap.info (((bounds.onePacketMenu timeouts leaks).information initial
        horizon
        scheduler).infoOf who trace) := by
  have info : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).infoOf who trace = (application setup timeouts leaks).observe who state :=
    (bounds.onePacketMenu timeouts leaks).info initial horizon scheduler who trace
  have mappedInfo : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).infoOf who ((onePacketSwapSymmetry (timeouts := timeouts) bounds initial horizon
        scheduler swap
        initialClosed bounded failures).mapTrace trace guarded) =
      (application setup timeouts leaks).observe who (swap.protocolState
        state) :=
    (bounds.onePacketMenu timeouts leaks).info initial horizon scheduler who _
  rw [mappedInfo, info]
  cases state with
  | none => rfl
  | some control =>
      change (if control.actor = some who then
          some ((control.execution.logs who).map swap.entry,
            (swap.execution control.execution).observe _ who) else none) =
        swap.info (if control.actor = some who then
          some (control.execution.logs who, control.execution.observe _ who) else none)
      split
      · rw [swap.observe_execution]
        rfl
      · rfl

end Vegas

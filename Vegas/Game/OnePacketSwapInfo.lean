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
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **The swap of an information state**: the recall entry by entry, and the
current view. -/
def EventGraphRuntime.HiddenSwap.info (swap : HiddenSwap (graph setup)) :
    (application setup runtime leaks).Info → (application setup runtime leaks).Info :=
  Option.map fun current => (current.1.map swap.entry, swap.view current.2)

/-- Swapping an information state twice gives it back. -/
theorem EventGraphRuntime.HiddenSwap.info_involutive (swap : HiddenSwap (graph setup)) :
    Function.Involutive (swap.info (runtime := runtime) (leaks := leaks)) := by
  rintro (_ | ⟨past, observed⟩)
  · rfl
  · change some ((past.map swap.entry).map swap.entry, swap.view (swap.view observed)) = _
    rw [List.map_map, swap.view_involutive]
    congr
    conv_rhs => rw [← List.map_id past]
    exact List.map_congr_left fun entry _ => swap.entry_involutive entry

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (application setup runtime leaks).State} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler} {allowed : Set (graph setup).Inputs}

/-- **The image of a history is in the swapped information state** of every
player. -/
theorem infoOf_mapTrace (swap : HiddenSwap (graph setup))
    [InitialAcceptedCompleted (runtime := runtime) (leaks := leaks) initial]
    (initialClosed : ∀ state ∈ initial.support, state.config.inputs ∈ allowed →
      state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (who : Player) {state : (application setup runtime leaks).ProtocolState}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol initial horizon
      scheduler).Trace state) (guarded : SwapGuardState setup runtime swap allowed state) :
    ((bounds.onePacketMenu runtime leaks).information initial horizon
      scheduler).infoOf who
      ((onePacketSwapSymmetry (runtime := runtime) bounds initial horizon scheduler swap
        initialClosed
        bounded).mapTrace trace guarded) =
      swap.info (((bounds.onePacketMenu runtime leaks).information initial
        horizon
        scheduler).infoOf who trace) := by
  have info : ((bounds.onePacketMenu runtime leaks).information initial horizon
      scheduler).infoOf who trace = (application setup runtime leaks).observe who state :=
    (bounds.onePacketMenu runtime leaks).info initial horizon scheduler who trace
  have mappedInfo : ((bounds.onePacketMenu runtime leaks).information initial horizon
      scheduler).infoOf who ((onePacketSwapSymmetry (runtime := runtime) bounds initial horizon
        scheduler swap
        initialClosed bounded).mapTrace trace guarded) =
      (application setup runtime leaks).observe who (swap.protocolState
        state) :=
    (bounds.onePacketMenu runtime leaks).info initial horizon scheduler who _
  rw [mappedInfo, info]
  cases state with
  | none => rfl
  | some control =>
      change (if control.actor = some who then
          some ((control.execution.recall who).map swap.entry,
            (swap.execution control.execution).observe _ who) else none) =
        swap.info (if control.actor = some who then
          some (control.execution.recall who, control.execution.observe _ who) else none)
      split
      · rw [swap.observe_execution]
        rfl
      · rfl

end Vegas

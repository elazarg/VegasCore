/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapRecord

/-! # The information state of a swapped history

A hidden swap acts on an information state of the one-packet game entry by entry
on the recall and on the current view (`Vegas.EventGraphRuntime.HiddenSwap.info`).
The image of a history under the swap symmetry is in the swapped information
state of the history, for every player (`Vegas.infoOf_mapTrace`). When the swap
fixes the binding read at the player's reveal turn, the swapped information
state has the same late-delivery key (`Vegas.lateKey_swapInfo`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **The swap of an information state**: the recall entry by entry, and the
current view. -/
def EventGraphRuntime.HiddenSwap.info (swap : HiddenSwap (graph setup)) :
    (application setup leaks).Info → (application setup leaks).Info :=
  Option.map fun current => (current.1.map swap.entry, swap.view current.2)

/-- Swapping an information state twice gives it back. -/
theorem EventGraphRuntime.HiddenSwap.info_involutive (swap : HiddenSwap (graph setup)) :
    Function.Involutive (swap.info (leaks := leaks)) := by
  rintro (_ | ⟨past, observed⟩)
  · rfl
  · change some ((past.map swap.entry).map swap.entry, swap.view (swap.view observed)) = _
    rw [List.map_map, swap.view_involutive]
    congr
    conv_rhs => rw [← List.map_id past]
    exact List.map_congr_left fun entry _ => swap.entry_involutive entry

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (application setup leaks).State} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler} {allowed : Set (graph setup).Inputs}

/-- **The image of a history is in the swapped information state** of every
player. -/
theorem infoOf_mapTrace (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ initial.support, state.config.inputs ∈ allowed →
      state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (who : Player) {state : (application setup leaks).ProtocolState}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).Trace state) (guarded : SwapGuardState setup swap allowed state) :
    ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who
      ((onePacketSwapSymmetry bounds initial horizon scheduler swap initialClosed
        bounded).mapTrace trace guarded) =
      swap.info (((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
        scheduler).infoOf who trace) := by
  have info : ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who trace = (application setup leaks).observe who state :=
    (bounds.onePacketMenu (runtime setup) leaks).info initial horizon scheduler who trace
  have mappedInfo : ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who ((onePacketSwapSymmetry bounds initial horizon scheduler swap
        initialClosed bounded).mapTrace trace guarded) =
      (application setup leaks).observe who (swap.protocolState state) :=
    (bounds.onePacketMenu (runtime setup) leaks).info initial horizon scheduler who _
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

omit [Fintype Player] in
/-- **The swap keeps the late-delivery key** of an information state when it
fixes every binding read at a reveal turn of the player. -/
theorem lateKey_swapInfo (swap : HiddenSwap (graph setup)) (who : Player)
    (info : (application setup leaks).Info)
    (fixed : ∀ past observed event, info = some (past, observed) →
      observed.application.publicView.ownTurn? who = some event →
        EventGraph.ResolutionFixed swap.values event) :
    lateKey setup leaks who (swap.info info) = lateKey setup leaks who info := by
  cases info with
  | none => rfl
  | some current =>
      obtain ⟨past, observed⟩ := current
      exact swap.lateKey_swap who past observed
        (fun event turn => fixed past observed event rfl turn)

end Vegas

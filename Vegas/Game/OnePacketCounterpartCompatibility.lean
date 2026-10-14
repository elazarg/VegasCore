/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapSymmetry

/-! # Failure invariants of compatible hidden swaps

Compatibility at a binding handle forces a hidden swap to fix the binding's
failure. Consequently, the swap guard fixes failures at every completed event,
whether it completed by accepting a handle or by expiry. A swap of raw prepared
values therefore cannot repair a completed failed binding into a success.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Compatibility for every candidate includes the unopenable candidate, whose
result is failure and which a raw-value swap leaves unchanged. -/
theorem BindCompatible.expiryFixed {swap : HiddenSwap graph} {event : graph.EventId}
    {handle : Handle graph} (compatible : BindCompatible swap event handle) :
    swap.values.ExpiryFixed event := by
  intro owner payload outputEq
  simpa only [candidateResult, swapCandidate_unopenable] using
    compatible owner payload outputEq .unopenable

end Vegas.EventGraphRuntime

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every completed event has its failure fixed by a guarded hidden swap. At an
accepted binding this follows from compatibility; without an accepted handle it
is the expiry clause of the guard. -/
theorem SwapGuard.expiryFixed_of_completed {swap : HiddenSwap (graph setup)}
    {allowed : Set (graph setup).Inputs} {current : (application setup leaks).Execution}
    (guarded : SwapGuard setup swap allowed current) {event : (graph setup).EventId}
    (completed : event ∈ current.application.config.cut.completed) :
    swap.values.ExpiryFixed event := by
  cases accepted : current.application.accepted (.inr event) with
  | none => exact Classical.byContradiction fun notFixed =>
      guarded.expired event notFixed completed accepted
  | some handle => exact (guarded.compatible event handle accepted).expiryFixed

/-- At a completed binding, a guarded swap preserves whether its stored result
is failure. Involutivity gives the reverse implication as well. -/
theorem SwapGuard.value_eq_failure_iff {swap : HiddenSwap (graph setup)}
    {allowed : Set (graph setup).Inputs} {current : (application setup leaks).Execution}
    (guarded : SwapGuard setup swap allowed current) {event : (graph setup).EventId}
    (completed : event ∈ current.application.config.cut.completed)
    {owner : Player} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (value : ((graph setup).outputLayout event).Value) :
    swap.values.value (.inr event) value =
        cast (congrArg EventGraph.EventField.Value outputEq.symm) .failure ↔
      value = cast (congrArg EventGraph.EventField.Value outputEq.symm) .failure := by
  have fixed := guarded.expiryFixed_of_completed completed owner payload outputEq
  constructor
  · intro equal
    have mapped := congrArg (swap.values.value (.inr event)) equal
    exact (swap.values.value_involutive (.inr event) value).symm.trans (mapped.trans fixed)
  · intro equal
    exact (congrArg (swap.values.value (.inr event)) equal).trans fixed

end Vegas

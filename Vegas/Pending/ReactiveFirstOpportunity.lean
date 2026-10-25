/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveOwnerActivationRecall

/-! # A fresh callback fits the original inclusion window

At an actual idle execution, pointwise opportunity supplies an earlier recorded
callback whenever the clock is too late. A callback absent from the owner's
recall must therefore still fit the protected-inclusion deadline.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Only the opportunity condition at this genuine idle predecessor is needed;
the service is not assumed on other native or recovery histories. -/
theorem inclusionFitsDeadline_of_unrecalled_turn
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (ordered : graph.RevealRelaxedOrdered)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (delay bound : graph.EventId → Nat) (timely : runtime.AsyncTimely delay bound)
    (opportunity : OpportunityAt runtime leaks control.execution delay)
    (event : graph.EventId) (owner : Player) (acting : graph.actor? event = some owner)
    (ready : control.execution.application.publicView.EventReady event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (never : ∀ entry ∈ control.execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    control.execution.application.publicView.InclusionFitsDeadline runtime bound event := by
  apply PublicView.inclusionFitsDeadline_of_response_delay runtime delay bound timely _ event
    entered (by rw [acting]; rfl) activated
  by_contra late
  push Not at late
  obtain ⟨response, remembered, turn⟩ :=
    recalled_turn_of_ownerActivatedSince runtime leaks initial horizon scheduler ordered control
      trace idle event owner entered acting (opportunity event owner entered acting ready
        activated late)
  exact never response remembered turn

end Vegas.EventGraphRuntime

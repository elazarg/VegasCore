module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveOwnerActivationRecall

@[expose] public section

/-! # A fresh callback fits the original inclusion window

At an actual idle execution, pointwise opportunity supplies an earlier recorded
callback whenever the clock is too late. A callback absent from the owner's
recall must therefore still fit the protected-inclusion deadline.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Only the opportunity condition at this genuine idle predecessor is needed;
the service is not assumed on other native or recovery histories. -/
theorem inclusionFitsDeadline_of_unrecalled_turn
    (initial : PMF ((reactiveApplication timeouts) leaks).State) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (ordered : graph.RevealRelaxedOrdered)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (delay bound : graph.EventId → Nat) (timely : (AsyncTimely timeouts) delay bound)
    (opportunity : OpportunityAt timeouts leaks control.execution delay)
    (event : graph.EventId) (owner : Player) (acting : graph.actor? event = some owner)
    (ready : control.execution.application.publicView.EventReady event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (never : ∀ entry ∈ control.execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    control.execution.application.publicView.InclusionFitsDeadline timeouts bound event := by
  apply PublicView.inclusionFitsDeadline_of_response_delay timeouts delay bound timely _ event
    entered (by rw [acting]; rfl) activated
  by_contra late
  push Not at late
  obtain ⟨response, remembered, turn⟩ :=
    recalled_turn_of_ownerActivatedSince timeouts leaks initial horizon scheduler ordered control
      trace idle event owner entered acting (opportunity event owner entered acting ready
        activated late)
  exact never response remembered turn

end Vegas.EventGraphRuntime

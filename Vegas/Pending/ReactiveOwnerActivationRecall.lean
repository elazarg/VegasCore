/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveOwnerOpportunity
import Vegas.Pending.ReactiveServiceConditions

/-! # Actual owner callback records before a clear readiness deadline -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A completed scheduler activation in a readiness episode leaves an actual
owner callback whose recorded view selects that event. No service contract is
needed to turn the recorded activation into its response. -/
theorem recalled_turn_of_ownerActivatedSince (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF ((reactiveApplication timeouts) leaks).State) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (ordered : graph.RevealRelaxedOrdered)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (actor : graph.actor? event = some owner)
    (activated : (OwnerActivatedSince timeouts) leaks control.execution.environmentRecall
      event owner entered) :
    ∃ response ∈ control.execution.logs owner,
      response.beforeView.application.publicView.ownTurn? owner = some event := by
  obtain ⟨activation, recorded, command, _entered, ready⟩ := activated
  obtain ⟨before, _prefixTrace, _own, response, remembered, viewed, publicEqual⟩ :=
    (activated_owner_response_prefix timeouts) leaks initial horizon scheduler control trace idle
      activation recorded owner command
  have publicState : before.execution.application.publicView =
      activation.beforeView.application := by
    simpa only [viewed, ReactiveApplication.Execution.observe, reactiveApplication,
      State.playerView] using publicEqual
  have turn : before.execution.application.publicView.ownTurn? owner = some event := by
    apply PublicView.ownTurn?_of_ownTurn
    apply State.ownTurn_of_ready _ ordered owner event
    · rw [publicState]
      exact ready
    · exact actor
  refine ⟨response, remembered, ?_⟩
  rw [viewed]
  exact turn

/-- A due owned event has a remembered ready callback whenever its actual
execution satisfies the pointwise opportunity predicate. -/
theorem due_owner_recalled_turn_of_opportunity (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {initial : PMF ((reactiveApplication timeouts) leaks).State} {horizon : Nat}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {delay bound : graph.EventId → Nat}
    (timely : (AsyncTimely timeouts) delay bound) (ordered : graph.RevealRelaxedOrdered)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (opportunity : OpportunityAt timeouts leaks control.execution delay)
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : timeouts.duration event ≤ control.execution.application.clock - entered) :
    ∃ response ∈ control.execution.logs owner,
      response.beforeView.application.publicView.ownTurn? owner = some event := by
  have occurred := opportunity event owner entered actor
    ((control.execution.application.publicView_eventReady event).mpr ready) activated (by
      have margin := timely event (by simp only [actor, Option.isSome_some])
      omega)
  exact recalled_turn_of_ownerActivatedSince timeouts leaks initial horizon scheduler ordered
    control trace idle event owner entered actor occurred

end Vegas.EventGraphRuntime

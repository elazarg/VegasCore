/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveOwnerOpportunity
import Vegas.Pending.ExclusionService

/-! # Actual owner callback records before a clear readiness deadline -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A completed scheduler activation in a readiness episode leaves an actual
owner callback whose recorded view selects that event. No service contract is
needed to turn the recorded activation into its response. -/
theorem recalled_turn_of_ownerActivatedSince (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (ordered : graph.RevealRelaxedOrdered)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (actor : graph.actor? event = some owner)
    (activated : runtime.OwnerActivatedSince leaks control.execution.environmentRecall
      event owner entered) :
    ∃ response ∈ control.execution.recall owner,
      response.beforeView.application.publicView.ownTurn? owner = some event := by
  obtain ⟨activation, recorded, command, _entered, ready⟩ := activated
  obtain ⟨before, _prefixTrace, _own, response, remembered, viewed, publicEqual⟩ :=
    runtime.activated_owner_response_prefix leaks initial horizon scheduler control trace idle
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
theorem due_owner_recalled_turn_of_opportunity (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {initial : PMF (runtime.reactiveApplication leaks).State} {horizon : Nat}
    {scheduler : (runtime.reactiveApplication leaks).Scheduler}
    {delay bound : graph.EventId → Nat}
    (timely : runtime.AsyncTimely delay bound) (ordered : graph.RevealRelaxedOrdered)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (opportunity : OpportunityAt runtime leaks control.execution delay)
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ control.execution.application.clock - entered) :
    ∃ response ∈ control.execution.recall owner,
      response.beforeView.application.publicView.ownTurn? owner = some event := by
  have occurred := opportunity event owner entered actor
    ((control.execution.application.publicView_eventReady event).mpr ready) activated (by
      have margin := timely event (by simp only [actor, Option.isSome_some])
      omega)
  exact recalled_turn_of_ownerActivatedSince runtime leaks initial horizon scheduler ordered
    control trace idle event owner entered actor occurred

namespace Recovery

/-- At an actual public-clear native prefix, a due owned event has a remembered
ready callback under the actual recovery opportunity contract. -/
theorem due_owner_recalled_turn_clear_native (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {initial : PMF (RecoveryState graph)}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : graph.EventId → Nat}
    (opportunity : Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound) (ordered : graph.RevealRelaxedOrdered)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (idle : control.actor = none)
    (clear : ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState graph))
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ control.execution.application.clock - entered) :
    ∃ response ∈ control.execution.recall owner,
      response.beforeView.application.publicView.ownTurn? owner = some event := by
  have actual := opportunity.clear_native runtime leaks initialized control trace clear
  exact due_owner_recalled_turn_of_opportunity runtime leaks timely ordered control trace idle
    actual event owner actor ready entered activated due

end Recovery
end Vegas.EventGraphRuntime

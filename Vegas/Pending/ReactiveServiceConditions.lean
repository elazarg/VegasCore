/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveAsyncContract

/-! # Service conditions at a fixed native execution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The native opportunity condition at a fixed execution. -/
def OpportunityAt (execution : (runtime.reactiveApplication leaks).Execution)
    (delay : graph.EventId → Nat) : Prop :=
  ∀ event owner entered, graph.actor? event = some owner →
    execution.application.publicView.EventReady event →
    execution.application.activatedAt event = some entered →
    entered + delay event < execution.application.clock →
    OwnerActivatedSince runtime leaks execution.environmentRecall event owner entered

/-- The native protected-inclusion condition at a fixed execution, retaining the
same recalled-packet uniqueness and strict timing premises. -/
def ProtectedInclusionAt (execution : (runtime.reactiveApplication leaks).Execution)
    (bound : graph.EventId → Nat) : Prop :=
  ∀ event owner, graph.actor? event = some owner →
  ∀ (earlier later : List (runtime.reactiveApplication leaks).PlayerEntry) entry message,
    execution.recall owner = earlier ++ entry :: later →
    entry.emitted = some message → message.sender = owner →
    message.payload.call.event? graph = some event →
    entry.beforeView.application.publicView.EventReady event →
    (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor runtime leaks other event message.id) →
    event ∉ execution.application.config.cut.completed →
    entry.beforeView.application.publicView.clock + bound event < execution.application.clock →
    ∃ accepted, (message.id, accepted) ∈ execution.receipts

/-- A native service opportunity contract supplies its fixed-execution condition. -/
theorem Opportunity.at {initial : PMF (State graph)} {horizon : Nat}
    {scheduler : (runtime.reactiveApplication leaks).Scheduler} {delay : graph.EventId → Nat}
    (opportunity : Opportunity runtime leaks initial horizon scheduler delay)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) : OpportunityAt runtime leaks control.execution delay :=
  opportunity control trace

/-- A native inclusion contract supplies its fixed-execution condition. -/
theorem ProtectedInclusion.at {initial : PMF (State graph)} {horizon : Nat}
    {scheduler : (runtime.reactiveApplication leaks).Scheduler} {bound : graph.EventId → Nat}
    (inclusion : ProtectedInclusion runtime leaks initial horizon scheduler bound)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) : ProtectedInclusionAt runtime leaks control.execution bound :=
  inclusion control trace

end Vegas.EventGraphRuntime

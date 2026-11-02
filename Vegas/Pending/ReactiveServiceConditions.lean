/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveAsyncContract

/-! # Service conditions at a fixed native execution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

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

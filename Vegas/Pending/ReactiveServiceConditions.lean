/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveAsyncContract

/-! # Service conditions at a fixed native execution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A native service opportunity contract supplies its fixed-execution condition. -/
theorem Opportunity.at {initial : PMF (State graph)} {horizon : Nat}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler} {delay : graph.EventId → Nat}
    (opportunity : Opportunity timeouts leaks initial horizon scheduler delay)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) : OpportunityAt timeouts leaks control.execution delay :=
  opportunity control trace

/-- A native inclusion contract supplies its fixed-execution condition. -/
theorem ProtectedInclusion.at {initial : PMF (State graph)} {horizon : Nat}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler} {bound : graph.EventId → Nat}
    (inclusion : ProtectedInclusion timeouts leaks initial horizon scheduler bound)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) : ProtectedInclusionAt timeouts leaks control.execution bound :=
  inclusion control trace

end Vegas.EventGraphRuntime

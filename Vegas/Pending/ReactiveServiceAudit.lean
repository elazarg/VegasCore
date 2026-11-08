/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveSettledVerdict
import Interaction.ReactiveTrafficState
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # Collected charges for signed-traffic protocol violations

The terminal service judges authentic signed traffic against the settled
contract record. Omission and failed publication are source-game outcomes;
they retain their declared payoffs and carry no additional audit charge.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The contract's settled record at an execution: its public view and the
receipts of every inclusion. -/
def settledRecord (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution) : SettledRecord graph :=
  ⟨execution.application.publicView, execution.receipts⟩

/-- The actual traffic history and the settled record. No private value,
player response representation or unsampled absence is used. -/
def serviceAuditObservation (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : ((reactiveApplication timeouts) leaks).ProtocolState) :=
  (((reactiveApplication timeouts) leaks).stateTraffic state,
    state.map fun control => (settledRecord timeouts) leaks control.execution)

/-- One collected verdict, with arbitrary correlation between players and
arbitrary sampling inside the supplied authentic traffic audit, which may read
the settled record. Before initialization nothing is collected. -/
def serviceAudit (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : SettledRecord graph →
      List ((reactiveApplication timeouts) leaks).TrafficRecord → PMF (Player → Bool))
    (observed : List ((reactiveApplication timeouts) leaks).TrafficRecord ×
      Option (SettledRecord graph)) :
    PMF (Player → Bool) :=
  match observed.2 with
  | none => PMF.pure fun _ => false
  | some record => trafficAudit record observed.1

/-- Collection is exactly the supplied signed-traffic verdict probability.
Public source defaults introduce no additional audit charge. -/
theorem serviceAudit_charge (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : SettledRecord graph →
      List ((reactiveApplication timeouts) leaks).TrafficRecord → PMF (Player → Bool))
    (control : ((reactiveApplication timeouts) leaks).Control) (who : Player) :
    TerminalAudit.charge ((serviceAuditObservation timeouts) leaks)
        ((serviceAudit timeouts) leaks trafficAudit) (some control) who =
      ((((trafficAudit ((settledRecord timeouts) leaks control.execution)
        (((reactiveApplication timeouts) leaks).executionTraffic control.execution)).map
          (fun verdict => verdict who)) true).toReal) := rfl

end Vegas.EventGraphRuntime

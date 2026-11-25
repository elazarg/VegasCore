module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceFacts
public import Vegas.Pending.CanonicalAcceptance

@[expose] public section

/-! # Canonical source packets and their exact native effects

A transmitting canonical decision fixes its graph action and actual typed result.
Authentic openings may publish failure when public guards reject them. At every
initialized raw history, a timely canonical packet is acceptable and its recorded
response is a protected fresh call, in every dependency choice.
-/
noncomputable section

namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


section Admission
variable {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- **A canonical decision sent in time is acceptable.** At every history of
the service runtime, the canonical decision of `who` at its turn `event`,
within the event's deadline, transmits a packet the contract accepts on the
current view. -/
theorem canonicalServiceDecision_freshServiceAcceptable {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup deps).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (within : control.execution.application.publicView.WithinDeadline
      (serviceTimeouts setup deps duration) event)
    (action : (serviceGraph setup deps).Action event)
    (material : (serviceApplication setup deps duration leaks).Submission)
    (submits : ((canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks who
      (control.execution.logs who)
      (control.execution.observe (serviceApplication setup deps duration leaks) who) event
      action).transmission = some material) :
    (freshServiceAcceptable (serviceTimeouts setup deps duration))
      control.execution.application.publicView
      ⟨(who, control.execution.network.nextSerial who),
        (serviceApplication setup deps duration leaks).packet
          ((serviceApplication setup deps duration leaks).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  rw [serviceInitialDistribution_eq_inputs setup] at trace
  exact EventGraphRuntime.canonicalServiceDecision_freshServiceAcceptable
    (timeouts := serviceTimeouts setup deps duration) (leaks := leaks) (control := control)
    trace who event turn within action material submits

/-- **The recall entry of a canonical packet is a fresh call.** At every
history of the service runtime, the canonical decision of `who` at its turn
`event`, sent while an inclusion within `bound event` slots lands before the
deadline, is recorded by the response as a fresh call of `who` for `event`. -/
theorem canonical_freshCall {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace (some control))
    (bound : (serviceGraph setup deps).EventId → Nat)
    (who : Player) (event : (serviceGraph setup deps).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (fits : control.execution.application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup deps duration) bound event)
    (action : (serviceGraph setup deps).Action event)
    (material : (serviceApplication setup deps duration leaks).Submission)
    (submits : ((canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks who
      (control.execution.logs who)
      (control.execution.observe (serviceApplication setup deps duration leaks) who) event
      action).transmission = some material) :
    FreshCall (serviceTimeouts setup deps duration) leaks who event bound
      ⟨control.execution.observe (serviceApplication setup deps duration leaks) who,
        (canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks who
          (control.execution.logs who)
          (control.execution.observe (serviceApplication setup deps duration leaks) who) event
          action,
        some ⟨(who, control.execution.network.nextSerial who),
          (serviceApplication setup deps duration leaks).packet
            ((serviceApplication setup deps duration leaks).submit control.execution.application
              who material) who (control.execution.network.known who) material⟩⟩
      ⟨(who, control.execution.network.nextSerial who),
        (serviceApplication setup deps duration leaks).packet
          ((serviceApplication setup deps duration leaks).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  rw [serviceInitialDistribution_eq_inputs setup] at trace
  exact EventGraphRuntime.canonical_freshCall (timeouts := serviceTimeouts setup deps duration)
    (leaks := leaks) (control := control) trace bound who event turn fits action material submits

end Admission

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrame
import Vegas.Pending.ReactiveServiceConformance
import Vegas.Pending.ReactiveBindingOmission
import Interaction.ReactiveTrafficState

/-! # Audit evidence along a repaired binding frame

The complete existing traffic record and the public omission predicate agree
on framed executions. In particular, a new forbidden record cannot already
occur in an original prefix whose repaired retained prefix is audit-clean.
This supplies the incremental-evidence fact needed for conditional sanctions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

theorem traffic (frame : Frame runtime leaks memory owner original repaired) :
    (runtime.reactiveApplication leaks).executionTraffic original =
      (runtime.reactiveApplication leaks).executionTraffic repaired := by
  unfold ReactiveApplication.executionTraffic
  rw [frame.service, frame.environment]

theorem missedBinding (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) :
    original.application.publicView.missedBinding event =
      repaired.application.publicView.missedBinding event := by
  rw [frame.publicView]

/-- Clean retained traffic rules out an old alarm on every good branch of the
repair. The record itself may be tested against any subsequent transcript. -/
theorem forbidden_record_new (frame : Frame runtime leaks memory owner original repaired)
    (clean : ∀ record ∈ (runtime.reactiveApplication leaks).executionTraffic repaired,
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.envelope = true)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (forbidden : runtime.permittedServiceEnvelope record.observation record.ledger
      record.envelope = false) :
    record ∉ (runtime.reactiveApplication leaks).executionTraffic original := by
  intro present
  rw [frame.traffic] at present
  have permitted := clean record present
  rw [forbidden] at permitted
  cases permitted

end Vegas.EventGraphRuntime.BindingMemory.Frame

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveAssociationPersistence
import Vegas.EventGraph.ResolutionFields

/-! # Opening certificates originate in an owner's resolution response

The retained menu issues certificates only with successful guarded openings.
Every network copy therefore identifies an accepted binding and a resolution
already recorded in that binding owner's response recall. This uses the
runtime's ideal certificate issuance and handle ownership rules; it does not
assert cryptographic key secrecy or identify a physical broadcaster.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A certificate's binding association and original resolution survive all
later network copies. The event is remembered by the certificate owner. -/
def ResolutionEvidence (execution : (runtime.reactiveApplication leaks).Execution)
    (fact : OpeningFact graph) : Prop :=
  ∃ event field, (graph.nodes event).resolutionField? = some field ∧
    execution.application.accepted field = some fact.handle ∧
    runtime.eventRecorded leaks (execution.recall fact.handle.1) event = true

theorem ResolutionEvidence.respond
    {execution : (runtime.reactiveApplication leaks).Execution} {fact : OpeningFact graph}
    (origin : runtime.ResolutionEvidence leaks execution fact)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action) :
    runtime.ResolutionEvidence leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) fact := by
  obtain ⟨event, field, node, accepted, recorded⟩ := origin
  refine ⟨event, field, node, ?_, runtime.eventRecorded_respond_of_recorded leaks
    execution who fact.handle.1 response event recorded⟩
  exact (congrFun (congrArg PublicView.accepted
    (runtime.reactive_respond_application leaks execution who response).2) field).trans accepted

theorem ResolutionEvidence.environment
    {execution next : (runtime.reactiveApplication leaks).Execution} {fact : OpeningFact graph}
    (origin : runtime.ResolutionEvidence leaks execution fact)
    (valid : execution.application.BindingInvariant)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep
      (runtime.reactiveApplication leaks) command).support) :
    runtime.ResolutionEvidence leaks next fact := by
  obtain ⟨event, field, node, accepted, recorded⟩ := origin
  refine ⟨event, field, node, ((runtime.reactiveAssociationInvariant leaks field
    fact.handle).environmentStep execution next command ⟨valid, accepted⟩ reached).2, ?_⟩
  rw [(runtime.reactiveApplication leaks).environmentStep_recall execution next command reached]
  exact recorded

variable [Fintype Player]

end Vegas.EventGraphRuntime

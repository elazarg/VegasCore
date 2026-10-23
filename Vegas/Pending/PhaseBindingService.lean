/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingAcceptance

/-! # Actual counted binding service across phase retirement

All association, signed-origin and count facts are discharged from the same
initialized physical history. The service endpoint retains the raw accepted
completion and exact normalized successor, including immediate phase rollback.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- Own count soundness is sufficient; all foreign responses remain raw. -/
theorem binding_accepted_of_own_history
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control))
    (owner : Player)
    (clean : ∀ packet ∈ control.execution.network.inputs, packet.sender = owner →
      permits control.execution.network.inputs packet = true)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs) (sender : message.sender = owner)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime event) :
    ∃ native next,
      handle runtime control.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      event ∈ native.config.cut.completed ∧
      native.accepted (.inr event) = some candidate ∧
      next = ({control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧
      (app).handle control.execution.application message = some next := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have recalled := (app).history_inputRecall initial horizon scheduler trace
  have signed := phaseSignedBindings_history runtime leaks plan inputs horizon scheduler trace
  have binding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler trace
  exact binding_accepted runtime leaks control.execution recalled owner clean signed
    ((app).uniqueIds_history scheduler initial horizon control trace)
    binding.active.toAssociationInvariant message member sender event candidate call request timely

end Vegas.EventGraphRuntime.PhaseCount

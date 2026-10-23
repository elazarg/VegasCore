/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseFirstResponseRecall
import Vegas.Pending.ReservedEpochCompletion
import Vegas.Pending.ReservedEpochFirstOffer

/-! # The actual first callback preceding a due reserved request -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Any still-ready due event already had a real first callback in its literal
physical namespace. The callback may be an old WAIT; it is not silently made
fresh. Future policy comparisons must inspect that actual recorded action. -/
theorem expired_request_first_response {length : Nat} (tape : Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
        (family runtime leaks (packetCapacity runtime) tape)).Trace (some control))
    (owner : Player) (event : graph.EventId) (entered : Nat)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (stamp : control.execution.application.current.native.activatedAt event = some entered)
    (due : runtime.deadline event ≤
      control.execution.application.current.native.clock - entered) :
    ∃ (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
          (family runtime leaks (packetCapacity runtime) tape)).Trace (some before))
      (entry : (app).PlayerEntry),
      TracePrefix prior trace ∧ before.actor = some owner ∧
      entry ∈ control.execution.recall owner ∧
      entry.beforeView = before.execution.observe (app) owner ∧
      entry.action ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (before.execution.recall owner) (before.execution.observe (app) owner) ∧
      before.execution.application.SeedRequest owner
        ⟨control.execution.application.attempt, event⟩ ∧
      ¬ PhaseCount.ResponseRecorded runtime leaks owner
        ⟨control.execution.application.attempt, event⟩ (before.execution.recall owner) ∧
      (∃ later, control.execution.recall owner =
        before.execution.recall owner ++ entry :: later) ∧
      ∃ postTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
            (family runtime leaks (packetCapacity runtime) tape)).Trace
              (some ⟨before.remaining, none,
                before.execution.respond (app) owner entry.action⟩),
        TracePrefix postTrace trace := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks (packetCapacity runtime) tape
  have recorded : PhaseCount.ResponseRecorded runtime leaks owner
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall owner) := by
    by_contra absent
    have bound := first_response_clock_bound runtime leaks (packetCapacity runtime)
      (completionCycles runtime) tape activationGap processingGap gaps plan ordered maximal inputs
        control (menu.toRawTrace initial (executionHorizon runtime) scheduler trace) event owner
          entered request stamp absent
    have fitting := margin event (by rw [request.2.2.2.1]; rfl)
    change (activationGap + 1) + (processingGap + 1) < runtime.deadline event at fitting
    omega
  exact phase_first_recorded_request_prefix runtime leaks menu plan inputs
    (executionHorizon runtime) scheduler control trace owner _ recorded

end Vegas.EventGraphRuntime.ReservedEpoch

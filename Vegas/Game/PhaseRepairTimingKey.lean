/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairOperationalView
import Vegas.Pending.PhaseOpeningBindingPrefix

/-! # Actual opening keys along chronological directed repair -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A ready opening's delivered key field is its actual visible binding.
Owner attribution uses the actual reveal-relaxed readiness theorem. -/
theorem phaseDeliveredValue_of_opening (ordered : graph.RevealRelaxedOrdered)
    (physical : (app).Execution) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : physical.application.SeedRequest owner ⟨physical.application.attempt, event⟩) :
    phaseDeliveredValue runtime leaks owner (physical.observe app owner) =
      some ⟨.binding owner payload,
        binding.get? physical.application.current.native.config.store⟩ := by
  classical
  have turn : physical.application.current.native.publicView.ownTurn? owner = some event := by
    apply PublicView.ownTurn?_of_ownTurn
    exact State.ownTurn_of_ready _ ordered owner event
      ((physical.application.current.native.publicView_eventReady event).mpr request.2.2.1)
      request.2.2.2.1
  have observedTurn : (physical.observe app owner).application.2.native.ownTurn? owner =
      some event := turn
  unfold phaseDeliveredValue
  simp only [observedTurn, node]
  change some (⟨.binding owner payload,
      binding.get? (graph.playerStore owner physical.application.current.native.config.store)⟩ :
        Σ kind : EventField Player L, Option kind.Value) = _
  rw [binding.get?_playerStore owner physical.application.current.native.config.store rfl]

namespace EventGraphRuntime.PhaseBindingRepair.Frame

variable [Fintype Player]

/-- At an actual earlier opening, the clear later binding callback derives the
successful delivered value. The chronological induction supplies the earlier
erased word; the current physical frame supplies all remaining key fields. -/
theorem opening_timingKey_eq (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (owner : Player) (remaining : Nat) (original repaired : (app).Execution)
    (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks (graph := graph)))
    (frame : PhaseBindingRepair.Frame runtime leaks memory owner original repaired)
    (past : (original.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (repaired.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (beforeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, original⟩))
    (final : (app).Control)
    (finalTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some final))
    (isPrefix : TracePrefix beforeTrace finalTrace)
    (clear : final.execution.application.current.excluded = ∅)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : original.application.SeedRequest owner ⟨original.application.attempt, event⟩)
    (imageRequest : repaired.application.SeedRequest owner ⟨repaired.application.attempt, event⟩)
    (bindingEvent : graph.EventId) (bindingOwner : Player) (bindingPayload : L.Ty)
    (bindingOutput : graph.outputLayout bindingEvent = .binding bindingOwner bindingPayload)
    (finalRequest : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩) :
    phaseTimingKey runtime leaks owner (some (original.recall owner, original.observe app owner)) =
      phaseTimingKey runtime leaks owner
        (some (repaired.recall owner, repaired.observe app owner)) := by
  obtain ⟨value, stored⟩ := phase_opening_binding_success_before_binding runtime leaks bounds plan
    ordered maximal inputs horizon scheduler ⟨remaining, some owner, original⟩ final beforeTrace
      finalTrace isPrefix clear event owner payload binding checks outputEq codeEq node
        request.2.2.1 bindingEvent bindingOwner bindingPayload bindingOutput finalRequest
  have preserves : original.application.current.native.config.store.BindingRefines
      repaired.application.current.native.config.store := frame.live.successful
  have imageStored := preserves.success binding value stored
  simp only [phaseTimingKey,
    phaseDeliveredValue_of_opening runtime leaks ordered original owner event payload binding checks
      outputEq codeEq node request,
    phaseDeliveredValue_of_opening runtime leaks ordered repaired owner event payload binding checks
      outputEq codeEq node imageRequest,
    stored, imageStored, frame.operationalView_eq, past]

end EventGraphRuntime.PhaseBindingRepair.Frame
end Vegas

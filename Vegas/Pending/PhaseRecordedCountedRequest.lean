/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseNativeInvariant
import Interaction.ReactiveRecordedResponse

/-! # The actual request addressed by a remembered counted transmission -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A remembered nonsilent response recovers its actual request from the
original legal prefix. Both the public namespace and static event are retained. -/
theorem recorded_material_request (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (owner : Player) (entry : (app).PlayerEntry)
    (recorded : entry ∈ current.execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material) :
    ∃ coordinate : CommitAttemptEvent graph,
      PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate ∧
      coordinate.attempt = entry.beforeView.application.2.attempt ∧
      material.call.packet.event? graph = some coordinate.event := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := onePacketMenu runtime leaks bounds
  obtain ⟨before, prior, _prefix, acting, viewed, offered, _after, _recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler current trace owner entry recorded
  have sentMember : (⟨some material⟩ : (app).Action) ∈
      onePacketActions runtime leaks bounds owner (before.execution.recall owner)
        (before.execution.observe (app) owner) := by
    have same : entry.action = (⟨some material⟩ : (app).Action) := by
      cases action : entry.action with
      | mk transmission =>
          rw [action] at transmitted
          exact congrArg ReactiveApplication.Action.mk transmitted
    rwa [same] at offered
  rcases before with ⟨remaining, actor, execution⟩
  cases acting
  obtain ⟨coordinate, request⟩ := onePacket_request_of_nonsilent runtime leaks bounds plan
    inputs horizon scheduler remaining owner execution prior material sentMember
  have addressed := onePacket_event_of_request runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner execution prior coordinate request material sentMember
  obtain ⟨_input, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    (menu.toRawTrace initial horizon scheduler prior)
  refine ⟨coordinate, ?_, ?_, addressed⟩
  · rw [viewed]
    exact (execution.application.requests_publicView valid owner coordinate).mpr request
  · rw [viewed]
    exact request.1

end Vegas.EventGraphRuntime.PhaseCount

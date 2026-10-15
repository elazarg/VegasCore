/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearRequestAddress
import Vegas.Pending.PhaseReadyRequests
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseClearTraceProgress
import Interaction.ReactiveRecordedResponse

/-! # Actual same-coordinate requests behind remembered native source turns -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every earlier native turn for a still-requested source event was a genuine
request for the SAME physical coordinate. Actual clear history rules out reset
ambiguity, and the static phase partition supplies the unique source address. -/
theorem phase_recorded_request_of_native_turn
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : graph.EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.recall who)
    (turn : entry.beforeView.application.1.publicView.ownTurn? who = some event) :
    PhaseRuntimeState.requests entry.beforeView.application.2 who
      ⟨control.execution.application.attempt, event⟩ := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨before, prior, isPrefix, _acting, viewed, _offered, _after, _recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler control trace who entry recorded
  have priorClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have raw := menu.toRawTrace initial horizon scheduler prior
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have living := (phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan input,
        PhaseRuntimeState.initial_live plan input⟩) raw
  have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler raw
  rw [viewed] at turn
  have selected := before.execution.application.current.native.publicView.ownTurn?_spec who
    event turn
  have ready := (before.execution.application.current.native.publicView_eventReady event).mp
    selected.1
  have oldRequest : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩ :=
    ⟨rfl, before.execution.application.ready_current_phase ordered living.1 living.2
      geometry.2.2 event ready, ready, selected.2, by simp only [priorClear]; simp⟩
  have oldAddress := phase_request_address_of_clear runtime leaks plan inputs horizon scheduler raw
    priorClear who ⟨before.execution.application.attempt, event⟩ oldRequest
  have currentAddress := phase_request_address_of_clear runtime leaks plan inputs horizon scheduler
    (menu.toRawTrace initial horizon scheduler trace) clear who
      ⟨control.execution.application.attempt, event⟩ request
  have same : before.execution.application.attempt = control.execution.application.attempt :=
    oldAddress.trans currentAddress.symm
  have publicRequest := (PhaseRuntimeState.requests_publicView before.execution.application valid
    who
    ⟨before.execution.application.attempt, event⟩).mpr oldRequest
  rw [viewed, ← same]
  exact publicRequest

end Vegas.EventGraphRuntime

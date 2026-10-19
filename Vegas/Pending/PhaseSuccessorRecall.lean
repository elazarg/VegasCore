/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseOncePolicy
import Vegas.EventGraph.ObservationStep
import Interaction.ReactiveRecordedResponse

/-! # Genuine first callbacks after a predecessor completes -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A still-unfinished prerequisite excludes every earlier callback for its
successor at the present physical address, including callbacks that sent WAIT. -/
theorem phase_unfinished_predecessor_no_response (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control))
    (owner : Player) (event predecessor : graph.EventId)
    (dependency : predecessor ∈ graph.order.predecessors event)
    (unfinished : predecessor ∉ control.execution.application.current.native.config.cut.completed) :
    ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall owner) := by
  rintro ⟨entry, member, requested⟩
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨before, prior, kept, _acting, viewed, _legal, _after, _recall⟩ :=
    menu.recorded_response_prefix initial horizon scheduler control trace owner entry member
  have raw := menu.toRawTrace initial horizon scheduler prior
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  rw [viewed] at requested
  have earlier := (PhaseRuntimeState.requests_publicView before.execution.application valid owner
    ⟨control.execution.application.attempt, event⟩).mp requested
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (by
      intro state supported
      obtain ⟨input, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input) raw
  have extension := phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
    before control prior trace kept ordered earlier.1.symm
  exact unfinished (completed_subset_of_history_prefix _ _ extension.2
    (earlier.2.2.1.2 dependency))

/-- An actual environment step that enables a successor does not manufacture an
old response for it. Its permanent own recall is the unchanged earlier word. -/
theorem phase_successor_first_after_environment (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control))
    (owner : Player) (coordinate : CommitAttemptEvent graph) (predecessor : graph.EventId)
    (dependency : predecessor ∈ graph.order.predecessors coordinate.event)
    (unfinished : predecessor ∉ control.execution.application.current.native.config.cut.completed)
    (next : (app).Execution) (command : (app).Command)
    (reached : next ∈ (control.execution.environmentStep (app) command).support)
    (same : control.execution.application.attempt = next.application.attempt)
    (request : next.application.SeedRequest owner coordinate) :
    ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate (next.recall owner) := by
  have address : coordinate =
      ⟨control.execution.application.attempt, coordinate.event⟩ := by
    cases coordinate with
    | mk attempt event =>
      exact congrArg (fun attempt => (⟨attempt, event⟩ : CommitAttemptEvent graph))
        (request.1.trans same.symm)
  rw [(app).environmentStep_recall control.execution next command reached, address]
  exact phase_unfinished_predecessor_no_response runtime leaks menu plan inputs horizon scheduler
    control trace owner coordinate.event predecessor dependency unfinished

end Vegas.EventGraphRuntime

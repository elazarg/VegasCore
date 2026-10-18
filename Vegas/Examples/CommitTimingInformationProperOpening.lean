/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationProperBinding
import Vegas.Pending.PhaseOpeningAcceptance

/-! # Successful native disclosure for the concrete constant guards -/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

/-- Both compiled guards are constantly TRUE and read only their own binding. -/
theorem reveal_eval_success (store : Store graph.layout) (owner : Player) (value : Bool)
    (stored : store (.inr (bindingEvent owner)) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value))) :
    (graph.nodes (revealEvent owner)).eval?
      (cast (congrArg EventField.Action (revealEvent_layout owner).symm) true) store = some
      (PMF.pure (cast (congrArg EventField.Value (revealEvent_layout owner).symm)
        (PublicationResult.success value))) := by
  fin_cases owner
  · change store (.inr (bindingEvent alice)) = some (.success value) at stored
    change (graph.nodes (revealEvent alice)).eval? true store =
      some (PMF.pure (.success value))
    change (Option.map PMF.pure
      ((store (.inr (bindingEvent alice))).bind fun bound => _)) = _
    rw [stored]
    rfl
  · change store (.inr (bindingEvent bob)) = some (.success value) at stored
    change (graph.nodes (revealEvent bob)).eval? true store =
      some (PMF.pure (.success value))
    change (Option.map PMF.pure
      ((store (.inr (bindingEvent bob))).bind fun bound => _)) = _
    rw [stored]
    rfl

/-- Actual opening acceptance executes TRUE disclosure. With the literal
compiled guards, its output is the successful stored Boolean, for either owner. -/
theorem handle_successful_binding_opening
    (state next : EventGraphRuntime.State graph) (identifier : MessageId Player) (owner : Player)
    (candidate : Handle graph) (raw : Raw simpleExpr) (value : Bool)
    (stored : state.config.store (.inr (bindingEvent owner)) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (accepted : handle runtime state
      ⟨identifier, .opening (revealEvent owner) candidate raw⟩ = some next) :
    next.config.outputs (revealEvent owner) = some
      (cast (congrArg EventField.Value (revealEvent_layout owner).symm)
        (PublicationResult.success value)) := by
  classical
  obtain ⟨ready, action, supported, _clock, _activated, _owner, _payload, _binding, _checks,
    _outputEq, _codeEq, _node, actionEq⟩ := runtime.handle_opening_config_step state next
      identifier (revealEvent owner) candidate raw accepted
  have evaluated := reveal_eval_success state.config.store owner value stored
  fin_cases owner
  all_goals
    change action = true at actionEq
    rw [actionEq] at supported
    rw [state.config.step_eq_map_of_eval _ ready true
      _ evaluated, PMF.pure_map, PMF.mem_support_pure_iff] at supported
    rw [supported, Config.complete_output_same]

/-- A real count-admitted, ready and timely opening publishes the surviving
owner's value. Authentication, accepted-handle association and the raw
handler result are derived from the same actual counted history. -/
theorem counted_successful_opening_accepted
    (selected : app.Scheduler) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some control))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (candidate : Handle graph) (raw : Raw simpleExpr)
    (opening : message.payload.packet.call = .opening (revealEvent owner) candidate raw)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime
      (revealEvent owner)) (value : Bool)
    (stored : control.execution.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value))) :
    ∃ native next,
      handle runtime control.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      (revealEvent owner) ∈ native.config.cut.completed ∧
      native.config.outputs (revealEvent owner) = some
        (cast (congrArg EventField.Value (revealEvent_layout owner).symm)
          (PublicationResult.success value)) ∧
      next = ({control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧
      app.handle control.execution.application message = some next := by
  have compiledTrace := trace
  obtain ⟨native, next, handled, completed, normalized, phaseHandled⟩ :=
    PhaseCount.opening_accepted_of_history runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon selected compiledTrace message member
      (revealEvent owner) candidate raw opening request timely
  have actual : handle runtime control.execution.application.current.native
      ⟨message.id, .opening (revealEvent owner) candidate raw⟩ = some native := by
    simpa only [opening] using handled
  exact ⟨native, next, handled, completed,
    handle_successful_binding_opening control.execution.application.current.native native
      message.id owner candidate raw value stored actual, normalized, phaseHandled⟩

end Vegas.Examples.CommitTimingInformation

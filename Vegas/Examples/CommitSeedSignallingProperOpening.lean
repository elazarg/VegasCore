/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingProperBinding
import Vegas.Examples.CommitSeedSignallingPayoffs
import Vegas.Pending.PhaseOpeningAcceptance

/-! # Successful native disclosure for the concrete constant guards -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- The compiled Alice guard is constantly TRUE and reads no foreign value. -/
theorem alice_reveal_eval_success (store : Store graph.layout) (value : Bool)
    (stored : store (.inr aliceBinding) = some (.success value)) :
    (graph.nodes aliceReveal).eval? true store = some (PMF.pure (.success value)) := by
  change (Option.map PMF.pure ((store (.inr aliceBinding)).bind fun bound => _)) = _
  rw [stored]
  rfl

/-- The compiled Bob guard is constantly TRUE and reads no foreign value. -/
theorem bob_reveal_eval_success (store : Store graph.layout) (value : Bool)
    (stored : store (.inr bobBinding) = some (.success value)) :
    (graph.nodes bobReveal).eval? true store = some (PMF.pure (.success value)) := by
  change (Option.map PMF.pure ((store (.inr bobBinding)).bind fun bound => _)) = _
  rw [stored]
  rfl

theorem bindingEvent_layout (owner : Player) :
    graph.outputLayout (bindingEvent owner) = .binding owner .bool := by
  fin_cases owner <;> rfl

theorem revealEvent_layout (owner : Player) :
    graph.outputLayout (revealEvent owner) = .publication .bool := by
  unfold revealEvent
  split <;> rfl

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
  by_cases left : owner = alice
  · subst owner
    change state.config.store (.inr aliceBinding) = some (.success value) at stored
    change handle runtime state ⟨identifier, .opening aliceReveal candidate raw⟩ = some next
      at accepted
    change next.config.outputs aliceReveal = some (.success value)
    obtain ⟨ready, action, supported, _clock, _activated, _owner, _payload, _binding, _checks,
      _outputEq, _codeEq, _node, actionEq⟩ := runtime.handle_opening_config_step state next
        identifier aliceReveal candidate raw accepted
    change action = true at actionEq
    rw [actionEq] at supported
    have evaluated := alice_reveal_eval_success state.config.store value stored
    rw [state.config.step_eq_map_of_eval aliceReveal ready true
      (PMF.pure (.success value)) evaluated, PMF.pure_map, PMF.mem_support_pure_iff] at supported
    rw [supported, Config.complete_output_same]
  · have right : owner = bob := by
      fin_cases owner
      · exact (left rfl).elim
      · rfl
    subst owner
    change state.config.store (.inr bobBinding) = some (.success value) at stored
    change handle runtime state ⟨identifier, .opening bobReveal candidate raw⟩ = some next
      at accepted
    change next.config.outputs bobReveal = some (.success value)
    obtain ⟨ready, action, supported, _clock, _activated, _owner, _payload, _binding, _checks,
      _outputEq, _codeEq, _node, actionEq⟩ := runtime.handle_opening_config_step state next
        identifier bobReveal candidate raw accepted
    change action = true at actionEq
    rw [actionEq] at supported
    have evaluated := bob_reveal_eval_success state.config.store value stored
    rw [state.config.step_eq_map_of_eval bobReveal ready true
      (PMF.pure (.success value)) evaluated, PMF.pure_map, PMF.mem_support_pure_iff] at supported
    rw [supported, Config.complete_output_same]

/-- A real count-admitted, ready and timely opening publishes the surviving
owner's value. Authentication, accepted-handle association and the raw
handler result are derived from the same actual counted history. -/
theorem counted_successful_opening_accepted
    (control : app.Control) (trace : countedProtocol.Trace (some control))
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
  obtain ⟨native, next, handled, completed, normalized, phaseHandled⟩ :=
    PhaseCount.opening_accepted_of_history runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler trace message member
      (revealEvent owner) candidate raw opening request timely
  have actual : handle runtime control.execution.application.current.native
      ⟨message.id, .opening (revealEvent owner) candidate raw⟩ = some native := by
    simpa only [opening] using handled
  exact ⟨native, next, handled, completed,
    handle_successful_binding_opening control.execution.application.current.native native
      message.id owner candidate raw value stored actual, normalized, phaseHandled⟩

end Vegas.Examples.CommitSeedSignalling

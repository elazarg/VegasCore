/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedPhysicalIsolation
import Vegas.Pending.PhaseEnvironmentIsolation

/-! # Every physical request loss is its own inclusion or expiry -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

namespace PhaseRuntimeState

/-- Private registration and packet emission leave a ready request intact. -/
theorem SeedRequest.submit {state : PhaseRuntimeState graph} {owner : Player}
    {coordinate : CommitAttemptEvent graph} (requested : state.SeedRequest owner coordinate)
    (actor : Player) (submission : WitnessedSubmission graph) :
    (state.submit actor submission).SeedRequest owner coordinate := by
  have config : (state.submit actor submission).current.native.config =
      state.current.native.config := by
    change (submitStep _ actor _).config = _
    rw [submitStep_config, (submission.call.register_facts actor state.current.native).1]
  refine ⟨requested.1, requested.2.1, ?_, requested.2.2.2.1, requested.2.2.2.2⟩
  rw [config]
  exact requested.2.2.1

end PhaseRuntimeState

/-- An authored response cannot be the transition that loses a physical request. -/
theorem respond_request (execution : (app).Execution) (actor : Player) (action : (app).Action)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : execution.application.SeedRequest owner coordinate) :
    (execution.respond app actor action).application.SeedRequest owner coordinate := by
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact requested
      | some material => exact requested.submit actor material

/-- A genuine request cannot disappear through another principal's work or
automatic retry. Its first loss is an expiry addressed to it or an accepting
inclusion of its owner's packet, with the original raw graph step retained. -/
theorem environment_request_or_own_resolution (ordered : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} (execution next : (app).Execution)
    (valid : execution.application.Invariant inputs)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : execution.application.SeedRequest owner coordinate)
    (command : (app).Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.application.SeedRequest owner coordinate ∨
      command = .application (.expire coordinate.event) ∨
      ∃ (identifier : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
        (native : State graph)
        (ready : execution.application.current.native.config.cut.Ready coordinate.event)
        (action : graph.Action coordinate.event),
        command = .include identifier ∧ execution.network.lookup identifier = some message ∧
        message.sender = owner ∧
        message.payload.packet.call.event? graph = some coordinate.event ∧
        EventGraphRuntime.handle runtime execution.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = some native ∧
        native.config ∈ (execution.application.current.native.config.step
          coordinate.event ready action).support ∧
        next.application = ({execution.application with
          current := execution.application.current.inclusionResult
            message.payload.packet.call native } :
            PhaseRuntimeState graph).normalize := by
  classical
  cases command with
  | activate who =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
      obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact Or.inl requested
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      cases reached
      exact Or.inl requested
  | application command =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
      obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ reached
      rcases PhaseRuntimeState.environment_request_or_expiry runtime ordered
          execution.application state command moved owner coordinate requested with retained | own
      · exact Or.inl retained
      · exact Or.inr (Or.inl (congrArg ReactiveApplication.Command.application own))
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      cases reached
      cases found : execution.network.lookup identifier with
      | none =>
          simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found] using Or.inl requested
      | some message =>
          cases handled : (app).handle execution.application message with
          | none =>
              simpa only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, handled, Option.getD_none] using
                  Or.inl requested
          | some target =>
              have moved : execution.application.handle runtime message = some target := handled
              have actual : (execution.includePending app identifier).application = target := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, handled, Option.getD_some]
              rcases PhaseRuntimeState.handle_request_or_own_completion runtime ordered
                  execution.application target valid message moved owner coordinate requested with
                retained | ⟨native, ready, action, sender, addressed, accepted, stepped, normalized⟩
              · exact Or.inl (actual.symm ▸ retained)
              · exact Or.inr (Or.inr ⟨identifier, message, native, ready, action, rfl, found,
                  sender, addressed, accepted, stepped, actual.trans normalized⟩)

end Vegas.EventGraphRuntime

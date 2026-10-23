/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseReadyResolution

/-! # A timely ready request can be lost only by accepting inclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Expiry before this ready event's deadline stutters before normalization,
which preserves its genuine request. No scheduler fairness premise is used. -/
theorem expiry_request_before_deadline (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (requested : state.SeedRequest owner coordinate)
    (timely : state.current.native.WithinDeadline runtime coordinate.event)
    (reached : next ∈ (state.environment runtime (.expire coordinate.event)).support) :
    next.SeedRequest owner coordinate := by
  classical
  cases activated : state.current.native.activatedAt coordinate.event with
  | none =>
      simp only [State.WithinDeadline, activated] at timely
  | some entered =>
      have notDue : ¬ runtime.deadline coordinate.event ≤ state.current.native.clock - entered :=
        Nat.not_le_of_lt (by simpa only [State.WithinDeadline, activated] using timely)
      have raw := environmentStep_expire_of_not_due runtime state.current.native coordinate.event
        requested.2.2.1 entered activated notDue
      unfold PhaseRuntimeState.environment at reached
      split at reached
      · rw [raw, PMF.pure_map, PMF.mem_support_pure_iff _ _] at reached
        have unchanged : state.current.environmentResult (.expire coordinate.event)
            state.current.native = state.current := by
          simp only [RecoveryState.environmentResult, requested.2.2.1.1, and_false, ite_false]
        simp only [unchanged] at reached
        cases reached
        exact requested.normalize.2
      · cases (PMF.mem_support_pure_iff _ _).mp reached
        exact requested

end PhaseRuntimeState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A timely physical request's actual first loss authenticates its own raw
packet inclusion, independently of the environment's priority rule. -/
theorem timely_first_request_loss_includes (ordered : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} (execution next : (app).Execution)
    (valid : execution.application.Invariant inputs)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : execution.application.SeedRequest owner coordinate)
    (timely : execution.application.current.native.WithinDeadline runtime coordinate.event)
    (command : (app).Command)
    (moved : next ∈ (execution.environmentStep app command).support)
    (lost : ¬ next.application.SeedRequest owner coordinate) :
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
  rcases environment_request_or_own_resolution runtime leaks ordered execution next valid
      owner coordinate requested command moved with retained | expiry | included
  · exact (lost retained).elim
  · have expirySupported := moved
    rw [expiry] at expirySupported
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at expirySupported
    obtain ⟨state, stateMoved, rfl⟩ := PMF.support_map .. ▸ expirySupported
    exact (lost (PhaseRuntimeState.expiry_request_before_deadline runtime
      execution.application state owner coordinate requested timely stateMoved)).elim
  · exact included

end Vegas.EventGraphRuntime

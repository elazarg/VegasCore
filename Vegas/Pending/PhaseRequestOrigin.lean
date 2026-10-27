/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseReadyRequests
import Vegas.Pending.PhaseRetryClock

/-! # Readiness origins retain the physical attempt coordinate -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

private theorem request_origin_of_bounds {inputs : graph.Inputs}
    (before after : PhaseRuntimeState graph) (ordered : graph.RevealRelaxedOrdered)
    (valid : before.Invariant inputs) (frontier : before.Frontier) (live : before.Live)
    (maximal : RuntimePhase.PartitionRegular before.phases)
    (quiescent : ∀ event, ¬ before.current.AutomaticReady event)
    (suffix : after.phases <:+ before.phases) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (entered limit : Nat)
    (request : after.SeedRequest owner coordinate)
    (origin : before.current.native.activatedAt coordinate.event = some entered ∨ limit ≤ entered)
    (retry : after.generation ≠ before.generation → limit ≤ entered) :
    (before.SeedRequest owner coordinate ∧
      before.current.native.activatedAt coordinate.event = some entered) ∨ limit ≤ entered := by
  by_cases fresh : limit ≤ entered
  · exact Or.inr fresh
  · obtain retained | born := origin
    · have ready : before.current.native.config.cut.Ready coordinate.event :=
        ((valid.active.activated_iff _).mp (by rw [retained]; rfl)).1
      have samePhase := ready_namespace_phase before after ordered frontier live maximal suffix
        owner coordinate request ready
      have sameGeneration : after.generation = before.generation := by
        by_contra changed
        exact fresh (retry changed)
      have sameAttempt : before.attempt = after.attempt := by
        change (⟨before.attempt.phase, before.generation⟩ : CommitAttemptId) =
          ⟨after.attempt.phase, after.generation⟩
        rw [samePhase, sameGeneration]
      refine Or.inl ⟨⟨request.1.trans sameAttempt.symm,
        ready_current_phase before ordered frontier live maximal _ ready,
        ready, request.2.2.2.1, ?_⟩, retained⟩
      intro excluded
      exact quiescent coordinate.event ⟨ready, by
        simpa only [request.2.2.2.1] using excluded⟩
    · exact (fresh born).elim

end PhaseRuntimeState

/-- A generation change stamps every surviving ready timer at or after the
physical operation's original clock. -/
theorem phaseApplication_retryTimers (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      ∀ inputs, before.Invariant inputs → after.generation ≠ before.generation →
        ∀ event entered, after.current.native.activatedAt event = some entered →
          before.current.native.clock ≤ entered) where
  refl _ _ _ changed := (changed rfl).elim
  submit _ _ _ _ _ changed := (changed rfl).elim
  handle state message next accepted _inputs valid changed :=
    PhaseRuntimeState.handle_retry_timers runtime state next valid message accepted changed
  environment state command next reached _inputs valid changed :=
    PhaseRuntimeState.environment_retry_timers runtime state next valid command reached changed

namespace PhaseSeedScheduler

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A response can preserve an existing request or start a fresh timer. It
cannot make an old timer reappear under a different physical attempt. -/
theorem respond_request_origin {inputs : graph.Inputs} (execution : (app).Execution)
    (who : Player) (action : (app).Action) (ordered : graph.RevealRelaxedOrdered)
    (valid : execution.application.Invariant inputs) (frontier : execution.application.Frontier)
    (live : execution.application.Live)
    (maximal : RuntimePhase.PartitionRegular execution.application.phases)
    (quiescent : ∀ event, ¬ execution.application.current.AutomaticReady event)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (entered : Nat)
    (request : (execution.respond app who action).application.SeedRequest owner coordinate)
    (activated : (execution.respond app who action).application.current.native.activatedAt
      coordinate.event = some entered) :
    (execution.application.SeedRequest owner coordinate ∧
      execution.application.current.native.activatedAt coordinate.event = some entered) ∨
        execution.application.current.native.clock ≤ entered := by
  exact PhaseRuntimeState.request_origin_of_bounds execution.application
    (execution.respond app who action).application ordered valid frontier live maximal quiescent
    ((phaseApplication_phaseSuffix runtime leaks).respond execution who action) owner coordinate
    entered execution.application.current.native.clock request
    ((phaseApplication_activationOrigin runtime leaks).respond execution who action inputs valid
      coordinate.event entered activated request.2.2.1.1)
    (fun changed => (phaseApplication_retryTimers runtime leaks).respond execution who action
      inputs valid changed coordinate.event entered activated)

/-- The same coordinate-aware origin holds for every actual environment move,
including physical inclusion, expiry, sampling and phase reset. -/
theorem environmentStep_request_origin {inputs : graph.Inputs}
    (execution next : (app).Execution) (command : (app).Command)
    (ordered : graph.RevealRelaxedOrdered) (valid : execution.application.Invariant inputs)
    (frontier : execution.application.Frontier) (live : execution.application.Live)
    (maximal : RuntimePhase.PartitionRegular execution.application.phases)
    (quiescent : ∀ event, ¬ execution.application.current.AutomaticReady event)
    (reached : next ∈ (execution.environmentStep app command).support)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (entered : Nat)
    (request : next.application.SeedRequest owner coordinate)
    (activated : next.application.current.native.activatedAt coordinate.event = some entered) :
    (execution.application.SeedRequest owner coordinate ∧
      execution.application.current.native.activatedAt coordinate.event = some entered) ∨
        execution.application.current.native.clock ≤ entered := by
  exact PhaseRuntimeState.request_origin_of_bounds execution.application next.application ordered
    valid frontier live maximal quiescent
    ((phaseApplication_phaseSuffix runtime leaks).environmentStep execution next command reached)
    owner coordinate entered execution.application.current.native.clock request
    ((phaseApplication_activationOrigin runtime leaks).environmentStep execution next command
      reached inputs valid coordinate.event entered activated request.2.2.1.1)
    (fun changed => (phaseApplication_retryTimers runtime leaks).environmentStep execution next
      command reached inputs valid changed coordinate.event entered activated)

end PhaseSeedScheduler
end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperRetryReceipts
import Vegas.Pending.PhaseBindingReceiptResolution
import Vegas.Pending.PhaseTimelyResolution

/-! # A proper initialized retry cannot lose its request by expiry -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

variable (clock : Nat)

/-- A genuine retry request which is lost by an actual expiry cannot belong
to the fixed-late owner's initialized trajectory. Positive age exposes its
earlier proper submission; its true receipt contradicts expiry permanence.
The other owner's policies and the complete original past are retained. -/
theorem scheduled_proper_retry_expiry_impossible
    (seed : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (afterRemaining : Nat) (after : app.Execution)
    (afterTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨afterRemaining, none, after⟩))
    (kept : TracePrefix trace afterTrace)
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (ownConsistent : (scheduledProperPolicy clock owner).Consistent (after.recall owner))
    (retired : coordinate.attempt ≠ originalAttempt)
    (binding : graph.outputLayout coordinate.event = .binding owner .bool)
    (request : execution.application.SeedRequest owner coordinate)
    (expiry : after ∈ (execution.environmentStep app
      (.application (.expire coordinate.event))).support)
    (lost : ¬ after.application.SeedRequest owner coordinate) : False := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have valid := raw_native_valid (family seed) ⟨remaining, none, execution⟩ raw
  have ordered := (raw_phase_geometry (family seed) ⟨remaining, none, execution⟩ raw).1.adjacent
  have nativeMoved : after.application ∈
      (execution.application.environment runtime (.expire coordinate.event)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at expiry
    obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ expiry
    exact supported
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff coordinate.event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  have due : runtime.deadline coordinate.event ≤
      execution.application.current.native.clock - entered := by
    by_contra early
    have timely : execution.application.current.native.WithinDeadline runtime coordinate.event := by
      rw [State.WithinDeadline, stamp]
      omega
    exact lost (PhaseRuntimeState.expiry_request_before_deadline runtime execution.application
      after.application owner coordinate request timely nativeMoved)
  have dueActual : runtime.deadline coordinate.event ≤
      execution.application.current.native.clock -
        (execution.application.current.native.activatedAt coordinate.event).getD
          execution.application.current.native.clock := by
    rw [stamp, Option.getD_some]
    exact due
  have positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (execution.observeEnvironment app) := by
    change 0 < execution.application.current.native.clock -
      (execution.application.current.native.activatedAt coordinate.event).getD
        execution.application.current.native.clock
    rw [stamp, Option.getD_some]
    change 6 ≤ execution.application.current.native.clock - entered at due
    omega
  have completed := execution.application.expire_resolves_of_request runtime after.application
    valid ordered request dueActual nativeMoved
  have resolved := CommitAttemptEvent.Resolved.of_step coordinate execution.application
    after.application request.1
    ((phaseApplication_namespace_progress runtime leaks).environmentStep execution after
      (.application (.expire coordinate.event)) expiry ordered) completed
  have receipt := scheduled_proper_recorded_tail_binding_accepted clock seed remaining
    execution trace
    ⟨afterRemaining, none, after⟩ afterTrace kept coordinate owner retired binding request positive
      ownConsistent resolved
  have compiledRaw := raw
  rw [initial_eq_compiled] at compiledRaw
  have forbidden := PhaseService.not_bindingAccepted_runRounds_after_expire runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed) compiledRaw coordinate owner request
      dueActual
      after expiry (fun who => scheduledProperPolicy clock who) 0 after (by
        change after ∈ (PMF.pure after).support
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact forbidden receipt

/-- The original initialized experiment supplies the retained own-record condition. -/
theorem initialized_scheduled_proper_retry_expiry_impossible
    (players : Player → app.Policy) (seed : Seeds) (count : Nat)
    (remaining : Nat) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (afterRemaining : Nat) (after : app.Execution)
    (afterTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨afterRemaining, none, after⟩))
    (kept : TracePrefix trace afterTrace)
    (reached : after ∈ (app.runRounds (family seed) players count initialExecution).support)
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (policy : players owner = scheduledProperPolicy clock owner)
    (retired : coordinate.attempt ≠ originalAttempt)
    (binding : graph.outputLayout coordinate.event = .binding owner .bool)
    (request : execution.application.SeedRequest owner coordinate)
    (expiry : after ∈ (execution.environmentStep app
      (.application (.expire coordinate.event))).support)
    (lost : ¬ after.application.SeedRequest owner coordinate) : False := by
  have consistent := (app.consistentRecall_policyInvariant players).runRounds (family seed) count
    initialExecution after (fun _ => .nil) reached
  have focal := consistent owner
  rw [policy] at focal
  exact scheduled_proper_retry_expiry_impossible clock seed remaining execution trace
    afterRemaining after
    afterTrace kept coordinate owner focal retired binding request expiry lost

end Vegas.Examples.CommitSeedBroadcast

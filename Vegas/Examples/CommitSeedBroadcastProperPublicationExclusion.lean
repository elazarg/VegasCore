/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperPublicationExpiry
import Vegas.Examples.CommitSeedBroadcastPublicationInclusion
import Vegas.Pending.PhaseBindingReceiptResolution

/-! # Proper original trajectories cannot acquire a publication exclusion -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

variable (clock : Nat)

private theorem publication_request_event (execution : app.Execution) (event : graph.EventId)
    (owner : Player) (inside : event ∈ publicationPhase.events)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩) : event = revealEvent owner := by
  have interval := (RuntimePhase.mem_events publicationPhase event).mp inside
  change 3 ≤ event.val ∧ event.val < 6 at interval
  have acting : graph.actor? event = some owner := request.2.2.2.1
  fin_cases event
  · change 3 ≤ (0 : Nat) ∧ 0 < 6 at interval
    omega
  · change 3 ≤ (1 : Nat) ∧ 1 < 6 at interval
    omega
  · change 3 ≤ (2 : Nat) ∧ 2 < 6 at interval
    omega
  · change some alice = some owner at acting
    cases Option.some.inj acting
    rfl
  · change some bob = some owner at acting
    cases Option.some.inj acting
    rfl
  · change some carol = some owner at acting
    cases Option.some.inj acting
    rfl

/-- A newly excluded successor in the installed publication block would
require a due owned expiry. The original proper record has already served
that callback, which rules out the actual excluded endpoint. -/
theorem scheduled_proper_publication_exclusion_impossible
    (seed : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (prior : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (afterRemaining : Nat) (after : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨afterRemaining, none, after⟩))
    (kept : TracePrefix prior trace)
    (joint : Player → Option app.Action)
    (moved : some (⟨afterRemaining, none, after⟩ : app.Control) ∈
      (app.transition initial horizon (family seed)
        (some ⟨remaining, none, execution⟩) joint).support)
    (owner : Player)
    (focal : (scheduledProperPolicy clock owner).Consistent (after.recall owner))
    (installed : execution.application.phases.head? = some publicationPhase)
    (active : owner ∉ execution.application.current.excluded)
    (excluded : owner ∈ after.application.current.excluded) : False := by
  have raw := countedMenu.toRawTrace initial horizon (family seed) prior
  have valid := raw_native_valid (family seed) ⟨remaining, none, execution⟩ raw
  have geometry := raw_phase_geometry (family seed) ⟨remaining, none, execution⟩ raw
  have retained := app.reaches_recall_prefix initial horizon (family seed)
    (countedMenu.reaches_raw initial horizon (family seed) kept.reachesWithin)
      ⟨remaining, none, execution⟩ ⟨afterRemaining, none, after⟩ rfl rfl owner
  obtain ⟨later, pastEq⟩ := retained
  have ownConsistent : (scheduledProperPolicy clock owner).Consistent (execution.recall owner) := by
    apply ReactiveApplication.Policy.Consistent.of_append (after := later)
    rwa [pastEq]
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp installed
  have positioned := geometry.1.positioned
  rw [phases] at positioned
  have completed : bindingEvent owner ∈ execution.application.current.native.config.cut.completed :=
    positioned.2.1 (bindingEvent owner) (by fin_cases owner <;> decide)
  have stored := scheduled_proper_completed_binding_success_of_consistent clock seed
    ⟨remaining, none, execution⟩ prior owner ownConsistent completed active
  obtain ⟨operation, stepped⟩ := PhaseService.new_exclusion_application_command runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed)
      ⟨remaining, none, execution⟩ ⟨afterRemaining, none, after⟩ joint moved owner active
        excluded (by
          intro message next handled
          exact phase_handle_keeps_successful_binding_owner execution.application next message owner
            true stored active handled)
  obtain ⟨updated, selected, equal⟩ := PMF.support_map .. ▸ stepped
  obtain ⟨native, supported, stateEq⟩ := PMF.support_map .. ▸ selected
  have afterApplication : after.application = native := by
    exact (congrArg (fun current : app.Execution => current.application) equal).symm.trans
      (congrArg (fun current : app.Execution => current.application) stateEq).symm
  have head : publicationPhase ∈ execution.application.phases.head? := Option.mem_def.mpr installed
  obtain ⟨event, _completedNative, commandEq, inside, request, _nativeStep, _completed,
    _normalized⟩ := PhaseRuntimeState.environment_new_exclusion_request runtime
      execution.application native publicationPhase head operation supported owner active
        (by simpa only [afterApplication] using excluded)
  have publication := publication_request_event execution event owner inside request
  have expiry : after ∈ (execution.environmentStep app (.application (.expire event))).support := by
    rwa [commandEq] at stepped
  have nativeMoved : after.application ∈
      (execution.application.environment runtime (.expire event)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at expiry
    obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ expiry
    exact supported
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  have due : runtime.deadline event ≤ execution.application.current.native.clock - entered := by
    by_contra early
    have timely : execution.application.current.native.WithinDeadline runtime event := by
      rw [State.WithinDeadline, stamp]
      omega
    have survives := PhaseRuntimeState.expiry_request_before_deadline runtime execution.application
      after.application owner _ request timely nativeMoved
    exact survives.2.2.2.2 excluded
  have positive : 0 < PhaseSeedScheduler.elapsed runtime leaks
      ⟨execution.application.attempt, event⟩ (execution.observeEnvironment app) := by
    change 0 < execution.application.current.native.clock -
      (execution.application.current.native.activatedAt event).getD
        execution.application.current.native.clock
    rw [stamp, Option.getD_some]
    change 6 ≤ execution.application.current.native.clock - entered at due
    omega
  have retired : execution.application.attempt ≠ originalAttempt := by
    intro same
    have phaseEq := congrArg CommitAttemptId.phase same
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some] at phaseEq
    change 3 = 0 at phaseEq
    omega
  have survives := scheduled_proper_positive_publication_survives clock seed remaining
    execution prior
    ⟨afterRemaining, none, after⟩ trace kept owner focal
      ⟨execution.application.attempt, event⟩ retired publication request positive
  exact survives excluded

/-- The original initialized experiment supplies the retained own-record condition. -/
theorem initialized_scheduled_proper_publication_exclusion_impossible
    (players : Player → app.Policy) (seed : Seeds) (count : Nat)
    (remaining : Nat) (execution : app.Execution)
    (prior : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (afterRemaining : Nat) (after : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨afterRemaining, none, after⟩))
    (kept : TracePrefix prior trace)
    (reached : after ∈ (app.runRounds (family seed) players count initialExecution).support)
    (joint : Player → Option app.Action)
    (moved : some (⟨afterRemaining, none, after⟩ : app.Control) ∈
      (app.transition initial horizon (family seed)
        (some ⟨remaining, none, execution⟩) joint).support)
    (owner : Player) (policy : players owner = scheduledProperPolicy clock owner)
    (installed : execution.application.phases.head? = some publicationPhase)
    (active : owner ∉ execution.application.current.excluded)
    (excluded : owner ∈ after.application.current.excluded) : False := by
  have consistent := (app.consistentRecall_policyInvariant players).runRounds (family seed) count
    initialExecution after (fun _ => .nil) reached
  have focal := consistent owner
  rw [policy] at focal
  exact scheduled_proper_publication_exclusion_impossible clock seed remaining execution
    prior afterRemaining
    after trace kept joint moved owner focal installed active excluded

end Vegas.Examples.CommitSeedBroadcast

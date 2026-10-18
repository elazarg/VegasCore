/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingProperRetryExpiry

/-! # Proper initialized play prevents new retry-binding exclusions -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem commitment_request_binding (execution : app.Execution) (event : graph.EventId)
    (owner : Player) (inside : event ∈ commitmentPhase.events)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩) :
    graph.outputLayout event = .binding owner .bool := by
  have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
  change 0 ≤ event.val ∧ event.val < 2 at interval
  have acting : graph.actor? event = some owner := request.2.2.2.1
  fin_cases event
  · change some alice = some owner at acting
    cases Option.some.inj acting
    rfl
  · change some bob = some owner at acting
    cases Option.some.inj acting
    rfl
  · change 0 ≤ 2 ∧ 2 < 2 at interval
    omega
  · change 0 ≤ 3 ∧ 3 < 2 at interval
    omega

/-- A one-step exclusion in a retry commitment block would identify an
actual lost binding expiry on the same initialized proper trajectory.
Request origin and expiry are derived from the raw transition, rather than
assumed delivery or proper behavior of the other owner. -/
theorem fixed_late_retry_exclusion_impossible
    (seed : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (afterRemaining : Nat) (after : app.Execution)
    (afterTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨afterRemaining, none, after⟩))
    (kept : TracePrefix trace afterTrace)
    (joint : Player → Option app.Action)
    (moved : some (⟨afterRemaining, none, after⟩ : app.Control) ∈
      (app.transition initial horizon (family seed)
        (some ⟨remaining, none, execution⟩) joint).support)
    (owner : Player)
    (ownConsistent : (fixedLatePolicy owner).Consistent (after.recall owner))
    (retired : execution.application.attempt ≠ originalAttempt)
    (installed : execution.application.phases.head? = some commitmentPhase)
    (active : owner ∉ execution.application.current.excluded)
    (excluded : owner ∈ after.application.current.excluded) : False := by
  classical
  have head : commitmentPhase ∈ execution.application.phases.head? :=
    Option.mem_def.mpr installed
  obtain ⟨operation, stepped⟩ := PhaseService.new_exclusion_application_command runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed)
      ⟨remaining, none, execution⟩ ⟨afterRemaining, none, after⟩ joint moved owner active
        excluded (by
        intro message next handled
        have same := PhaseRuntimeState.handle_commitment_phase_excluded runtime
          execution.application next commitmentPhase head rfl message handled
        exact fun chosen => active (same ▸ chosen))
  obtain ⟨updated, selected, equal⟩ := PMF.support_map .. ▸ stepped
  obtain ⟨native, supported, stateEq⟩ := PMF.support_map .. ▸ selected
  have afterApplication : after.application = native := by
    exact (congrArg (fun current : app.Execution => current.application) equal).symm.trans
      (congrArg (fun current : app.Execution => current.application) stateEq).symm
  obtain ⟨event, _completedNative, commandEq, inside, request, _nativeStep, _completed,
    _normalized⟩ := PhaseRuntimeState.environment_new_exclusion_request runtime
      execution.application native commitmentPhase head operation supported owner active
        (by simpa only [afterApplication] using excluded)
  have expired : after ∈ (execution.environmentStep app
      (.application (.expire event))).support := by
    rwa [commandEq] at stepped
  have binding := commitment_request_binding execution event owner inside request
  have lost : ¬ after.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩ := by
    intro retained
    exact retained.2.2.2.2 excluded
  exact fixed_late_retry_expiry_impossible seed remaining execution trace afterRemaining after
    afterTrace kept ⟨execution.application.attempt, event⟩ owner ownConsistent retired binding
      request expired lost

/-- The original initialized experiment supplies the retained own-record condition. -/
theorem initialized_fixed_late_retry_exclusion_impossible
    (players : Player → app.Policy) (seed : Seeds) (count : Nat)
    (remaining : Nat) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (afterRemaining : Nat) (after : app.Execution)
    (afterTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨afterRemaining, none, after⟩))
    (kept : TracePrefix trace afterTrace)
    (reached : after ∈ (app.runRounds (family seed) players count initialExecution).support)
    (joint : Player → Option app.Action)
    (moved : some (⟨afterRemaining, none, after⟩ : app.Control) ∈
      (app.transition initial horizon (family seed)
        (some ⟨remaining, none, execution⟩) joint).support)
    (owner : Player) (policy : players owner = fixedLatePolicy owner)
    (retired : execution.application.attempt ≠ originalAttempt)
    (installed : execution.application.phases.head? = some commitmentPhase)
    (active : owner ∉ execution.application.current.excluded)
    (excluded : owner ∈ after.application.current.excluded) : False := by
  have consistent := (app.consistentRecall_policyInvariant players).runRounds (family seed) count
    initialExecution after (fun _ => .nil) reached
  have focal := consistent owner
  rw [policy] at focal
  exact fixed_late_retry_exclusion_impossible seed remaining execution trace afterRemaining after
    afterTrace kept joint moved owner focal retired installed active excluded

end Vegas.Examples.CommitSeedSignalling

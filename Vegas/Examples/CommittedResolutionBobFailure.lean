/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionBobAudit
import Vegas.Pending.EventResolutionEnvironment

/-! # Failed Bob responses cannot recover after the final inclusion -/

noncomputable section

namespace Vegas.Examples.CommittedResolutionBobFailure

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability
open CommittedResolutionService CommittedResolutionReadout CommittedResolutionBobService

/-- Bob's resolve event has no result at any of his legal RAW decision
histories, independently of Alice's earlier messages and application results. -/
theorem bob_prefix_output_none (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    control.execution.application.config.store (.inr bobEvent) = none := by
  have ready := (recovery_bob_phase control trace active).2.2.2.1
  change control.execution.application.config.outputs bobEvent = none
  cases stored : control.execution.application.config.outputs bobEvent with
  | none => rfl
  | some value =>
      exfalso
      apply ready.1
      rw [← control.execution.application.config.output_available, stored]
      rfl

/-- In particular, Bob has no old pending envelope at that decision. -/
theorem bob_prefix_no_pending (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob)
    (message : Message Player app.Payload) (pending : message ∈ control.execution.network.pending) :
    message.sender ≠ bob := by
  intro owned
  have provenance := app.history_provenance (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler trace
  obtain ⟨entry, recalled, _⟩ := provenance.pending message pending
  rw [owned, (recovery_bob_phase control trace active).2.2.1] at recalled
  simp at recalled

/-- Every Bob-authored pending packet after a noncanonical response is
rejected by the actual application. The response may perform arbitrary private
preparation or request arbitrary certificate evidence. -/
theorem bob_pending_response_rejected (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) (response : app.Action)
    (wrong : ∀ material : WitnessedSubmission nativeGraph,
      response.transmission = some material →
        material.call.packet ≠ .opening bobEvent bobCandidate ⟨.bool, true⟩)
    (message : Message Player app.Payload)
    (pending : message ∈ (control.execution.respond app bob response).network.pending)
    (owned : message.sender = bob) :
    app.handle (control.execution.respond app bob response).application message = none := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      exact False.elim (bob_prefix_no_pending control trace active message pending owned)
  | some material =>
      change message ∈ List.append control.execution.network.pending
        [⟨(bob, control.execution.network.nextSerial bob),
          app.packet (app.submit control.execution.application bob material) bob
            (control.execution.network.known bob) material⟩] at pending
      rcases List.mem_append.mp pending with earlier | fresh
      · exact False.elim (bob_prefix_no_pending control trace active message earlier owned)
      · cases List.mem_singleton.mp fresh
        change app.handle (app.submit control.execution.application bob material) _ = none
        cases accepted : app.handle (app.submit control.execution.application bob material)
            ⟨(bob, control.execution.network.nextSerial bob),
              app.packet (app.submit control.execution.application bob material) bob
                (control.execution.network.known bob) material⟩ with
        | none => rfl
        | some next =>
            exact False.elim (wrong material rfl
              ((bob_raw_response_accepts_iff control trace active material).mp ⟨next, accepted⟩))

/-- Noncanonical responses, including silence, cannot succeed at Bob's one
actual inclusion opportunity. No previous pending Bob message can rescue them. -/
theorem bob_rejected_round_no_success (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) (response : app.Action)
    (wrong : ∀ material : WitnessedSubmission nativeGraph,
      response.transmission = some material →
        material.call.packet ≠ .opening bobEvent bobCandidate ⟨.bool, true⟩)
    (next : app.Execution)
    (reached : next ∈ (app.round CommittedResolutionRecovery.scheduler players
      (control.execution.respond app bob response)).support) :
    ∀ value : Bool, next.application.config.store (.inr bobEvent) ≠ some (.success value) := by
  let start := control.execution.respond app bob response
  have cursor : start.environmentRecall.length = 11 := by
    rw [app.respond_environmentRecall, (recovery_bob_phase control trace active).1]
  have before : ∀ value : Bool,
      start.application.config.store (.inr bobEvent) ≠ some (.success value) := by
    have equal := (runtime setup).reactive_respond_application leaks control.execution bob response
    rw [equal.1, bob_prefix_output_none control trace active]
    intro value impossible
    cases impossible
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨observed, environment, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have passive := recovery_after_bob_passive start.environmentRecall
    (start.observeEnvironment app) (by omega) command selected
  change next ∈ (app.resume players (command.actor? app) observed).support at resumed
  rw [passive] at resumed
  have same : next = observed := (PMF.mem_support_pure_iff _ _).mp resumed
  subst next
  have selectedEq : command = (runtime setup).reactiveLatest leaks bobEvent bob
      (start.observeEnvironment app) := by
    simpa only [CommittedResolutionRecovery.scheduler, app.respond_environmentRecall,
      (recovery_bob_phase control trace active).1, show (11 : Nat) ≠ 5 by decide,
      ↓reduceIte, CommittedResolutionService.scheduler, stageChoice,
      PMF.mem_support_pure_iff] using selected
  rcases (runtime setup).reactiveLatest_wait_or_owned leaks bobEvent bob
      (start.observeEnvironment app) with idle | ⟨id, ownedId, inclusion⟩
  · have idleCommand : command = .wait := selectedEq.trans idle
    rw [idleCommand] at environment
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff] at environment
    subst observed
    exact before
  · have includeCommand : command = .include id := selectedEq.trans inclusion
    rw [includeCommand] at environment
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff] at environment
    subst observed
    change ∀ value : Bool,
      (start.includePending app id).application.config.store (.inr bobEvent) ≠
        some (.success value)
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases found : start.network.lookup id with
    | none => exact before
    | some message =>
        have pending : message ∈ start.network.pending := List.mem_of_find?_eq_some found
        have named : message.id = id := by
          simpa only [decide_eq_true_eq] using List.find?_some found
        have owned : message.sender = bob := by
          exact (congrArg Prod.fst named).trans ownedId
        have rejected := bob_pending_response_rejected control trace active response wrong
          message pending owned
        change ∀ value : Bool,
          ((app.handle start.application message).getD start.application).config.store
            (.inr bobEvent) ≠ some (.success value)
        change app.handle start.application message = none at rejected
        rw [rejected]
        exact before

/-- After Bob's sole inclusion, only waiting, clock advancement, and expiry
remain. This is the actual public controller, for arbitrary public views. -/
theorem recovery_after_bob_inclusion (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (later : 12 ≤ past.length) (command : app.Command)
    (selected : command ∈ (CommittedResolutionRecovery.scheduler past view).support) :
    command = .wait ∨ command = .application .advanceClock ∨
      command = .application (.expire bobEvent) := by
  have notLate : past.length ≠ 5 := by omega
  simp only [CommittedResolutionRecovery.scheduler, notLate, ↓reduceIte,
    CommittedResolutionService.scheduler] at selected
  generalize located : past.length = position at later selected
  by_cases inside : position < 16
  · interval_cases position <;>
      simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    all_goals subst command; simp
  · have idle : stageChoice position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, PMF.mem_support_pure_iff] at selected
    exact Or.inl selected

/-- No future policy or scheduler round can recover a successful Bob
publication after the actual final inclusion opportunity has passed. -/
theorem recovery_bob_no_success_suffix (players : Player → app.Policy) (count : Nat)
    (execution final : app.Execution) (later : 12 ≤ execution.environmentRecall.length)
    (before : ∀ value : Bool,
      execution.application.config.store (.inr bobEvent) ≠ some (.success value))
    (reached : final ∈
      (app.runRounds CommittedResolutionRecovery.scheduler players count execution).support) :
    ∀ value : Bool,
      final.application.config.store (.inr bobEvent) ≠ some (.success value) := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact before
  | succ count ih =>
      obtain ⟨next, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have cursor := app.round_environmentRecall_length CommittedResolutionRecovery.scheduler
        players execution next moved
      apply ih next (by omega) _ continued
      obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨observed, environment, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have passive := recovery_after_bob_passive execution.environmentRecall
        (execution.observeEnvironment app) (by omega) command selected
      change next ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [passive] at resumed
      have same : next = observed := (PMF.mem_support_pure_iff _ _).mp resumed
      subst next
      rcases recovery_after_bob_inclusion _ _ later command selected with idle | tick | expiry
      · subst command
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff] at environment
        subst observed
        exact before
      · subst command
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ environment
        obtain ⟨state, primitive, rfl⟩ := PMF.support_map .. ▸ supported
        exact environmentStep_resolution_no_success (runtime setup) execution.application
          state bobEvent bob .bool bobBinding [] rfl rfl rfl .advanceClock before primitive
      · subst command
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ environment
        obtain ⟨state, primitive, rfl⟩ := PMF.support_map .. ▸ supported
        exact environmentStep_resolution_no_success (runtime setup) execution.application
          state bobEvent bob .bool bobBinding [] rfl rfl rfl (.expire bobEvent) before primitive

/-- Every physical horizon outcome after a noncanonical Bob response has
publication failure. This covers silence, wrong values, handles, events,
private preparations, and certificate requests under arbitrary RAW policies. -/
theorem bob_failed_response_at_horizon (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) (response : app.Action)
    (wrong : ∀ material : WitnessedSubmission nativeGraph,
      response.transmission = some material →
        material.call.packet ≠ .opening bobEvent bobCandidate ⟨.bool, true⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds CommittedResolutionRecovery.scheduler players 5
      (control.execution.respond app bob response)).support) :
    final.application.config.store (.inr bobEvent) = some .failure := by
  have firstReached := reached
  rw [ReactiveApplication.runRounds] at firstReached
  obtain ⟨next, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ firstReached)
  have noFirst := bob_rejected_round_no_success players control trace active response wrong
    next moved
  have cursor := app.round_environmentRecall_length CommittedResolutionRecovery.scheduler players
    (control.execution.respond app bob response) next moved
  rw [app.respond_environmentRecall, (recovery_bob_phase control trace active).1] at cursor
  have noFinal := recovery_bob_no_success_suffix players 4 next final (by omega)
    noFirst continued
  have baseTrace := app.trace_of_scheduler_support_subset (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler
      CommittedResolutionService.scheduler
        CommittedResolutionRecovery.scheduler_support_subset trace
  have budget := bob_activation_remaining control baseTrace active
  rcases control with ⟨remaining, actor, execution⟩
  dsimp only at active budget
  subst actor
  subst remaining
  obtain ⟨responded⟩ := app.raw_trace_respond (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler 5 execution bob
      response trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler players 0 5
      (execution.respond app bob response) final responded reached
  have completed := CommittedResolutionRecovery.contract.completes ⟨0, none, final⟩
    finalTrace ⟨rfl, rfl⟩
  have available := final.application.config.store_available_of_terminal completed (.inr bobEvent)
  obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp available
  cases result with
  | failure => exact stored
  | success value => exact False.elim (noFinal value stored)

end Vegas.Examples.CommittedResolutionBobFailure

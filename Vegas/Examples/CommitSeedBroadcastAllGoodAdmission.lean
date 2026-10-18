/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastEligibleResponse
import Vegas.Examples.CommitSeedBroadcastOriginalEarlySuccess
import Vegas.Examples.CommitSeedBroadcastRecordedEmission
import Vegas.Examples.CommitSeedBroadcastFirstLateRecord
import Vegas.Examples.CommitSeedBroadcastEarlyLedger
import Vegas.Examples.CommitSeedBroadcastSubmissionShape

/-! # Original admission from actual all-good first-late responses -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem good_requested_poll (seed : Seeds) (owner : Player)
    (good : seed.2 owner = true) (execution : app.Execution) (remaining : Nat)
    (trace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (position : execution.environmentRecall.length = 5 + (seed.1.symm owner).val) :
    family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate owner) := by
  classical
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have readyOwner : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true := by
    apply decide_eq_true
    change PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, bindingEvent owner⟩
    rw [original]
    exact (execution.application.requests_publicView
      (raw_native_valid (family seed) _ trace) owner
        (originalCoordinate owner)).mpr request
  rw [family, choose_original _ _ _ original, position]
  apply congrArg PMF.pure
  apply (original_command_activation seed owner _ _ _ readyOwner).mpr
  simp [originalTurns, good]

/-- This is a property of the actual response kernel at genuine callbacks,
not a successful-preparation or a later-admission hypothesis. -/
def FirstLateOwnerTransmits (seed : Seeds) (final : app.Execution) (owner : Player) : Prop :=
  ∀ remaining execution
    (_trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (_request : execution.application.SeedRequest owner (originalCoordinate owner))
    (_clock : execution.application.current.native.clock = 2)
    (_empty : execution.receipts = []) first
    (_word : execution.recall owner = [first])
    (_request : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (_silent : first.action.transmission = none)
    (_zero : first.beforeView.application.2.native.clock = 0) entry,
    (∃ after, final.recall owner = execution.recall owner ++ entry :: after) →
    entry.beforeView = execution.observe app owner →
      entry.action.transmission ≠ none

/-- Every owner's recorded first-late transmission rule. -/
def FirstLateRecordedTransmits (seed : Seeds) (final : app.Execution) : Prop :=
  ∀ owner, FirstLateOwnerTransmits seed final owner

theorem rounds_recall_retained (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (before after : app.Execution)
    (reached : after ∈ (app.runRounds selected players count before).support) (owner : Player) :
    before.recall owner <+: after.recall owner := by
  have preserved : app.PolicyInvariant players
      (fun current => before.recall owner <+: current.recall owner) := by
    constructor
    · intro current actor action valid _
      exact valid.trans (app.respond_recall_prefix current actor owner action)
    · intro current next command valid moved
      rw [app.environmentStep_recall current next command moved]
      exact valid
  exact preserved.runRounds selected count before after (List.prefix_refl _) reached

/-- A good owner is admitted by a resolved endpoint of the actual experiment
when its retained first-late response transmits. Other seeds are unrestricted. -/
theorem good_original_admission (seed : Seeds) (owner : Player)
    (good : seed.2 owner = true)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (final : app.Execution)
    (transmits : FirstLateOwnerTransmits seed final owner)
    (reached : final ∈ (app.runRounds (family seed) players horizon initialExecution).support)
    (resolved : ∀ who, (originalCoordinate who).Resolved final.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  obtain ⟨finalTrace⟩ := countedMenu.trace_roundsFrom initial horizon (family seed) players
    covered horizon (by omega) final (by
      simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
        using reached)
  simp only [Nat.sub_self] at finalTrace
  by_contra unaccepted
  let index := 5 + (seed.1.symm owner).val
  have rankBound := (seed.1.symm owner).isLt
  have small : index < 28 := by dsimp only [index]; omega
  have bound : index < horizon := by dsimp only [horizon, index]; omega
  have split : horizon = index + (horizon - index) := by omega
  have initialized := reached
  rw [split, app.runRounds_add] at initialized
  obtain ⟨before, prior, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ initialized)
  have position : before.environmentRecall.length = index := by
    have length := app.runRounds_environmentRecall_length (family seed) players index
      initialExecution before prior
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  obtain ⟨beforeTrace⟩ := countedMenu.trace_roundsFrom initial horizon (family seed) players
    covered index (by omega) before (by
      simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
        using prior)
  have beforeUnaccepted : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner before := fun accepted => unaccepted (original_binding_accepted_runRounds
        (family seed) players _ before final future owner accepted)
  have request := original_request_of_unaccepted_before_expiry seed _
    (countedMenu.toRawTrace initial horizon (family seed) beforeTrace) owner beforeUnaccepted
      (by rw [position]; exact small)
  have selected := good_requested_poll seed owner good before _
    (countedMenu.toRawTrace initial horizon (family seed) beforeTrace) request position
  have rest : horizon - index = (horizon - index - 1) + 1 := by omega
  rw [rest] at future
  change final ∈ ((app.round (family seed) players before).bind
    (app.runRounds (family seed) players (horizon - index - 1))).support at future
  obtain ⟨middle, firstRound, following⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ future)
  rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
    completeActivation_law, PMF.pure_bind] at firstRound
  change middle ∈ ((players owner _ _).map _).support at firstRound
  obtain ⟨action, chosen, sameMiddle⟩ := (PMF.mem_support_map_iff _ _ _).mp firstRound
  subst middle
  let observed := completeActivation before owner
  have remaining : horizon - index = (horizon - index - 1) + 1 := rest
  rw [remaining] at beforeTrace
  obtain ⟨activeTrace⟩ := countedMenu.trace_environment initial horizon (family seed)
    (horizon - index - 1) before observed (.activate owner) beforeTrace
      (by rw [selected]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      (by rw [completeActivation_law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have observedRequest : observed.application.SeedRequest owner (originalCoordinate owner) :=
    request
  have original : observed.application.attempt = originalAttempt := request.1.symm
  have clock : observed.application.current.native.clock = 2 := by
    have counted := original_clock_index seed _
      (countedMenu.toRawTrace initial horizon (family seed) activeTrace) original
    rw [counted]
    change originalClock observed.environmentRecall.length = 2
    have observedPosition : observed.environmentRecall.length =
        before.environmentRecall.length + 1 := by
      simp only [observed, completeActivation, ReactiveApplication.Execution.sampledActivation,
        List.length_append, List.length_singleton]
    rw [observedPosition, position]
    dsimp only [index]
    generalize rankEq : seed.1.symm owner = rank
    fin_cases rank <;> rfl
  have empty := original_good_firstLate_receipts_empty seed _
    (countedMenu.toRawTrace initial horizon (family seed) activeTrace) owner rfl original clock
      good
  obtain ⟨first, word, _view, firstRequest, zero⟩ := original_first_late_initial_record seed
    (horizon - index - 1) observed owner
      (countedInRaw.trace initial horizon (family seed) activeTrace) original clock empty
  have offered := covered owner (observed.recall owner) (observed.observe app owner) action chosen
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed)
    (horizon - index - 1) observed owner action activeTrace offered
  have silent : first.action.transmission = none := by
    cases emitted : first.action.transmission with
    | none => rfl
    | some material =>
        have firstMember : first ∈ (observed.respond app owner action).recall owner :=
          (app.respond_recall_prefix observed owner owner action).subset (by
            rw [word]; exact List.mem_singleton_self _)
        have initialClock := original_recorded_transmission_clock seed _ _ responded owner first
          firstMember firstRequest material emitted 0 zero
        obtain ⟨packet, packetMember, atZero⟩ := List.mem_map.mp initialClock
        have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu
          initial horizon (family seed) _ _ responded
        have retained := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks
          (family seed) players _ (observed.respond app owner action) final words following owner
            (originalCoordinate owner)
        have retainedPacket := retained.subset packetMember
        have zeroPacket : (0, packet.2) ∈ (PhaseSeedScheduler.localInput runtime leaks
            (originalCoordinate owner) owner final.environmentRecall
              (final.observeEnvironment app)).emissions := by
          simpa only [← atZero] using retainedPacket
        exact (unaccepted (original_clock_zero_emission_resolved_accepted seed 0 final finalTrace
          owner (resolved owner) packet.2 zeroPacket)).elim
  obtain ⟨emitted, recalled⟩ := app.respond_recall_entry observed owner action
  let entry : app.PlayerEntry := ⟨observed.observe app owner, action, emitted⟩
  obtain ⟨later, laterWord⟩ :=
    rounds_recall_retained (family seed) players _ _ final following owner
  have entryRecorded : ∃ later, final.recall owner = observed.recall owner ++ entry :: later := by
    refine ⟨later, ?_⟩
    rw [← laterWord, recalled]
    exact List.append_assoc _ _ _
  have emits := transmits _ observed activeTrace observedRequest clock empty first word
    firstRequest silent zero entry entryRecorded rfl
  cases materialEq : action.transmission with
  | none => exact emits materialEq
  | some material =>
      have actionEq : action = ⟨some material⟩ := by cases action; exact congrArg _ materialEq
      subst action
      have nativeRequest : observed.application.SeedRequest owner
          ⟨observed.application.attempt, bindingEvent owner⟩ := by
        simpa only [original, originalCoordinate] using observedRequest
      obtain ⟨serial, preparation, evidence, materialShape, _bounded, _fresh⟩ :=
        counted_submission_binding_shape (family seed) _ observed owner activeTrace
          (bindingEvent owner) .bool (bindingEvent_layout owner) nativeRequest material offered
      have named : material.call.packet.event? graph = some (bindingEvent owner) := by
        rw [materialShape]; rfl
      exact unaccepted (original_eligible_response_resolved_accepted seed _ observed owner
        activeTrace observedRequest (by simpa only [good, lateClock, ite_true] using clock) material
          offered named players covered final following (resolved owner))

/-- Every original binding is admitted in the all-good experiment under the
actual recorded transmission rule, independently of its private preparation. -/
theorem allGood_original_admission (seed : Seeds) (good : ∀ who, seed.2 who = true)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (final : app.Execution) (transmits : FirstLateRecordedTransmits seed final)
    (reached : final ∈ (app.runRounds (family seed) players horizon initialExecution).support)
    (resolved : ∀ who, (originalCoordinate who).Resolved final.application) :
    ∀ who, PhaseService.BindingAccepted runtime leaks (originalCoordinate who) who final := by
  intro owner
  exact good_original_admission seed owner (good owner) players covered final (transmits owner)
    reached resolved

end Vegas.Examples.CommitSeedBroadcast

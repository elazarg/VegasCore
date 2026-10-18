/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInitializedHalf
import Vegas.Examples.CommitSeedSignallingOriginalCalendar
import Vegas.Examples.CommitSeedSignallingTimingIncentives
import Vegas.Pending.PhaseReadyResolution

/-! # Actual initialized ready requests at the first late polls -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem pending_not_application (identifier : MessageId Player)
    (view : app.EnvironmentView) (command : EnvironmentCommand graph) :
    pendingCommand identifier view ≠ (.application command : app.Command) := by
  unfold pendingCommand
  split <;> intro impossible <;> cases impossible

private theorem activate_not_application (owner : Player) (event : graph.EventId)
    (view : app.EnvironmentView) (command : EnvironmentCommand graph) :
    activateReady owner event view ≠ (.application command : app.Command) := by
  unfold activateReady
  split <;> intro impossible <;> cases impossible

private theorem poll_not_application (owner : Player) (bit wanted : Bool)
    (view : app.EnvironmentView) (command : EnvironmentCommand graph) :
    pollCommand owner bit wanted view ≠ (.application command : app.Command) := by
  unfold pollCommand
  split
  · exact activate_not_application owner (bindingEvent owner) view command
  · intro impossible
    cases impossible

private theorem early_not_application (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (command : EnvironmentCommand graph) :
    earlyCommand owner past view ≠ (.application command : app.Command) := by
  unfold earlyCommand
  split
  · intro impossible; cases impossible
  · split
    · intro impossible; cases impossible
    · exact pending_not_application _ view command

private theorem late_not_application (owner : Player) (bit : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : EnvironmentCommand graph) :
    lateCommand owner bit clock past view ≠ (.application command : app.Command) := by
  unfold lateCommand
  split
  · split
    · intro impossible; cases impossible
    · exact pending_not_application _ view command
  · intro impossible; cases impossible

/-- No command before the first late poll can resolve either original binding.
Arbitrary bounded private responses at the two initial callbacks are retained. -/
theorem original_request_before_first_poll (players : Player → app.Policy)
    (seed : Seeds) (count : Nat) (early : count ≤ 4)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players count initialExecution).support)
    (owner : Player) : execution.application.SeedRequest owner (originalCoordinate owner) := by
  classical
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      change initialState.SeedRequest owner ⟨originalAttempt, bindingEvent owner⟩
      exact initial_binding_request owner
  | succ count induction =>
      rw [app.runRounds_succ_eq_bind_round, PMF.support_bind] at reached
      obtain ⟨before, beforeReached, moved⟩ := Set.mem_iUnion₂.mp reached
      have requested := induction (by omega) before beforeReached
      have original : before.application.attempt = originalAttempt := requested.1.symm
      have length := app.runRounds_environmentRecall_length (family seed) players count
        initialExecution before beforeReached
      have countEq : before.environmentRecall.length = count := by
        simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
          Nat.zero_add] using length
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      have selectedEq : command = originalCommand seed count before.environmentRecall
          (before.observeEnvironment app) := by
        rw [family_apply, choose_original seed _ _ original, countEq] at selected
        exact (PMF.mem_support_pure_iff _ _).mp selected
      have small : count ≤ 3 := by omega
      have clockNotExpiry : (ReactiveApplication.Command.application .advanceClock : app.Command) ≠
          .application (.expire (bindingEvent owner)) := by
        intro impossible
        have same := ReactiveApplication.Command.application.inj impossible
        change (EnvironmentCommand.advanceClock : EnvironmentCommand graph) =
          .expire (bindingEvent owner) at same
        cases same
      have notExpiry : command ≠ .application (.expire (bindingEvent owner)) := by
        rw [selectedEq]
        interval_cases count
        · change activateReady alice aliceBinding _ ≠ _
          unfold activateReady
          split <;> intro impossible <;> cases impossible
        · change activateReady bob bobBinding _ ≠ _
          unfold activateReady
          split <;> intro impossible <;> cases impossible
        · exact clockNotExpiry
        · exact clockNotExpiry
      have notInclude (identifier : MessageId Player) : command ≠ .include identifier := by
        rw [selectedEq]
        interval_cases count
        · change activateReady alice aliceBinding _ ≠ _
          unfold activateReady
          split <;> intro impossible <;> cases impossible
        · change activateReady bob bobBinding _ ≠ _
          unfold activateReady
          split <;> intro impossible <;> cases impossible
        · intro impossible; cases impossible
        · intro impossible; cases impossible
      obtain ⟨observed, environmentMoved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have originRun : before ∈ (app.roundsFrom initial (family seed) players count).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using beforeReached
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom initial horizon (family seed) players count
        (by change count ≤ 64; omega) before originRun
      have valid := raw_native_valid (family seed) ⟨horizon - count, none, before⟩ trace
      have retained := environment_request_or_own_resolution runtime leaks
        (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
        before observed valid owner (originalCoordinate owner) requested command environmentMoved
      have observedRequest : observed.application.SeedRequest owner (originalCoordinate owner) :=
        by
          rcases retained with retained | expired | included
          · exact retained
          · exact (notExpiry expired).elim
          · obtain ⟨identifier, _, _, _, _, included, _⟩ := included
            exact (notInclude identifier included).elim
      cases actorEq : command.actor? app with
      | none =>
          change execution ∈ (app.resume players (command.actor? app) observed).support at resumed
          rw [actorEq] at resumed
          cases (PMF.mem_support_pure_iff _ _).mp resumed
          exact observedRequest
      | some actor =>
          change execution ∈ (app.resume players (command.actor? app) observed).support at resumed
          rw [actorEq] at resumed
          obtain ⟨action, _chosen, rfl⟩ := PMF.support_map .. ▸ resumed
          exact respond_request runtime leaks observed actor action owner _ observedRequest

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

/-- Passive initial clock advances retain the complete quiet own recall. -/
theorem quiet_before_first_poll_recall (seed : Seeds)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (count : Nat) (late : 2 ≤ count) (early : count ≤ 4) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players count initialExecution).support) :
    execution.recall = quietAfterTwo.recall := by
  classical
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le late
  induction extra generalizing execution with
  | zero =>
      rw [Nat.add_zero, quiet_first_two_rounds players seed aliceWait bobWait] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ extra induction =>
      rw [show 2 + (extra + 1) = (2 + extra) + 1 by omega,
        app.runRounds_succ_eq_bind_round, PMF.support_bind] at reached
      obtain ⟨before, prior, moved⟩ := Set.mem_iUnion₂.mp reached
      have recalled : before.recall = quietAfterTwo.recall := by
        apply induction
        all_goals omega
      have request := original_request_before_first_poll players seed (2 + extra) (by omega)
        before prior alice
      have original : before.application.attempt = originalAttempt := request.1.symm
      have length := app.runRounds_environmentRecall_length (family seed) players (2 + extra)
        initialExecution before prior
      have countEq : before.environmentRecall.length = 2 + extra := by
        simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
          Nat.zero_add] using length
      have command : family seed before.environmentRecall (before.observeEnvironment app) =
          PMF.pure (.application .advanceClock) := by
        rw [family_apply, choose_original seed _ _ original, countEq]
        have small : extra ≤ 1 := by omega
        interval_cases extra <;> rfl
      rw [ReactiveApplication.round, command, PMF.pure_bind,
        ReactiveApplication.dispatch, PMF.support_bind] at moved
      obtain ⟨observed, environmentMoved, resumed⟩ := Set.mem_iUnion₂.mp moved
      have same : execution = observed := (PMF.mem_support_pure_iff _ _).mp resumed
      rw [same]
      exact (app.environmentStep_recall before observed (.application .advanceClock)
        environmentMoved).trans recalled

/-- Until the first Bob poll, no Bob packet exists and his original request
cannot be resolved by any Alice response or actual network inclusion. -/
theorem quiet_bob_before_first_poll (seed : Seeds)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (count : Nat) (late : 2 ≤ count) (early : count ≤ 12) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players count initialExecution).support) :
    execution.application.SeedRequest bob (originalCoordinate bob) ∧
      execution.recall bob = quietAfterTwo.recall bob := by
  classical
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le late
  induction extra generalizing execution with
  | zero =>
      rw [Nat.add_zero, quiet_first_two_rounds players seed aliceWait bobWait] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      constructor
      · change initialState.SeedRequest bob ⟨originalAttempt, bindingEvent bob⟩
        exact initial_binding_request bob
      · rfl
  | succ extra induction =>
      rw [show 2 + (extra + 1) = (2 + extra) + 1 by omega,
        app.runRounds_succ_eq_bind_round, PMF.support_bind] at reached
      obtain ⟨before, prior, moved⟩ := Set.mem_iUnion₂.mp reached
      have previous : before.application.SeedRequest bob (originalCoordinate bob) ∧
          before.recall bob = quietAfterTwo.recall bob := by
        apply induction
        all_goals omega
      obtain ⟨requested, recalled⟩ := previous
      have original : before.application.attempt = originalAttempt := requested.1.symm
      have length := app.runRounds_environmentRecall_length (family seed) players (2 + extra)
        initialExecution before prior
      have countEq : before.environmentRecall.length = 2 + extra := by
        simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
          Nat.zero_add] using length
      obtain ⟨trace⟩ := counted_profile_trace profile seed (2 + extra)
        (by change 2 + extra ≤ 64; omega) before prior
      have rawTrace := countedMenu.toRawTrace initial horizon (family seed) trace
      have valid := raw_native_valid (family seed) ⟨horizon - (2 + extra), none, before⟩ rawTrace
      have readyBob : ready bob (bindingEvent bob) (before.observeEnvironment app) = true := by
        change decide (PhaseRuntimeState.requests before.application.publicView bob
          ⟨before.application.attempt, bindingEvent bob⟩) = true
        apply decide_eq_true
        apply (before.application.requests_publicView valid bob _).mpr
        simpa only [original, originalCoordinate] using requested
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      have selectedEq : command = originalCommand seed (2 + extra) before.environmentRecall
          (before.observeEnvironment app) := by
        rw [family_apply, choose_original seed _ _ original, countEq] at selected
        exact (PMF.mem_support_pure_iff _ _).mp selected
      have notBob : command.actor? app ≠ some bob := by
        intro active
        have commandEq : command = .activate bob := by
          cases command with
          | activate actor =>
              have same : actor = bob := Option.some.inj active
              cases same
              rfl
          | «include» identifier => cases active
          | wait => cases active
          | application native => cases active
        have turn := (original_command_activation seed bob (2 + extra) before.environmentRecall
          (before.observeEnvironment app) readyBob).mp (selectedEq.symm.trans commandEq)
        change 2 + extra ∈ [1, if seed.2 (originalAddress bob) then 14 else 12, 17] at turn
        rcases List.mem_cons.mp turn with first | later
        · omega
        · rcases List.mem_cons.mp later with middle | last
          · cases bit : seed.2 (originalAddress bob)
            · rw [bit] at middle
              change 2 + extra = 12 at middle
              omega
            · rw [bit] at middle
              change 2 + extra = 14 at middle
              omega
          · have lastEq := List.mem_singleton.mp last
            omega
      have notExpiry : command ≠ .application (.expire (bindingEvent bob)) := by
        rw [selectedEq]
        have bound : extra ≤ 9 := by omega
        have clockNotExpiry :
            (ReactiveApplication.Command.application .advanceClock : app.Command) ≠
              .application (.expire (bindingEvent bob)) := by
          intro impossible
          have same := ReactiveApplication.Command.application.inj impossible
          change (EnvironmentCommand.advanceClock : EnvironmentCommand graph) =
            .expire (bindingEvent bob) at same
          cases same
        interval_cases extra
        · exact clockNotExpiry
        · exact clockNotExpiry
        · exact poll_not_application alice _ false _ _
        · exact early_not_application bob _ _ _
        · exact poll_not_application alice _ true _ _
        · exact late_not_application alice _ 2 _ _ _
        · exact clockNotExpiry
        · exact activate_not_application alice aliceBinding _ _
        · exact late_not_application alice _ 3 _ _ _
        · exact clockNotExpiry
      obtain ⟨observed, environmentMoved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have retained := environment_request_or_own_resolution runtime leaks
        (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
        before observed valid bob (originalCoordinate bob) requested command environmentMoved
      have observedRequest : observed.application.SeedRequest bob (originalCoordinate bob) := by
        rcases retained with retained | expired | included
        · exact retained
        · exact (notExpiry expired).elim
        · obtain ⟨identifier, message, _native, _ready, _action, _included, found, sender, _rest⟩ :=
            included
          have provenance := app.history_provenance initial horizon (family seed) rawTrace
          have issued := provenance.pending message (List.mem_of_find?_eq_some found)
          obtain ⟨entry, member, _material, _sent, emitted, _packet⟩ := issued
          rw [sender] at member
          have output : message ∈ app.outputs (before.recall bob) :=
            List.mem_filterMap.mpr ⟨entry, member, emitted⟩
          rw [recalled] at output
          have empty : app.outputs (quietAfterTwo.recall bob) = [] := rfl
          rw [empty] at output
          exact (List.not_mem_nil output).elim
      have observedRecall : observed.recall bob = quietAfterTwo.recall bob := by
        rw [app.environmentStep_recall before observed command environmentMoved]
        exact recalled
      cases acting : command.actor? app with
      | none =>
          change execution ∈ (app.resume players (command.actor? app) observed).support at resumed
          rw [acting] at resumed
          have same : execution = observed := (PMF.mem_support_pure_iff _ _).mp resumed
          rw [same]
          exact ⟨observedRequest, observedRecall⟩
      | some actor =>
          have different : bob ≠ actor := by
            intro same
            exact notBob (acting.trans (congrArg some same.symm))
          change execution ∈ (app.resume players (command.actor? app) observed).support at resumed
          rw [acting] at resumed
          obtain ⟨action, _positive, rfl⟩ := PMF.support_map .. ▸ resumed
          refine ⟨respond_request runtime leaks observed actor action bob _ observedRequest, ?_⟩
          rw [app.respond_recall_other observed actor bob different action]
          exact observedRecall

/-- The initialized first late input retains its genuine old namespace and
quiet own word. The earlier other-owner service has not consumed this request. -/
theorem original_first_poll_request_recall (seed : Seeds) (owner : Player)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players (firstLatePosition owner)
      initialExecution).support) :
    execution.application.SeedRequest owner (originalCoordinate owner) ∧
      execution.recall owner = quietAfterTwo.recall owner := by
  fin_cases owner
  · refine ⟨original_request_before_first_poll players seed 4 le_rfl execution reached alice, ?_⟩
    exact congrFun (quiet_before_first_poll_recall profile seed aliceWait bobWait 4
      (by decide) le_rfl execution reached) alice
  · exact quiet_bob_before_first_poll profile seed aliceWait bobWait 12
      (by decide) le_rfl execution reached

end Counted

end Vegas.Examples.CommitSeedSignalling

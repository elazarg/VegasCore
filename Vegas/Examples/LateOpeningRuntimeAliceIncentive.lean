/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceDecision
import Interaction.ReactivePassiveContinuation
import Interaction.ReactiveEmissionOrder

/-! # Quiet continuation incentives for arbitrary genuine first-opening histories

The previous opening may use any private submission syntax. Only its actual
signed envelope, the existing immutable binding and the actual callback state
enter the comparison. Future Bob policies are unrestricted. Failed lottery
inclusion can lose both the source forfeit and Alice's audit deposit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceIncentive

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeRetryAudit
  LateOpeningRuntimeAliceDecision LateOpeningRuntimeUtility

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- The public scheduler has no Alice activation after her remaining late
response. Bob can still act and arbitrary passive settlement remains. -/
theorem alice_absent (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (later : 8 ≤ past.length) (command : app.Command)
    (selected : command ∈
      (LateOpeningRuntimeService.scheduler weight nonnegative past view).support) :
    command.actor? app ≠ some alice := by
  change command ∈ (stageChoice weight nonnegative past.length view).support at selected
  generalize located : past.length = position at later selected
  by_cases inside : position < 26
  · interval_cases position
    all_goals simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    case «8» =>
      have passive := (lottery_passive weight nonnegative view command selected).1
      rw [passive]
      simp
    case «12» | «20» =>
      rw [selected, (latestAuthor_passive bob view).1]
      simp
    case «13» | «14» =>
      split at selected
      · rw [selected]
        first
        | exact (by decide : (some bob : Option Player) ≠ some alice)
        | rw [(latestAuthor_passive bob view).1]; simp
      · subst command
        simp [ReactiveApplication.Command.actor?]
    all_goals subst command; simp [ReactiveApplication.Command.actor?, alice, bob]
  · have idle : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, PMF.mem_support_pure_iff] at selected
    subst command
    simp [ReactiveApplication.Command.actor?]

def continuation (decision : DecisionHistory weight nonnegative) (response : app.Action)
    (players : Player → app.Policy) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
    (decision.execution.respond app alice response)

def waiting (decision : DecisionHistory weight nonnegative) : app.Execution :=
  decision.execution.respond app alice ⟨none⟩

def accepted (decision : DecisionHistory weight nonnegative) : app.Execution :=
  let execution := waiting weight nonnegative decision
  { execution.includePending app (alice, 0) with environmentRecall :=
    execution.environmentRecall ++ [⟨execution.observeEnvironment app, .include (alice, 0)⟩] }

def omitted (decision : DecisionHistory weight nonnegative) : app.Execution :=
  recorded (waiting weight nonnegative decision) .wait decision.execution.application

def quietLaw (decision : DecisionHistory weight nonnegative) (players : Player → app.Policy) :
    PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (quietAgainst players) 18 (waiting weight nonnegative decision)

def secondLaw (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (players : Player → app.Policy) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
    (decision.execution.respond app alice ⟨some submission⟩)

/-- Replacing only Alice's future policy by silence preserves the actual
continuation, since the remaining scheduler never activates her. -/
theorem quietLaw_eq_continuation (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) :
    quietLaw weight nonnegative decision players =
      continuation weight nonnegative decision ⟨none⟩ players := by
  apply app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative) (quietAgainst players) players
  · intro who different
    exact ite_eq_right different
  · change 8 ≤ decision.execution.environmentRecall.length
    rw [decision_cursor]

theorem secondLaw_eq_continuation (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (players : Player → app.Policy) :
    secondLaw weight nonnegative decision submission players =
      continuation weight nonnegative decision ⟨some submission⟩ players := rfl

private theorem lookup_waiting (decision : DecisionHistory weight nonnegative) :
    (waiting weight nonnegative decision).network.lookup (alice, 0) =
      some (openingMessage decision.bit) := by
  change decision.execution.network.lookup (alice, 0) = _
  rw [MessageNetwork.lookup, decision.pending]
  rfl

private theorem handle_waiting (decision : DecisionHistory weight nonnegative) :
    app.handle (waiting weight nonnegative decision).application (openingMessage decision.bit) =
      some (decision.execution.application.complete aliceEvent decision.ready true
        (.success decision.bit)) := by
  rw [LateOpeningRuntimeService.runtime.reactiveApplication_handle_of_tokenValid leaks
    _ _ (by rfl)]
  exact handle_opening_eq LateOpeningRuntimeService.runtime decision.execution.application
    (alice, 0) aliceEvent aliceCandidate alice .bool aliceBinding [] rfl rfl rfl
      decision.ready decision.timely rfl rfl decision.associated decision.bit decision.fixed
        decision.bound (.success decision.bit)
          (by rw [EventCode.resolveOutput?, decision.bound]; rfl)

private theorem accepted_physical (decision : DecisionHistory weight nonnegative) :
    (accepted weight nonnegative decision).application =
      decision.execution.application.complete aliceEvent decision.ready true
        (.success decision.bit) := by
  change ((waiting weight nonnegative decision).includePending app (alice, 0)).application = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, lookup_waiting]
  change (app.handle (waiting weight nonnegative decision).application
    (openingMessage decision.bit)).getD _ = _
  rw [handle_waiting]
  rfl

private theorem accepted_receipt (decision : DecisionHistory weight nonnegative) :
    ((alice, 0), true) ∈ (accepted weight nonnegative decision).receipts := by
  change ((alice, 0), true) ∈
    ((waiting weight nonnegative decision).includePending app (alice, 0)).receipts
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, lookup_waiting]
  change ((alice, 0), true) ∈ (waiting weight nonnegative decision).receipts ++
    [((alice, 0), (app.handle (waiting weight nonnegative decision).application
      (openingMessage decision.bit)).isSome)]
  rw [handle_waiting]
  exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem accepted_inputs (decision : DecisionHistory weight nonnegative) :
    (accepted weight nonnegative decision).network.inputs = [openingMessage decision.bit] := by
  have same : (accepted weight nonnegative decision).network.inputs =
      (waiting weight nonnegative decision).network.inputs := by
    change ((waiting weight nonnegative decision).includePending app (alice, 0)).network.inputs = _
    unfold ReactiveApplication.Execution.includePending
    rw [MessageNetwork.includePending, lookup_waiting]
  exact same.trans decision.inputs

theorem lottery_round (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (waiting weight nonnegative decision) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (accepted weight nonnegative decision))
        (PMF.pure (omitted weight nonnegative decision)) := by
  have cursor : (waiting weight nonnegative decision).environmentRecall.length = 8 :=
    decision_cursor weight nonnegative decision
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative
      (waiting weight nonnegative decision).environmentRecall
      ((waiting weight nonnegative decision).observeEnvironment app) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (.include (alice, 0))) (PMF.pure .wait) := by
    rw [LateOpeningRuntimeService.scheduler, cursor]
    change (MessageNetwork.chooseWithOutside weight nonnegative
      (MessageNetwork.pendingIds decision.execution.network.pending)).map _ = _
    rw [decision.pending]
    change (MessageNetwork.chooseWithOutside weight nonnegative {(alice, 0)}).map _ = _
    rw [MessageNetwork.chooseWithOutside]
    simp only [Finset.card_singleton]
    rw [MessageNetwork.chooseUniform_singleton, mix_map, PMF.pure_map, PMF.pure_map]
    rfl
  rw [ReactiveApplication.round, chosen, mix_bind, PMF.pure_bind, PMF.pure_bind]
  congr 1
  · simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  · simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    rw [recorded_wait, PMF.pure_bind]
    rfl

private theorem accepted_trace (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative) (players : Player → app.Policy) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨17, none, accepted weight nonnegative decision⟩)) := by
  obtain ⟨quiet⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
      ⟨none⟩ decision.trace
  apply app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 17
      (waiting weight nonnegative decision) _ quiet
  rw [lottery_round]
  exact mem_support_mix_left (inclusionProbability weight)
    (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
    (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
    (by unfold inclusionProbability MessageNetwork.inclusionMass; positivity) (by simp)

theorem accepted_quiet_nonnegative (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative) (players : Player → app.Policy)
    {reward : ℝ} (rewardNonnegative : 0 ≤ reward) (forfeit : ℝ) (deposit : Player → ℝ)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (quietAgainst players) 17 (accepted weight nonnegative decision)).support) :
    0 ≤ aliceUtility reward forfeit deposit execution := by
  obtain ⟨prior⟩ := accepted_trace weight nonnegative positive decision (quietAgainst players)
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (quietAgainst players) 0 17
      (accepted weight nonnegative decision) execution prior reached
  have published : (accepted weight nonnegative decision).application.config.store
      (.inr aliceEvent) = some (.success decision.bit) := by
    rw [accepted_physical]
    change (decision.execution.application.complete aliceEvent decision.ready true
      (.success decision.bit)).config.outputs aliceEvent = _
    simp [EventGraphRuntime.State.complete, Config.complete]
  have retained := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr aliceEvent)
      (.success decision.bit)) (quietAgainst players)).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 17 _ execution published reached
  have only : OnlyAlicePacket decision.bit (accepted weight nonnegative decision) := by
    intro message member _
    rw [accepted_inputs] at member
    exact List.mem_singleton.mp member
  have after := (quiet_onlyAlicePacket decision.bit players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 17 _ execution only reached
  have receipt := (app.receipt_policyInvariant (quietAgainst players) ((alice, 0), true)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 17 _ execution
      (accepted_receipt weight nonnegative decision) reached
  have charged : TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
        (fun actual => PMF.pure actual)) (app.finished execution) alice = 0 := by
    apply alice_audit_charge_zero (fun actual => PMF.pure actual)
    · intro actual observed supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact List.Subset.refl _
    · intro traffic member owner
      have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) trace
      change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
        execution.network.inputs at inputs
      have submitted : traffic.envelope ∈ execution.network.inputs := by
        rw [← inputs]
        exact List.mem_map.mpr ⟨traffic, member, rfl⟩
      rw [after traffic.envelope submitted owner]
      exact accepted_alice_opening_permitted _ (alice, 0) decision.bit (some ⟨aliceEvent⟩) receipt
  unfold aliceUtility TerminalAudit.utility
  rw [charged, zero_mul, sub_zero]
  exact completed_opening_base_nonnegative rewardNonnegative forfeit weight nonnegative
    ⟨0, none, execution⟩ trace ⟨rfl, rfl⟩ decision.bit retained

theorem quiet_payoff_lower (positive : 0 < weight) (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) :
    -(1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      expect (quietLaw weight nonnegative decision players)
        (aliceUtility reward forfeit deposit) := by
  let scheduler := LateOpeningRuntimeService.scheduler weight nonnegative
  let yes := app.runRounds scheduler (quietAgainst players) 17
    (accepted weight nonnegative decision)
  let no := app.runRounds scheduler (quietAgainst players) 17 (omitted weight nonnegative decision)
  have acceptedBound : 0 ≤ expect yes (aliceUtility reward forfeit deposit) := by
    apply expect_nonneg
    intro execution reached
    exact accepted_quiet_nonnegative weight nonnegative positive decision players
      rewardNonnegative forfeit deposit execution reached
  have omittedBound : -forfeit - deposit alice ≤
      expect no (aliceUtility reward forfeit deposit) := by
    have comparison := expect_mono (μ := no) (f := fun _ => -forfeit - deposit alice)
      (g := aliceUtility reward forfeit deposit)
      (fun execution _ => (aliceUtility_bounds rewardNonnegative forfeitNonnegative
        deposit depositNonnegative execution).1)
      (payoffIntegrable_constant no (-forfeit - deposit alice))
      (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative no)
    simpa only [expect_constant] using comparison
  unfold quietLaw
  rw [ReactiveApplication.runRounds, lottery_round, mix_bind, PMF.pure_bind, PMF.pure_bind,
    expect_mix _ _ _ _ _ _
      (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative yes)
      (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative no)]
  have first := mul_nonneg
    (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1) acceptedBound
  have second := mul_le_mul_of_nonneg_left omittedBound
    (sub_nonneg.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le)
  linarith

theorem extra_payoff_upper (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (players : Player → app.Policy) {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) :
    expect (secondLaw weight nonnegative decision submission players)
      (aliceUtility reward forfeit deposit) ≤ reward - deposit alice := by
  apply expect_le_const _ _
    (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative _) _
  intro execution reached
  have own := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  change decision.execution.InputRecall app at own
  have ordered := app.emissionOrder_history (LateOpeningRuntimeService.scheduler weight nonnegative)
    initial LateOpeningRuntimeService.horizon decision.trace
  change decision.execution.EmissionOrder app at ordered
  have counter := congrArg List.length (ordered alice)
  rw [List.length_map, List.length_map, List.length_range, ← own alice, decision.inputs] at counter
  have serial : decision.execution.network.nextSerial alice = 1 := by
    simpa [openingMessage, Message.sender] using counter.symm
  let packet : Message Player app.Payload :=
    ⟨(alice, 1), app.packet (app.submit decision.execution.application alice submission) alice
      (decision.execution.network.known alice) submission⟩
  have inputs : (decision.execution.respond app alice ⟨some submission⟩).network.inputs =
      [openingMessage decision.bit, packet] := by
    change decision.execution.network.inputs ++ [⟨(alice,
      decision.execution.network.nextSerial alice), _⟩] = _
    rw [decision.inputs, serial]
    rfl
  obtain ⟨after⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
      ⟨some submission⟩ decision.trace
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 18 _ execution after reached
  have firstPresent := (input_persists players (openingMessage decision.bit)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 _ execution
      (by rw [inputs]; simp) reached
  have secondPresent := (input_persists players packet).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 _ execution
      (by rw [inputs]; simp) reached
  have traffic := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
    execution.network.inputs at traffic
  rw [← traffic] at firstPresent secondPresent
  obtain ⟨first, firstMember, firstEnvelope⟩ := List.mem_map.mp firstPresent
  obtain ⟨second, secondMember, secondEnvelope⟩ := List.mem_map.mp secondPresent
  exact alice_two_envelopes_utility_bound rewardNonnegative forfeitNonnegative deposit
    depositNonnegative weight nonnegative ⟨0, none, execution⟩ trace ⟨rfl, rfl⟩ first second
      firstMember secondMember (by rw [firstEnvelope]; rfl) (by rw [secondEnvelope]; rfl)
      (by rw [firstEnvelope, secondEnvelope]; change (alice, 0) ≠ (alice, 1); decide)

/-- A uniform margin valid throughout an actual information class, preserving
every previous private raw action and unrestricted future Bob behavior. -/
theorem quiet_second_packet_regret (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (players alternatives : Player → app.Policy) {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) :
    deposit alice - reward - (1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      expect (quietLaw weight nonnegative decision players) (aliceUtility reward forfeit deposit) -
      expect (secondLaw weight nonnegative decision submission alternatives)
        (aliceUtility reward forfeit deposit) := by
  have lower := quiet_payoff_lower weight nonnegative positive decision players
    rewardNonnegative forfeitNonnegative deposit depositNonnegative
  have upper := extra_payoff_upper weight nonnegative decision submission alternatives
    rewardNonnegative forfeitNonnegative deposit depositNonnegative
  linarith

end Vegas.Examples.LateOpeningRuntimeAliceIncentive

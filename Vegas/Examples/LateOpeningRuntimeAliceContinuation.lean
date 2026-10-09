/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeRetryAudit
import Vegas.Examples.LateOpeningRuntimeLateHistories
import Vegas.Examples.LateOpeningRuntimeTerminalReceipt
import Interaction.ReactiveTrafficContinuation
import Interaction.ReactiveRawRoundTrace

/-! # Quiet continuation after a genuine first late opening

Alice's remaining policy is silence; Bob's policy is unrestricted. The
accepted branch preserves her initialized opening and has zero Alice audit
charge. The omitted branch still allows loss of both the source forfeit and
the audit deposit. The comparison uses their actual native continuation laws.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
open LateOpeningRuntimeLateHistories LateOpeningRuntimeReliability
open LateOpeningRuntimeUtility LateOpeningRuntimeRetryAudit

def quietAgainst (players : Player → app.Policy) : Player → app.Policy :=
  fun who => if who = alice then fun _ _ => PMF.pure ⟨none⟩ else players who

def aliceUtility (reward forfeit : ℝ) (deposit : Player → ℝ)
    (execution : app.Execution) : ℝ :=
  TerminalAudit.utility (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
      (fun actual => PMF.pure actual)) deposit (app.finished execution) alice

private def OnlyAlicePacket (bit : Bool) (execution : app.Execution) : Prop :=
  ∀ message ∈ execution.network.inputs, message.sender = alice → message = openingMessage bit

private theorem quiet_onlyAlicePacket (bit : Bool) (players : Player → app.Policy) :
    app.PolicyInvariant (quietAgainst players) (OnlyAlicePacket bit) where
  respond execution who action valid supported := by
    by_cases owner : who = alice
    · subst who
      simp only [quietAgainst, ↓reduceIte, PMF.mem_support_pure_iff] at supported
      subst action
      exact valid
    · rcases action with ⟨transmission⟩
      cases transmission with
      | none => exact valid
      | some submission =>
          intro message member authored
          change message ∈ execution.network.inputs ++ [_] at member
          rcases List.mem_append.mp member with old | fresh
          · exact valid message old authored
          · cases List.mem_singleton.mp fresh
            exact (owner authored).elim
  environment execution next command valid reached := by
    intro message member authored
    rw [app.environmentStep_inputs execution next command reached] at member
    exact valid message member authored

private theorem beforeLottery_inputs (bit : Bool) (label : Fin 3) (seen : Bool) :
    (beforeLottery bit label 0 seen).network.inputs = [openingMessage bit] := by
  change ((beforeBob bit label 0).network.learn bob
    (if seen then {(alice, 0)} else ∅)).inputs = _
  rw [beforeBob_first_network]
  rfl

private theorem acceptedLottery_onlyAlicePacket (bit : Bool) (label : Fin 3) (seen : Bool) :
    OnlyAlicePacket bit (acceptedLottery bit label 0 seen) := by
  intro message member _
  have inputs : (acceptedLottery bit label 0 seen).network.inputs =
      (beforeLottery bit label 0 seen).network.inputs := by
    change ((beforeLottery bit label 0 seen).includePending app (alice, 0)).network.inputs = _
    unfold ReactiveApplication.Execution.includePending
    rw [MessageNetwork.includePending, beforeLottery_lookup]
  rw [inputs, beforeLottery_inputs] at member
  exact List.mem_singleton.mp member

private theorem base_bounds {reward forfeit : ℝ} (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (state : app.ProtocolState) :
    -forfeit ≤ nativeBaseUtility reward forfeit state alice ∧
      nativeBaseUtility reward forfeit state alice ≤ reward := by
  change -forfeit ≤ (serviceSourceReadout setup .sequential
    LateOpeningRuntimeService.deadline leaks state).elim 0 (fun source =>
      sourceUtility reward forfeit source alice) ∧
    (serviceSourceReadout setup .sequential LateOpeningRuntimeService.deadline leaks state).elim 0
      (fun source => sourceUtility reward forfeit source alice) ≤ reward
  cases decoded : serviceSourceReadout setup .sequential
      LateOpeningRuntimeService.deadline leaks state with
  | none =>
      simpa only [Option.elim_none] using
        And.intro (neg_nonpos.mpr forfeitNonnegative) rewardNonnegative
  | some source => exact sourceUtility_alice_bounds rewardNonnegative forfeitNonnegative source

theorem aliceUtility_bounds {reward forfeit : ℝ} (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (deposit : Player → ℝ)
    (depositNonnegative : 0 ≤ deposit alice) (execution : app.Execution) :
    -forfeit - deposit alice ≤ aliceUtility reward forfeit deposit execution ∧
      aliceUtility reward forfeit deposit execution ≤ reward := by
  have base := base_bounds rewardNonnegative forfeitNonnegative (app.finished execution)
  have charged := TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
      (fun actual => PMF.pure actual)) (app.finished execution) alice
  have upperPenalty := mul_le_of_le_one_left depositNonnegative charged.2
  have lowerPenalty := mul_nonneg charged.1 depositNonnegative
  unfold aliceUtility TerminalAudit.utility
  constructor <;> linarith

private theorem aliceUtility_integrable {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) (law : PMF app.Execution) :
    PayoffIntegrable law (aliceUtility reward forfeit deposit) := by
  apply payoffIntegrable_of_bounded law _ (C := forfeit + deposit alice + reward)
  intro execution
  obtain ⟨lower, upper⟩ := aliceUtility_bounds rewardNonnegative forfeitNonnegative
    deposit depositNonnegative execution
  rw [abs_le]
  constructor <;> linarith

private theorem completed_opening_base_nonnegative {reward : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeit : ℝ) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (bit : Bool)
    (published : control.execution.application.config.store (.inr aliceEvent) =
      some (.success bit)) : 0 ≤ nativeBaseUtility reward forfeit (some control) alice := by
  have complete := LateOpeningRuntimeService.completes weight nonnegative control trace terminal
  obtain ⟨initialBit, label, aliceResult, binding, answer, decoded⟩ := nativeReadout_complete
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace complete
  have base := nativeBaseUtility_of_readout reward forfeit (some control) _ decoded alice
  have storeDecoded :
      decodeState? (terminalRefs setup.program) control.execution.application.config.store =
      some (terminalStateOf initialBit label aliceResult binding answer) := by
    unfold serviceSourceReadout at decoded
    simpa only [Option.bind_some, ite_eq_left complete] using decoded
  have agreed := decodeState?_agrees _ _ _ storeDecoded alicePublication
  change control.execution.application.config.store (.inr aliceEvent) = some aliceResult at agreed
  rw [published] at agreed
  cases Option.some.inj agreed
  rw [base, sourceUtility_alice]
  change 0 ≤ grossUtility reward _ alice - (if true then 0 else forfeit)
  simp only [ite_true, sub_zero]
  exact (alice_gross_bounds rewardNonnegative _).1

/-- After accepted late inclusion, remaining silence leaves Alice clean and
nonnegative even if Bob chooses arbitrary malformed or withholding responses. -/
theorem accepted_quiet_payoff_nonnegative {reward : ℝ} (rewardNonnegative : 0 ≤ reward)
    (forfeit : ℝ) (deposit : Player → ℝ) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (seen : Bool) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (quietAgainst players) 17 (acceptedLottery bit label 0 seen)).support) :
    0 ≤ aliceUtility reward forfeit deposit execution := by
  obtain ⟨priorHistory⟩ := acceptedLottery_trace weight nonnegative positive bit label 0 seen
    (Or.inl rfl)
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (quietAgainst players)
      0 17 (acceptedLottery bit label 0 seen) execution
        (rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) priorHistory) reached
  have terminal : app.terminal (app.finished execution) := ⟨rfl, rfl⟩
  have stored : (acceptedLottery bit label 0 seen).application.config.store (.inr aliceEvent) =
      some (.success bit) := by
    rw [acceptedLottery_physical]
    exact openedPhysical_bit bit label
  have published := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr aliceEvent)
      (.success bit)) (quietAgainst players)).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 17
          (acceptedLottery bit label 0 seen) execution stored reached
  have only := (quiet_onlyAlicePacket bit players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 17
      (acceptedLottery bit label 0 seen) execution
        (acceptedLottery_onlyAlicePacket bit label seen) reached
  have receipt := (app.receipt_policyInvariant (quietAgainst players) ((alice, 0), true)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 17
      (acceptedLottery bit label 0 seen) execution
        (acceptedLottery_receipt bit label 0 seen) reached
  have charged : TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
        (fun actual => PMF.pure actual)) (app.finished execution) alice = 0 := by
    apply alice_audit_charge_zero (fun actual => PMF.pure actual)
    · intro actual observed supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact List.Subset.refl _
    · intro traffic member owner
      have input : traffic.envelope ∈ execution.network.inputs := by
        have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) trace
        change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
          execution.network.inputs at inputs
        rw [← inputs]
        exact List.mem_map.mpr ⟨traffic, member, rfl⟩
      have same := only traffic.envelope input owner
      rw [same]
      exact accepted_alice_opening_permitted _ (alice, 0) bit (some ⟨aliceEvent⟩) receipt
  unfold aliceUtility TerminalAudit.utility
  rw [charged, zero_mul, sub_zero]
  exact completed_opening_base_nonnegative rewardNonnegative forfeit weight nonnegative
    ⟨0, none, execution⟩ trace terminal bit published

/-- The lottery is a passive scheduler command, so its inclusion law does not
depend on either player's continuation policy. -/
theorem lottery_round_any (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (slot : Fin 2) (seen : Bool) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (beforeLottery bit label slot seen) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (acceptedLottery bit label slot seen))
        (PMF.pure (omittedLottery bit label slot seen)) := by
  rw [ReactiveApplication.round]
  change (stageChoice weight nonnegative 8 _).bind _ = _
  rw [lottery_command_law, mix_bind, PMF.pure_bind, PMF.pure_bind]
  congr 1
  · simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  · simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    rw [recorded_wait, PMF.pure_bind]
    rfl

/-- A genuine first late opening followed by silence has a conservative
expected payoff bound. Omission can lose both forfeit and audit deposit;
acceptance leaves Alice clean regardless of Bob's future responses. -/
theorem quiet_expected_payoff_lower {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (players : Player → app.Policy) (bit : Bool) (label : Fin 3) (seen : Bool) :
    -(1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (quietAgainst players) 18 (beforeLottery bit label 0 seen))
          (aliceUtility reward forfeit deposit) := by
  let scheduler := LateOpeningRuntimeService.scheduler weight nonnegative
  let accepted := app.runRounds scheduler (quietAgainst players) 17
    (acceptedLottery bit label 0 seen)
  let omitted := app.runRounds scheduler (quietAgainst players) 17
    (omittedLottery bit label 0 seen)
  have acceptedBound : 0 ≤ expect accepted (aliceUtility reward forfeit deposit) := by
    apply expect_nonneg
    intro execution reached
    exact accepted_quiet_payoff_nonnegative rewardNonnegative forfeit deposit weight
      nonnegative positive players bit label seen execution reached
  have omittedBound : -forfeit - deposit alice ≤
      expect omitted (aliceUtility reward forfeit deposit) := by
    have comparison := expect_mono (μ := omitted) (f := fun _ => -forfeit - deposit alice)
      (g := aliceUtility reward forfeit deposit)
      (fun execution _ => (aliceUtility_bounds rewardNonnegative forfeitNonnegative
        deposit depositNonnegative execution).1)
      (payoffIntegrable_constant omitted (-forfeit - deposit alice))
      (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit
        depositNonnegative omitted)
    simpa only [expect_constant] using comparison
  have law : app.runRounds scheduler (quietAgainst players) 18
      (beforeLottery bit label 0 seen) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le accepted omitted := by
    rw [ReactiveApplication.runRounds, lottery_round_any, mix_bind,
      PMF.pure_bind, PMF.pure_bind]
  rw [law, expect_mix _ _ _ _ _ _
    (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit
      depositNonnegative accepted)
    (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit
      depositNonnegative omitted)]
  have first := mul_nonneg
    (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1) acceptedBound
  have second := mul_le_mul_of_nonneg_left omittedBound
    (sub_nonneg.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le)
  linarith

/-- For sufficiently reliable inclusion, silence after the first late opening
beats the upper bound for every continuation emitting two Alice envelopes. -/
theorem quiet_expected_payoff_above_extra_packet_bound {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (reliable : (1 - inclusionProbability weight) * (forfeit + deposit alice) <
      deposit alice - reward)
    (players : Player → app.Policy) (bit : Bool) (label : Fin 3) (seen : Bool) :
    reward - deposit alice <
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (quietAgainst players) 18 (beforeLottery bit label 0 seen))
          (aliceUtility reward forfeit deposit) := by
  have lower := quiet_expected_payoff_lower rewardNonnegative forfeitNonnegative
    deposit depositNonnegative weight nonnegative positive players bit label seen
  linarith

private theorem secondLateDecision_raw_trace (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (seen : Bool) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice, secondLateDecision bit label 0 seen⟩)) := by
  obtain ⟨observed⟩ := bobObserved_first_trace weight nonnegative bit label seen
  let e5 := bobObserved bit label 0 seen
  let e6 := recorded e5 .wait e5.application
  let e7 := recorded e6 (.application .advanceClock)
    { e6.application with clock := e6.application.clock + 1 }
  have noBob : latestAuthor bob (e5.observeEnvironment app) = .wait := by
    cases seen <;> rfl
  have noForeign : foreignPending alice e7.network.pending = ∅ := by
    cases seen <;> rfl
  obtain ⟨waited⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20 e5 e6 .wait
      (rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) observed)
      (by change .wait ∈ (PMF.pure (latestAuthor bob _)).support; rw [noBob]; simp)
      (by rw [recorded_wait]; apply (PMF.mem_support_pure_iff _ _).mpr; rfl)
  obtain ⟨ticked⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 19 e6 e7
      (.application .advanceClock) waited (by
        change (.application .advanceClock : app.Command) ∈ (stageChoice weight nonnegative
          e6.environmentRecall.length (e6.observeEnvironment app)).support
        have cursor : e6.environmentRecall.length = 6 := rfl
        rw [cursor]
        simp [stageChoice])
      (by rw [recorded_clock]; apply (PMF.mem_support_pure_iff _ _).mpr; rfl)
  apply app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 e7
      (secondLateDecision bit label 0 seen) (.activate alice) ticked
  · change (.activate alice : app.Command) ∈ (stageChoice weight nonnegative
      e7.environmentRecall.length (e7.observeEnvironment app)).support
    have cursor : e7.environmentRecall.length = 7 := rfl
    rw [cursor]
    simp [stageChoice]
  · rw [recorded_activation e7 alice noForeign]
    apply (PMF.mem_support_pure_iff _ _).mpr
    rfl

private theorem input_persists (players : Player → app.Policy)
    (message : Message Player app.Payload) :
    app.PolicyInvariant players (fun execution => message ∈ execution.network.inputs) where
  respond execution who action valid _ := by
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid
    | some submission => exact List.mem_append_left _ valid
  environment execution next command valid reached := by
    rw [app.environmentStep_inputs execution next command reached]
    exact valid

def secondPacket (bit : Bool) (label : Fin 3) (seen : Bool)
    (submission : app.Submission) : Message Player app.Payload :=
  let execution := secondLateDecision bit label 0 seen
  ⟨(alice, 1), app.packet (app.submit execution.application alice submission) alice
    (execution.network.known alice) submission⟩

private theorem secondPacket_inputs (bit : Bool) (label : Fin 3) (seen : Bool)
    (submission : app.Submission) :
    ((secondLateDecision bit label 0 seen).respond app alice ⟨some submission⟩).network.inputs =
      [openingMessage bit, secondPacket bit label seen submission] := by
  have inputs : (secondLateDecision bit label 0 seen).network.inputs =
      [openingMessage bit] := by
    change ((beforeBob bit label 0).network.learn bob
      (if seen then {(alice, 0)} else ∅)).inputs = _
    rw [beforeBob_first_network]
    rfl
  have serial : (secondLateDecision bit label 0 seen).network.nextSerial alice = 1 := by
    change ((beforeBob bit label 0).network.learn bob
      (if seen then {(alice, 0)} else ∅)).nextSerial alice = _
    rw [beforeBob_first_network]
    rfl
  change (secondLateDecision bit label 0 seen).network.inputs ++
    [⟨(alice, (secondLateDecision bit label 0 seen).network.nextSerial alice), _⟩] = _
  rw [inputs, serial]
  rfl

/-- Any second submission at the remaining Alice decision costs a full audit
deposit. This includes another canonical opening and every malformed packet;
both players' later policies remain arbitrary. -/
theorem second_packet_payoff_upper {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (seen : Bool) (submission : app.Submission)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 18 ((secondLateDecision bit label 0 seen).respond app alice
        ⟨some submission⟩)).support) :
    aliceUtility reward forfeit deposit execution ≤ reward - deposit alice := by
  obtain ⟨active⟩ := secondLateDecision_raw_trace weight nonnegative bit label seen
  obtain ⟨after⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18
      (secondLateDecision bit label 0 seen) alice ⟨some submission⟩ active
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 18
      ((secondLateDecision bit label 0 seen).respond app alice ⟨some submission⟩)
        execution after reached
  have firstPresent := (input_persists players (openingMessage bit)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18
      ((secondLateDecision bit label 0 seen).respond app alice ⟨some submission⟩)
        execution (by rw [secondPacket_inputs]; simp) reached
  have secondPresent := (input_persists players (secondPacket bit label seen submission)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18
      ((secondLateDecision bit label 0 seen).respond app alice ⟨some submission⟩)
        execution (by rw [secondPacket_inputs]; simp) reached
  have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
    execution.network.inputs at inputs
  rw [← inputs] at firstPresent secondPresent
  obtain ⟨first, firstMember, firstEnvelope⟩ := List.mem_map.mp firstPresent
  obtain ⟨second, secondMember, secondEnvelope⟩ := List.mem_map.mp secondPresent
  exact alice_two_envelopes_utility_bound rewardNonnegative forfeitNonnegative deposit
    depositNonnegative weight nonnegative ⟨0, none, execution⟩ trace ⟨rfl, rfl⟩
      first second firstMember secondMember
      (by rw [firstEnvelope]; rfl) (by rw [secondEnvelope]; rfl)
      (by rw [firstEnvelope, secondEnvelope]; change (alice, 0) ≠ (alice, 1); decide)

theorem second_packet_expected_payoff_upper {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (seen : Bool) (submission : app.Submission) :
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 18 ((secondLateDecision bit label 0 seen).respond app alice
        ⟨some submission⟩)) (aliceUtility reward forfeit deposit) ≤ reward - deposit alice := by
  apply expect_le_const _ _
    (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative _) _
  intro execution reached
  exact second_packet_payoff_upper rewardNonnegative forfeitNonnegative deposit
    depositNonnegative weight nonnegative players bit label seen submission execution reached

/-- When the omission loss is small enough, remaining silence strictly
dominates every second raw submission, even allowing an arbitrary future policy. -/
theorem quiet_strictly_beats_second_packet {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (reliable : (1 - inclusionProbability weight) * (forfeit + deposit alice) <
      deposit alice - reward)
    (players alternatives : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (seen : Bool) (submission : app.Submission) :
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      alternatives 18 ((secondLateDecision bit label 0 seen).respond app alice
        ⟨some submission⟩)) (aliceUtility reward forfeit deposit) <
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (quietAgainst players) 18 (beforeLottery bit label 0 seen))
          (aliceUtility reward forfeit deposit) :=
  lt_of_le_of_lt (second_packet_expected_payoff_upper rewardNonnegative forfeitNonnegative
    deposit depositNonnegative weight nonnegative alternatives bit label seen submission)
    (quiet_expected_payoff_above_extra_packet_bound rewardNonnegative forfeitNonnegative
      deposit depositNonnegative weight nonnegative positive reliable players bit label seen)

/-- The comparison has a uniform quantitative margin over every second
submission and every later pair of policies. -/
theorem quiet_second_packet_regret {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (players alternatives : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (seen : Bool) (submission : app.Submission) :
    deposit alice - reward - (1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (quietAgainst players) 18 (beforeLottery bit label 0 seen))
          (aliceUtility reward forfeit deposit) -
      expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        alternatives 18 ((secondLateDecision bit label 0 seen).respond app alice
          ⟨some submission⟩)) (aliceUtility reward forfeit deposit) := by
  have lower := quiet_expected_payoff_lower rewardNonnegative forfeitNonnegative
    deposit depositNonnegative weight nonnegative positive players bit label seen
  have upper := second_packet_expected_payoff_upper rewardNonnegative forfeitNonnegative
    deposit depositNonnegative weight nonnegative alternatives bit label seen submission
  linarith

/-- Fixed collateral above the gross reward range admits a finite public
lottery weight with positive comparison margin. The resulting scheduler also
satisfies the actual all-raw service contract and late-packet independence. -/
theorem exists_service_with_quiet_margin {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (largeDeposit : reward < deposit alice) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      (1 - inclusionProbability weight) * (forfeit + deposit alice) < deposit alice - reward := by
  have totalPositive : 0 < forfeit + deposit alice := by linarith
  have gapPositive : 0 < deposit alice - reward := sub_pos.mpr largeDeposit
  obtain ⟨weight, nonnegative, positive, contract, blind, receipts⟩ :=
    LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure
      ((deposit alice - reward) / (forfeit + deposit alice))
      (div_pos gapPositive totalPositive)
  obtain ⟨_, _, _, close⟩ := receipts false 0 0
  rw [LateOpeningRuntimeTerminalReceipt.terminal_receipt_probability] at close
  have scaled := mul_lt_mul_of_pos_right close totalPositive
  rw [div_mul_cancel₀ _ (ne_of_gt totalPositive)] at scaled
  exact ⟨weight, nonnegative, positive, contract, blind, scaled⟩

/-- After collateral is fixed, one finite public scheduler makes remaining
silence strictly beat every second raw packet at every initialized type and
possible first-sample branch. Its terminal omission probability remains
strictly positive and can be smaller than any requested positive bound. -/
theorem exists_service_with_quiet_normalization {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (largeDeposit : reward < deposit alice)
    (failureFloor : ℝ) (floorPositive : 0 < failureFloor) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      0 < 1 - inclusionProbability weight ∧ 1 - inclusionProbability weight < failureFloor ∧
      ∀ (players alternatives : Player → app.Policy) (bit : Bool) (label : Fin 3)
        (seen : Bool) (submission : app.Submission),
        expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          alternatives 18 ((secondLateDecision bit label 0 seen).respond app alice
            ⟨some submission⟩)) (aliceUtility reward forfeit deposit) <
          expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
            (quietAgainst players) 18 (beforeLottery bit label 0 seen))
              (aliceUtility reward forfeit deposit) := by
  have totalPositive : 0 < forfeit + deposit alice := by linarith
  have gapPositive : 0 < deposit alice - reward := sub_pos.mpr largeDeposit
  let floor := min failureFloor ((deposit alice - reward) / (forfeit + deposit alice))
  have positiveFloor : 0 < floor := lt_min floorPositive (div_pos gapPositive totalPositive)
  obtain ⟨weight, nonnegative, positive, contract, blind, receipts⟩ :=
    LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure floor positiveFloor
  obtain ⟨_, _, _, close⟩ := receipts false 0 0
  rw [LateOpeningRuntimeTerminalReceipt.terminal_receipt_probability] at close
  have reliable : (1 - inclusionProbability weight) * (forfeit + deposit alice) <
      deposit alice - reward := by
    have scaled := mul_lt_mul_of_pos_right
      (close.trans_le (min_le_right failureFloor _)) totalPositive
    rw [div_mul_cancel₀ _ (ne_of_gt totalPositive)] at scaled
    exact scaled
  refine ⟨weight, nonnegative, positive, contract, blind,
    sub_pos.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1),
    close.trans_le (min_le_left failureFloor _), ?_⟩
  intro players alternatives bit label seen submission
  exact quiet_strictly_beats_second_packet rewardNonnegative forfeitNonnegative
    deposit (by linarith) weight nonnegative positive reliable players alternatives bit label
      seen submission

end Vegas.Examples.LateOpeningRuntimeAliceContinuation

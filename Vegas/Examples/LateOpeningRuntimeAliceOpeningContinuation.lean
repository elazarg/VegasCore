/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision
import Vegas.Examples.LateOpeningRuntimeAliceIncentive

/-! # Sending a genuine opening at Alice's remaining opportunity

The actual raw submission may have arbitrary private syntax. Its emitted
public envelope identifies the fixed initialized opening. Earlier Bob traffic
is unrestricted; it has already left the pending pool. The real lottery
therefore accepts this sole opening with probability weight/(1+weight).
Success leaves Alice audit-clean with nonnegative payoff against any later
Bob policy. Failure may lose both the source forfeit and the audit deposit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceOpeningContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeUtility
  LateOpeningRuntimeAliceEmptyDecision

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def EmitsOpening (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) : Prop :=
  app.packet (app.submit decision.execution.application alice submission) alice
    (decision.execution.network.known alice) submission = (openingMessage decision.bit).payload

theorem opening_submission_unchanged (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    app.submit decision.execution.application alice submission =
      decision.execution.application := by
  have call := congrArg WitnessedPacket.call genuine
  change submission.call.packet = .opening aliceEvent aliceCandidate ⟨.bool, decision.bit⟩ at call
  rcases submission with ⟨⟨packet, material⟩, evidence⟩
  dsimp only at call
  subst packet
  cases material <;> rfl

theorem canonical_emits_opening (decision : DecisionHistory weight nonnegative) :
    EmitsOpening weight nonnegative decision
      (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, decision.bit⟩)) := by
  unfold EmitsOpening
  change app.packet decision.execution.application alice (decision.execution.network.known alice)
    (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, decision.bit⟩)) = _
  rw [LateOpeningRuntimeService.runtime.windowOpening_packet leaks alice aliceEvent aliceCandidate
    ⟨.bool, decision.bit⟩ _ _ rfl decision.fixed,
    decision.execution.application.publicView_tokenFor_of_ready _ aliceEvent rfl decision.ready]
  rfl

def submitted (decision : DecisionHistory weight nonnegative) (submission : app.Submission) :=
  decision.execution.respond app alice ⟨some submission⟩

def accepted (decision : DecisionHistory weight nonnegative) (submission : app.Submission) :
    app.Execution :=
  let execution := submitted weight nonnegative decision submission
  { execution.includePending app (alice, 0) with environmentRecall :=
    execution.environmentRecall ++ [⟨execution.observeEnvironment app, .include (alice, 0)⟩] }

def omitted (decision : DecisionHistory weight nonnegative) (submission : app.Submission) :=
  recorded (submitted weight nonnegative decision submission) .wait
    (submitted weight nonnegative decision submission).application

def openingLaw (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (players : Player → app.Policy) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (quietAgainst players) 18 (submitted weight nonnegative decision submission)

theorem submitted_pending (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    (submitted weight nonnegative decision submission).network.pending =
      [openingMessage decision.bit] := by
  change decision.execution.network.pending ++ [⟨(alice,
    decision.execution.network.nextSerial alice), _⟩] = _
  rw [decision.pending, decision_serial weight nonnegative decision, genuine]
  rfl

theorem submitted_onlyAlicePacket (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    OnlyAlicePacket decision.bit (submitted weight nonnegative decision submission) := by
  intro message member owner
  change message ∈ decision.execution.network.inputs ++ [⟨(alice,
    decision.execution.network.nextSerial alice), _⟩] at member
  rw [decision_serial weight nonnegative decision, genuine] at member
  rcases List.mem_append.mp member with old | fresh
  · exact (no_alice_inputs weight nonnegative ⟨18, some alice, decision.execution⟩
      decision.trace decision.quiet message old owner).elim
  · exact List.mem_singleton.mp fresh

private theorem lookup_submitted (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    (submitted weight nonnegative decision submission).network.lookup (alice, 0) =
      some (openingMessage decision.bit) := by
  rw [MessageNetwork.lookup, submitted_pending weight nonnegative decision submission genuine]
  rfl

private theorem handle_submitted (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    app.handle (submitted weight nonnegative decision submission).application
      (openingMessage decision.bit) =
        some (decision.execution.application.complete aliceEvent decision.ready true
          (.success decision.bit)) := by
  change app.handle (app.submit decision.execution.application alice submission) _ = _
  rw [opening_submission_unchanged weight nonnegative decision submission genuine,
    LateOpeningRuntimeService.runtime.reactiveApplication_handle_of_tokenValid leaks
      _ _ (by rfl)]
  exact handle_opening_eq LateOpeningRuntimeService.runtime decision.execution.application
    (alice, 0) aliceEvent aliceCandidate alice .bool aliceBinding [] rfl rfl rfl
      decision.ready decision.timely rfl rfl decision.associated decision.bit decision.fixed
        decision.bound (.success decision.bit)
          (by rw [EventCode.resolveOutput?, decision.bound]; rfl)

private theorem accepted_physical (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    (accepted weight nonnegative decision submission).application =
      decision.execution.application.complete aliceEvent decision.ready true
        (.success decision.bit) := by
  change ((submitted weight nonnegative decision submission).includePending app
    (alice, 0)).application = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending,
    lookup_submitted weight nonnegative decision submission genuine]
  change (app.handle _ (openingMessage decision.bit)).getD _ = _
  rw [handle_submitted weight nonnegative decision submission genuine]
  rfl

private theorem accepted_receipt (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    ((alice, 0), true) ∈ (accepted weight nonnegative decision submission).receipts := by
  change ((alice, 0), true) ∈
    ((submitted weight nonnegative decision submission).includePending app (alice, 0)).receipts
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending,
    lookup_submitted weight nonnegative decision submission genuine]
  change ((alice, 0), true) ∈ (submitted weight nonnegative decision submission).receipts ++
    [((alice, 0), (app.handle _ (openingMessage decision.bit)).isSome)]
  rw [handle_submitted weight nonnegative decision submission genuine]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem lottery_round (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission)
    (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (submitted weight nonnegative decision submission) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (accepted weight nonnegative decision submission))
        (PMF.pure (omitted weight nonnegative decision submission)) := by
  have cursor : (submitted weight nonnegative decision submission).environmentRecall.length = 8 :=
    decision_cursor weight nonnegative decision
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative
      (submitted weight nonnegative decision submission).environmentRecall
      ((submitted weight nonnegative decision submission).observeEnvironment app) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (.include (alice, 0))) (PMF.pure .wait) := by
    rw [LateOpeningRuntimeService.scheduler, cursor]
    change (MessageNetwork.chooseWithOutside weight nonnegative (MessageNetwork.pendingIds
      (submitted weight nonnegative decision submission).network.pending)).map _ = _
    rw [submitted_pending weight nonnegative decision submission genuine]
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
    (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (genuine : EmitsOpening weight nonnegative decision submission)
    (players : Player → app.Policy) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨17, none, accepted weight nonnegative decision submission⟩)) := by
  obtain ⟨after⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
      ⟨some submission⟩ decision.trace
  apply app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 17
      (submitted weight nonnegative decision submission) _ after
  rw [lottery_round weight nonnegative decision submission genuine]
  exact mem_support_mix_left (inclusionProbability weight)
    (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
    (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
    (by unfold inclusionProbability MessageNetwork.inclusionMass; positivity) (by simp)

theorem accepted_opening_nonnegative (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (genuine : EmitsOpening weight nonnegative decision submission) (players : Player → app.Policy)
    {reward : ℝ} (rewardNonnegative : 0 ≤ reward) (forfeit : ℝ) (deposit : Player → ℝ)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (quietAgainst players) 17 (accepted weight nonnegative decision submission)).support) :
    0 ≤ aliceUtility reward forfeit deposit execution := by
  obtain ⟨prior⟩ := accepted_trace weight nonnegative positive decision submission genuine
    (quietAgainst players)
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (quietAgainst players) 0 17
      (accepted weight nonnegative decision submission) execution prior reached
  have published : (accepted weight nonnegative decision submission).application.config.store
      (.inr aliceEvent) = some (.success decision.bit) := by
    rw [accepted_physical weight nonnegative decision submission genuine]
    change (decision.execution.application.complete aliceEvent decision.ready true
      (.success decision.bit)).config.outputs aliceEvent = _
    simp [EventGraphRuntime.State.complete, Config.complete]
  have retained := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr aliceEvent)
      (.success decision.bit)) (quietAgainst players)).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 17 _ execution published reached
  have only : OnlyAlicePacket decision.bit (accepted weight nonnegative decision submission) := by
    intro message member owner
    have unchanged : (accepted weight nonnegative decision submission).network.inputs =
        (submitted weight nonnegative decision submission).network.inputs := by
      change ((submitted weight nonnegative decision submission).includePending app
        (alice, 0)).network.inputs = _
      unfold ReactiveApplication.Execution.includePending
      rw [MessageNetwork.includePending,
        lookup_submitted weight nonnegative decision submission genuine]
    rw [unchanged] at member
    exact submitted_onlyAlicePacket weight nonnegative decision submission genuine message
      member owner
  have after := (quiet_onlyAlicePacket decision.bit players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 17 _ execution only reached
  have receipt := (app.receipt_policyInvariant (quietAgainst players) ((alice, 0), true)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 17 _ execution
      (accepted_receipt weight nonnegative decision submission genuine) reached
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
      have present : traffic.envelope ∈ execution.network.inputs := by
        rw [← inputs]
        exact List.mem_map.mpr ⟨traffic, member, rfl⟩
      rw [after traffic.envelope present owner]
      exact accepted_alice_opening_permitted _ (alice, 0) decision.bit (some ⟨aliceEvent⟩) receipt
  unfold aliceUtility TerminalAudit.utility
  rw [charged, zero_mul, sub_zero]
  exact completed_opening_base_nonnegative rewardNonnegative forfeit weight nonnegative
    ⟨0, none, execution⟩ trace ⟨rfl, rfl⟩ decision.bit retained

theorem opening_payoff_lower (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (genuine : EmitsOpening weight nonnegative decision submission) (players : Player → app.Policy)
    {reward forfeit : ℝ} (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) :
    -(1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      expect (openingLaw weight nonnegative decision submission players)
        (aliceUtility reward forfeit deposit) := by
  let scheduler := LateOpeningRuntimeService.scheduler weight nonnegative
  let yes := app.runRounds scheduler (quietAgainst players) 17
    (accepted weight nonnegative decision submission)
  let no := app.runRounds scheduler (quietAgainst players) 17
    (omitted weight nonnegative decision submission)
  have acceptedBound : 0 ≤ expect yes (aliceUtility reward forfeit deposit) := by
    apply expect_nonneg
    intro execution reached
    exact accepted_opening_nonnegative weight nonnegative positive decision submission genuine
      players rewardNonnegative forfeit deposit execution reached
  have omittedBound : -forfeit - deposit alice ≤
      expect no (aliceUtility reward forfeit deposit) := by
    have comparison := expect_mono (μ := no) (f := fun _ => -forfeit - deposit alice)
      (g := aliceUtility reward forfeit deposit)
      (fun execution _ => (aliceUtility_bounds rewardNonnegative forfeitNonnegative
        deposit depositNonnegative execution).1)
      (payoffIntegrable_constant no (-forfeit - deposit alice))
      (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative no)
    simpa only [expect_constant] using comparison
  unfold openingLaw
  rw [ReactiveApplication.runRounds, lottery_round weight nonnegative decision submission genuine,
    mix_bind, PMF.pure_bind, PMF.pure_bind,
    expect_mix _ _ _ _ _ _
      (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative yes)
      (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative no)]
  have first := mul_nonneg
    (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1) acceptedBound
  have second := mul_le_mul_of_nonneg_left omittedBound
    (sub_nonneg.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le)
  linarith

end Vegas.Examples.LateOpeningRuntimeAliceOpeningContinuation

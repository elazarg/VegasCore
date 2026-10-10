/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeGame
import Vegas.Examples.LateOpeningRuntimeBobDirtyDisclosurePublication
import Vegas.Examples.LateOpeningRuntimeAliceOpeningContinuation

/-! # Protected Alice publication against rational future Bob play

A genuine opening at an actual clean Alice decision starts Bob binding on time,
including histories with earlier Bob traffic. For labels below two, rational
future Bob play gives the actual accepted continuation its half-reward floor.
The lottery bound includes omitted service and the exact Alice audit charge.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAliceProtectedPublication
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeUtility
  LateOpeningRuntimeAliceEmptyDecision LateOpeningRuntimeAliceOpeningContinuation
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
theorem binding_ready_after_alice (physical : app.State)
    (ready : physical.config.cut.Ready aliceEvent) :
    (physical.config.cut.complete aliceEvent ready).Ready bobBindEvent := by
  have before : bobBindEvent ∉ physical.config.cut.completed := by
    intro completed
    exact ready.1 (physical.config.cut.predecessor_closed completed
      (by decide : aliceEvent ∈ nativeGraph.order.predecessors bobBindEvent))
  refine ⟨?_, ?_⟩
  · change bobBindEvent ∉ insert aliceEvent physical.config.cut.completed
    simpa only [Finset.mem_insert, show bobBindEvent ≠ aliceEvent by decide, false_or]
      using before
  · intro predecessor earlier
    change predecessor ∈ insert aliceEvent physical.config.cut.completed
    have eq : predecessor = aliceEvent := by
      change Fin 3 at predecessor
      fin_cases predecessor
      · rfl
      · have smaller := nativeGraph.order.predecessor_lt earlier
        change (1 : Nat) < 1 at smaller
        omega
      · have smaller := nativeGraph.order.predecessor_lt earlier
        change (2 : Nat) < 1 at smaller
        omega
    rw [eq]
    exact Finset.mem_insert_self _ _

theorem accepted_binding_ready_timer (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission)
    (genuine : EmitsOpening weight nonnegative decision submission) :
    (accepted weight nonnegative decision submission).application.config.cut.Ready bobBindEvent ∧
      (accepted weight nonnegative decision submission).application.activatedAt bobBindEvent =
        some 2 ∧
      (accepted weight nonnegative decision submission).application.clock = 2 := by
  have ready := binding_ready_after_alice decision.execution.application decision.ready
  have clock := decision_clock weight nonnegative decision
  obtain ⟨bit, label, invariant⟩ := history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
        ⟨18, some alice, decision.execution⟩ decision.trace
  have unactivated : decision.execution.application.activatedAt bobBindEvent = none := by
    cases timer : decision.execution.application.activatedAt bobBindEvent with
    | none => rfl
    | some entered =>
        have beforeReady := ((invariant.activated_iff bobBindEvent).mp (by rw [timer]; rfl)).1
        exact (decision.ready.1 (beforeReady.2
          (by decide : aliceEvent ∈ nativeGraph.order.predecessors bobBindEvent))).elim
  rw [accepted_physical weight nonnegative decision submission genuine]
  refine ⟨ready, ?_, clock⟩
  change State.refreshActivated _ decision.execution.application.clock
    decision.execution.application.activatedAt bobBindEvent = some 2
  unfold State.refreshActivated
  have completedReady : (decision.execution.application.config.complete aliceEvent decision.ready
      true (.success decision.bit)).cut.Ready bobBindEvent := ready
  rw [dite_eq_left completedReady]
  change (decision.execution.application.activatedAt bobBindEvent).orElse
    (fun _ => some decision.execution.application.clock) = some 2
  rw [unactivated, clock]
  rfl

def beforeBinding (execution : app.Execution) : app.Execution :=
  let ticked := LateOpeningRuntimeBobSuffix.ticked execution
  recorded ticked (.application (.expire aliceEvent)) ticked.application

private theorem completed_alice_expiry (execution : app.Execution)
    (completed : aliceEvent ∈ execution.application.config.cut.completed) :
    execution.environmentStep app (.application (.expire aliceEvent)) =
      PMF.pure (recorded execution (.application (.expire aliceEvent)) execution.application) := by
  rw [ReactiveApplication.Execution.environmentStep]
  change ((environmentStep LateOpeningRuntimeService.runtime execution.application
    (.expire aliceEvent)).map _).map _ = _
  rw [environmentStep_expire_of_not_ready LateOpeningRuntimeService.runtime _ aliceEvent
    (fun ready => ready.1 completed), PMF.pure_map, PMF.pure_map]
  rfl

theorem beforeBinding_run (execution : app.Execution) (players : Player → app.Policy)
    (position : execution.environmentRecall.length = 9)
    (completed : aliceEvent ∈ execution.application.config.cut.completed) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 2 execution =
      PMF.pure (beforeBinding execution) := by
  let ticked := LateOpeningRuntimeBobSuffix.ticked execution
  have s9 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players execution =
      PMF.pure ticked :=
    fixed_round weight nonnegative players execution ticked 9 (.application .advanceClock)
      position rfl (recorded_clock execution)
  have tickedPosition : ticked.environmentRecall.length = 10 := by
    simp only [ticked, LateOpeningRuntimeBobSuffix.ticked, recorded,
      List.length_append, List.length_singleton]
    omega
  have s10 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players ticked =
      PMF.pure (beforeBinding execution) :=
    fixed_round weight nonnegative players ticked (beforeBinding execution) 10
      (.application (.expire aliceEvent)) tickedPosition rfl
      (completed_alice_expiry ticked completed)
  rw [ReactiveApplication.runRounds, s9, PMF.pure_bind,
    ReactiveApplication.runRounds, s10, PMF.pure_bind, ReactiveApplication.runRounds]

theorem beforeBinding_physical (execution : app.Execution) :
    (beforeBinding execution).application = { execution.application with
      clock := execution.application.clock + 1 } := by
  simp only [beforeBinding, LateOpeningRuntimeBobSuffix.ticked, recorded]

theorem protected_publication_floor (execution : app.Execution)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨17, none, execution⟩))
    (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timer : execution.application.activatedAt bobBindEvent = some 2)
    (clock : execution.application.clock = 2)
    (labelLow : (LateOpeningRuntimeBobSuccessPayoff.originalLabel execution).val < 2)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (bobDepositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 17 execution).support) :
    reward / 2 - TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) alice * deposit alice ≤
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice := by
  have rawTrace := rawMenu.toRawTrace _ _ _ boundedTrace
  have position : execution.environmentRecall.length = 9 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) rawTrace
    change execution.environmentRecall.length + 17 = 26 at counted
    omega
  have completed : aliceEvent ∈ execution.application.config.cut.completed := by
    apply (execution.application.config.output_available aliceEvent).mp
    change (execution.application.config.store (.inr aliceEvent)).isSome = true
    rw [published]
    rfl
  let decoded := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  let before := beforeBinding execution
  obtain ⟨beforeTrace⟩ := rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decoded
      (fun who => rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who))
      15 2 execution before boundedTrace (by
        rw [beforeBinding_run weight nonnegative execution decoded position completed]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative) players 2 15,
    beforeBinding_run weight nonnegative execution players position completed, PMF.pure_bind]
      at reached
  obtain ⟨next, activated, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have beforePosition : before.environmentRecall.length = 11 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawTrace _ _ _ beforeTrace)
    change before.environmentRecall.length + 15 = 26 at counted
    omega
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative before.environmentRecall
      (before.observeEnvironment app) = PMF.pure (.activate bob) := by
    change stageChoice weight nonnegative _ _ = _
    rw [beforePosition]
    rfl
  rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch] at activated
  obtain ⟨observed, sampled, responded⟩ := (PMF.mem_support_bind_iff _ _ _).mp activated
  obtain ⟨response, supported, rfl⟩ := PMF.support_map .. ▸ responded
  obtain ⟨observedTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 before observed (.activate bob)
      beforeTrace (by rw [chosen]; exact (PMF.mem_support_pure_iff _ _).mpr rfl) sampled
  have physical : observed.application = before.application := by
    obtain ⟨updated, supportedSample, rfl⟩ := PMF.support_map .. ▸ sampled
    obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supportedSample
    rfl
  have finalPhysical := physical.trans (beforeBinding_physical execution)
  have observedPublished : observed.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool) := by rw [finalPhysical]; exact published
  have observedReady : observed.application.config.cut.Ready bobBindEvent := by
    rw [finalPhysical]; exact ready
  have observedTimely : observed.application.WithinDeadline LateOpeningRuntimeService.runtime
      bobBindEvent := by
    unfold State.WithinDeadline
    rw [finalPhysical]
    change (match execution.application.activatedAt bobBindEvent with
      | none => False
      | some entered => execution.application.clock + 1 - entered <
          LateOpeningRuntimeService.runtime.deadline bobBindEvent)
    rw [timer, clock]
    decide
  have observedLow : (LateOpeningRuntimeBobSuccessPayoff.originalLabel observed).val < 2 := by
    change (observed.application.config.inputs labelInput).val.toNat < 2
    rw [finalPhysical]
    exact labelLow
  have responseSupported : response ∈ (decoded bob (observed.recall bob)
      (observed.observe app bob)).support := by
    change response ∈ (players bob _ _).support at supported
    rwa [bobPolicy] at supported
  exact LateOpeningRuntimeBobDirtyDisclosurePublication.binding_payoff_floor weight nonnegative
    reward
    forfeit deposit assessment observed observedTrace observedReady observedTimely bit
    observedPublished observedLow rewardNonnegative forfeitPositive bobDepositPositive rational
    response responseSupported players bobPolicy final suffix

theorem accepted_genuine_floor (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice, decision.execution⟩))
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission)
    (available : (⟨some submission⟩ : app.Action) ∈ rawMenu.actions alice
      (decision.execution.recall alice) (decision.execution.observe app alice))
    (labelLow : (LateOpeningRuntimeBobSuccessPayoff.originalLabel decision.execution).val < 2)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (bobDepositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (quietAgainst players) 17 (accepted weight nonnegative decision submission)).support) :
    reward / 2 ≤ aliceUtility reward forfeit deposit final := by
  let decoded := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
      ⟨some submission⟩ boundedTrace available
  obtain ⟨acceptedTrace⟩ := rawMenu.trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decoded
      (fun who => rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who))
      17 (submitted weight nonnegative decision submission)
      (accepted weight nonnegative decision submission) respondedTrace (by
        rw [lottery_round weight nonnegative decision submission genuine]
        exact mem_support_mix_left (inclusionProbability weight)
          (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
          (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
          (by unfold inclusionProbability MessageNetwork.inclusionMass; positivity) (by simp))
  have published : (accepted weight nonnegative decision submission).application.config.store
      (.inr aliceEvent) = some (.success decision.bit) := by
    rw [accepted_physical weight nonnegative decision submission genuine]
    change (decision.execution.application.complete aliceEvent decision.ready true
      (.success decision.bit)).config.outputs aliceEvent = _
    simp [EventGraphRuntime.State.complete, Config.complete]
  obtain ⟨ready, timer, clock⟩ := accepted_binding_ready_timer weight nonnegative decision
    submission
    genuine
  have low : (LateOpeningRuntimeBobSuccessPayoff.originalLabel
      (accepted weight nonnegative decision submission)).val < 2 := by
    change ((accepted weight nonnegative decision submission).application.config.inputs
      labelInput).val.toNat < 2
    rw [accepted_physical weight nonnegative decision submission genuine]
    exact labelLow
  have owner : (quietAgainst players) bob = decoded bob := by
    simp only [quietAgainst, show bob ≠ alice by decide, ite_false]
    exact bobPolicy
  have floorBound := protected_publication_floor weight nonnegative
    (accepted weight nonnegative decision submission) acceptedTrace decision.bit published ready
    timer clock low reward forfeit deposit rewardNonnegative forfeitPositive bobDepositPositive
    assessment rational (quietAgainst players) owner final reached
  have charge := accepted_charge_zero weight nonnegative decision submission genuine
    (rawMenu.toRawTrace _ _ _ acceptedTrace) players final reached
  rw [charge, zero_mul, sub_zero] at floorBound
  exact floorBound

theorem opening_payoff_floor (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice, decision.execution⟩))
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission)
    (available : (⟨some submission⟩ : app.Action) ∈ rawMenu.actions alice
      (decision.execution.recall alice) (decision.execution.observe app alice))
    (labelLow : (LateOpeningRuntimeBobSuccessPayoff.originalLabel decision.execution).val < 2)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (bobDepositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (aliceDepositNonnegative : 0 ≤ deposit alice) :
    inclusionProbability weight * reward / 2 -
        (1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      expect (openingLaw weight nonnegative decision submission players)
        (aliceUtility reward forfeit deposit) := by
  let scheduler := LateOpeningRuntimeService.scheduler weight nonnegative
  let yes := app.runRounds scheduler (quietAgainst players) 17
    (accepted weight nonnegative decision submission)
  let no := app.runRounds scheduler (quietAgainst players) 17
    (omitted weight nonnegative decision submission)
  have acceptedBound : reward / 2 ≤ expect yes (aliceUtility reward forfeit deposit) := by
    have comparison := expect_mono (μ := yes) (f := fun _ => reward / 2)
      (g := aliceUtility reward forfeit deposit)
      (fun execution reached => accepted_genuine_floor weight nonnegative positive decision
        boundedTrace submission genuine available labelLow reward forfeit deposit rewardNonnegative
        forfeitPositive bobDepositPositive assessment rational players bobPolicy execution reached)
      (payoffIntegrable_constant yes (reward / 2))
      (aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit
        aliceDepositNonnegative yes)
    simpa only [expect_constant] using comparison
  have omittedBound : -forfeit - deposit alice ≤
      expect no (aliceUtility reward forfeit deposit) := by
    have comparison := expect_mono (μ := no) (f := fun _ => -forfeit - deposit alice)
      (g := aliceUtility reward forfeit deposit)
      (fun execution _ => (aliceUtility_bounds rewardNonnegative forfeitPositive.le
        deposit aliceDepositNonnegative execution).1)
      (payoffIntegrable_constant no (-forfeit - deposit alice))
      (aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit
        aliceDepositNonnegative no)
    simpa only [expect_constant] using comparison
  unfold openingLaw
  rw [ReactiveApplication.runRounds, lottery_round weight nonnegative decision submission genuine,
    mix_bind, PMF.pure_bind, PMF.pure_bind,
    expect_mix _ _ _ _ _ _
      (aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit
        aliceDepositNonnegative yes)
      (aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit
        aliceDepositNonnegative no)]
  have first := mul_le_mul_of_nonneg_left acceptedBound
    (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
  have second := mul_le_mul_of_nonneg_left omittedBound
    (sub_nonneg.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le)
  linarith

end Vegas.Examples.LateOpeningRuntimeAliceProtectedPublication

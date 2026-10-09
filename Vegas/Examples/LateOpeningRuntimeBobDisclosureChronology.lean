/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingChronology
import Vegas.Examples.LateOpeningRuntimeBobFinalAuditRationality
import Vegas.Examples.LateOpeningRuntimeOptionalPacket

/-! # Actual receiver disclosure callbacks after first binding

Acceptance of the first clock-three binding starts its disclosure clock.
The following observation is an actual ready timely optional callback.
If the receiver stays silent there, author service waits, three ticks pass,
the completed binding ignores expiry, and the final observation occurs at
clock six with the same clean openable answer. Pending foreign traffic and
future foreign policies are unrestricted.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDisclosureChronology

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobService
  LateOpeningRuntimeBobAudit LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobBindingPacket LateOpeningRuntimeBobBindingChronology
open LateOpeningRuntimeBobRawBinding (serviced serviced_trace)
open LateOpeningRuntimeBobSafeContinuation (optional_activation)
open LateOpeningRuntimeLatePrefix (recorded recorded_clock fixed_round)
open LateOpeningRuntimeBobSuffix (ticked)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem activation_receipts (execution observed : app.Execution) (who : Player)
    (sampled : observed ∈ (execution.environmentStep app (.activate who)).support) :
    observed.receipts = execution.receipts := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ sampled
  obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

/-- The readiness timestamp is derived from this actual accepted first
binding; earlier accepted bindings at clock one are not covered. -/
theorem optional_of_binding (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (material : app.Submission) (answer : Answer)
    (selected : (serviced execution ⟨some material⟩).application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (packet : responseMessage execution material = LateOpeningRuntimeBobSuffix.bindingMessage)
    (observed : app.Execution)
    (sampled : observed ∈ ((serviced execution ⟨some material⟩).environmentStep app
      (.activate bob)).support) :
    ∃ decision : LateOpeningRuntimeOptionalOpening.DecisionHistory weight nonnegative,
      decision.execution = observed ∧ decision.answer = answer ∧
        observed.application.activatedAt bobRevealEvent = some 3 ∧
        observed.application.clock = 3 := by
  obtain ⟨servedTrace⟩ := serviced_trace weight nonnegative execution trace quiet ⟨some material⟩
  obtain ⟨revealReady, timer, clock⟩ := accepted_chronology weight nonnegative execution trace quiet
    ready ⟨some material⟩ answer selected
  have clean := canonical_packet_clean weight nonnegative execution trace quiet ready material
    answer selected packet
  obtain ⟨⟨observedTrace⟩, physical, inputs, observedReady, timely, observedClock⟩ :=
    optional_activation weight nonnegative _ observed servedTrace revealReady clock timer sampled
  have receipts := activation_receipts _ observed bob sampled
  have observedClean : CleanBindings observed := by
    intro message present owner
    rw [inputs] at present
    obtain ⟨token, content, receipt⟩ := clean message present owner
    exact ⟨token, content, receipts ▸ receipt⟩
  exact ⟨⟨observed, observedTrace, answer, physical ▸ selected, observedReady, timely,
    observedClean⟩, rfl, rfl, physical ▸ timer, observedClock⟩

def afterSilence (execution : app.Execution) : app.Execution :=
  let responded := execution.respond app bob ⟨none⟩
  recorded responded .wait responded.application

def beforeFinal (execution : app.Execution) : app.Execution :=
  let advanced := ticked (ticked (ticked (afterSilence execution)))
  recorded advanced (.application (.expire bobBindEvent)) advanced.application

theorem silence_round (decision : LateOpeningRuntimeOptionalOpening.DecisionHistory
    weight nonnegative) (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (decision.execution.respond app bob ⟨none⟩) = PMF.pure (afterSilence decision.execution) := by
  have chosen := protected_response_scheduler weight nonnegative
    ⟨12, some bob, decision.execution⟩ decision.trace bob rfl ⟨none⟩ (Or.inl rfl)
  have selected : latestAuthor bob
      ((decision.execution.respond app bob ⟨none⟩).observeEnvironment app) = .wait :=
    LateOpeningRuntimeOptionalPacket.latestAuthor_clean weight nonnegative
      ⟨12, some bob, decision.execution⟩ decision.trace decision.clean
  rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind, ReactiveApplication.dispatch]
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

private theorem cursor (decision : LateOpeningRuntimeOptionalOpening.DecisionHistory
    weight nonnegative) : decision.execution.environmentRecall.length = 14 := by
  have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  change decision.execution.environmentRecall.length + 12 = 26 at counted
  omega

private theorem recorded_cursor (execution : app.Execution) (command : app.Command)
    (physical : app.State) :
    (recorded execution command physical).environmentRecall.length =
      execution.environmentRecall.length + 1 := by
  simp only [recorded, List.length_append, List.length_singleton]

private theorem ticked_cursor (execution : app.Execution) :
    (ticked execution).environmentRecall.length = execution.environmentRecall.length + 1 :=
  recorded_cursor execution _ _

private theorem silence_cursor (decision : LateOpeningRuntimeOptionalOpening.DecisionHistory
    weight nonnegative) : (afterSilence decision.execution).environmentRecall.length = 15 := by
  rw [afterSilence, recorded_cursor, app.respond_environmentRecall, cursor weight nonnegative]

private theorem clock_round (players : Player → app.Policy) (execution : app.Execution)
    (position : Fin 3) (atClock : execution.environmentRecall.length = 15 + position.val) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players execution =
      PMF.pure (ticked execution) := by
  have selected : stageChoice weight nonnegative (15 + position.val)
      (execution.observeEnvironment app) = PMF.pure (.application .advanceClock) := by
    fin_cases position <;> rfl
  exact fixed_round weight nonnegative players execution (ticked execution) (15 + position.val)
    (.application .advanceClock) atClock selected (recorded_clock execution)

private theorem binding_expiry (execution : app.Execution)
    (completed : bobBindEvent ∈ execution.application.config.cut.completed) :
    execution.environmentStep app (.application (.expire bobBindEvent)) =
      PMF.pure (recorded execution (.application (.expire bobBindEvent))
        execution.application) := by
  have absent : ¬ execution.application.config.cut.Ready bobBindEvent := fun ready =>
    ready.1 completed
  have law := environmentStep_expire_of_not_ready LateOpeningRuntimeService.runtime
    execution.application bobBindEvent absent
  change app.environment execution.application (.expire bobBindEvent) =
    PMF.pure execution.application at law
  simp only [ReactiveApplication.Execution.environmentStep, law, PMF.pure_map]
  rfl

/-- Five actual commands after optional silence have a fixed result and do
not invoke either player's future policy. No pending-pool restriction is used. -/
theorem silence_prefix_law (decision : LateOpeningRuntimeOptionalOpening.DecisionHistory
    weight nonnegative) (players : Player → app.Policy) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 5
      (decision.execution.respond app bob ⟨none⟩) = PMF.pure (beforeFinal decision.execution) := by
  let first := afterSilence decision.execution
  have firstCursor : first.environmentRecall.length = 15 := silence_cursor weight nonnegative
    decision
  have secondCursor : (ticked first).environmentRecall.length = 16 := by
    rw [ticked_cursor, firstCursor]
  have thirdCursor : (ticked (ticked first)).environmentRecall.length = 17 := by
    rw [ticked_cursor, secondCursor]
  have fourthCursor : (ticked (ticked (ticked first))).environmentRecall.length = 18 := by
    rw [ticked_cursor, thirdCursor]
  have completed : bobBindEvent ∈
      (ticked (ticked (ticked first))).application.config.cut.completed :=
    decision.ready.2 (by decide)
  have expiry := fixed_round weight nonnegative players (ticked (ticked (ticked first)))
    (beforeFinal decision.execution) 18 (.application (.expire bobBindEvent)) fourthCursor rfl
      (binding_expiry (ticked (ticked (ticked first))) completed)
  change (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (decision.execution.respond app bob ⟨none⟩)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 4) = _
  rw [silence_round weight nonnegative decision players, PMF.pure_bind]
  change (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players first).bind
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 3) = _
  rw [clock_round weight nonnegative players first 0 firstCursor, PMF.pure_bind]
  change (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (ticked first)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 2) = _
  rw [clock_round weight nonnegative players (ticked first) 1 secondCursor, PMF.pure_bind]
  change (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (ticked (ticked first))).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 1) = _
  rw [clock_round weight nonnegative players (ticked (ticked first)) 2 thirdCursor, PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  exact expiry

private theorem beforeFinal_physical (execution : app.Execution) :
    (beforeFinal execution).application = { execution.application with
      clock := execution.application.clock + 3 } := by
  simp only [beforeFinal, ticked, afterSilence, recorded, ReactiveApplication.Execution.respond]

/-- Each possible final observation after optional silence is a genuine
clean final disclosure class, with its clock-three timer still timely at six. -/
theorem final_of_optional_silence
    (decision : LateOpeningRuntimeOptionalOpening.DecisionHistory weight nonnegative)
    (timer : decision.execution.application.activatedAt bobRevealEvent = some 3)
    (clock : decision.execution.application.clock = 3) (observed : app.Execution)
    (sampled : observed ∈ ((beforeFinal decision.execution).environmentStep app
      (.activate bob)).support) :
    ∃ finalDecision : LateOpeningRuntimeBobIncentive.DecisionHistory weight nonnegative,
      finalDecision.execution = observed ∧ finalDecision.answer = decision.answer ∧
        observed.application.clock = 6 := by
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 decision.execution bob ⟨none⟩
      decision.trace
  obtain ⟨beforeTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (fun _ => app.silentPolicy)
      7 5 _ (beforeFinal decision.execution) responded (by
        rw [silence_prefix_law weight nonnegative decision]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have position : (beforeFinal decision.execution).environmentRecall.length = 19 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) beforeTrace
    change (beforeFinal decision.execution).environmentRecall.length + 7 = 26 at counted
    omega
  have selected : (.activate bob : app.Command) ∈ (LateOpeningRuntimeService.scheduler
      weight nonnegative (beforeFinal decision.execution).environmentRecall
        ((beforeFinal decision.execution).observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative _ _).support
    rw [position]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨observedTrace⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 6 _ observed (.activate bob)
      beforeTrace selected sampled
  have physical : observed.application = (beforeFinal decision.execution).application := by
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ sampled
    obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  have finalPhysical := physical.trans (beforeFinal_physical decision.execution)
  have observedBound : observed.application.config.store (.inr bobBindEvent) =
      some (.success decision.answer) := by
    rw [finalPhysical]
    exact decision.bound
  have observedReady : observed.application.config.cut.Ready bobRevealEvent := by
    rw [finalPhysical]
    exact decision.ready
  have observedClock : observed.application.clock = 6 := by
    rw [finalPhysical, clock]
  have timely : observed.application.WithinDeadline LateOpeningRuntimeService.runtime
      bobRevealEvent := by
    unfold State.WithinDeadline
    rw [finalPhysical]
    change (match decision.execution.application.activatedAt bobRevealEvent with
      | none => False
      | some entered => decision.execution.application.clock + 3 - entered <
          LateOpeningRuntimeService.runtime.deadline bobRevealEvent)
    rw [timer, clock]
    decide
  have inputs : observed.network.inputs = decision.execution.network.inputs := by
    rw [app.environmentStep_inputs _ observed (.activate bob) sampled]
    rfl
  have receipts : observed.receipts = decision.execution.receipts :=
    (activation_receipts _ observed bob sampled).trans rfl
  have clean : CleanBindings observed := by
    intro message present owner
    rw [inputs] at present
    obtain ⟨token, content, receipt⟩ := decision.clean message present owner
    exact ⟨token, content, receipts ▸ receipt⟩
  exact ⟨⟨observed, observedTrace, decision.answer, observedBound, observedReady, timely, clean⟩,
    rfl, rfl, observedClock⟩

end Vegas.Examples.LateOpeningRuntimeBobDisclosureChronology

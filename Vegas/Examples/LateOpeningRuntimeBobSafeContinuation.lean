/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobQuietPrefix
import Vegas.Examples.LateOpeningRuntimeNash

/-! # Clean chosen-answer settlement and the quiet/Safe comparison

Bob can bind any selected answer at clock three and open it at the following
optional callback, using only public clock and completion information. Every
such suffix succeeds with zero audit charge. Remaining silent before Alice
settles and then selecting Safe gives a nonnegative early comparison against
arbitrary future Alice policies.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSafeContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobService LateOpeningRuntimeBobAudit LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobQuietPrefix LateOpeningRuntimeUtility

/-- Bind the selected answer at the clock-three commitment callback and open
it at the following callback; all other callbacks remain silent. -/
def answerPolicy (answer : Answer) : app.Policy := fun past view =>
  PMF.pure (if view.application.publicView.clock = 3 then
    if bobBindEvent ∈ view.application.publicView.observation.completionOrder then
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob past view
        bobRevealEvent true
    else LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob past view
      bobBindEvent (.success answer)
  else ⟨none⟩)

/-- The concrete quiet-then-Safe comparison policy. -/
def safePolicy : app.Policy := answerPolicy safe

theorem answerPolicy_silent (answer : Answer) (past : List app.PlayerEntry)
    (view : app.PlayerView) (clock : view.application.publicView.clock ≠ 3) :
    answerPolicy answer past view = PMF.pure ⟨none⟩ := by
  simp only [answerPolicy, ite_eq_right clock]

theorem safePolicy_silent (past : List app.PlayerEntry) (view : app.PlayerView)
    (clock : view.application.publicView.clock ≠ 3) : safePolicy past view = PMF.pure ⟨none⟩ :=
  answerPolicy_silent safe past view clock

private theorem observed_completed (execution : app.Execution) (event : nativeGraph.EventId) :
    event ∈ (execution.observe app bob).application.publicView.observation.completionOrder ↔
      event ∈ execution.application.config.cut.completed := by
  exact execution.application.config.history_exact event

theorem answerPolicy_binding (weight : ℝ) (nonnegative : 0 ≤ weight) (answer : Answer)
    (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (clock : execution.application.clock = 3) :
    answerPolicy answer (execution.recall bob) (execution.observe app bob) =
      PMF.pure (LateOpeningRuntimeBobSuffix.binding answer) := by
  have missing : bobBindEvent ∉
      (execution.observe app bob).application.publicView.observation.completionOrder := by
    rw [observed_completed]
    exact ready.1
  have viewed : (execution.observe app bob).application.publicView.clock = 3 := clock
  simp only [answerPolicy, ite_eq_left viewed, ite_eq_right missing]
  rw [canonical_binding weight nonnegative ⟨remaining, some bob, execution⟩ trace quiet
    ready answer]

theorem answerPolicy_opening (answer : Answer) (execution : app.Execution)
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (clock : execution.application.clock = 3) :
    answerPolicy answer (execution.recall bob) (execution.observe app bob) =
      PMF.pure (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (execution.recall bob) (execution.observe app bob) bobRevealEvent true) := by
  have done : bobBindEvent ∈
      (execution.observe app bob).application.publicView.observation.completionOrder := by
    rw [observed_completed]
    exact ready.2 (by decide)
  have viewed : (execution.observe app bob).application.publicView.clock = 3 := clock
  simp only [answerPolicy, ite_eq_left viewed, ite_eq_left done]

private theorem activation_physical (execution observed : app.Execution) (who : Player)
    (sampled : observed ∈ (execution.environmentStep app (.activate who)).support) :
    observed.application = execution.application := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ sampled
  obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

/-- Every supported optional observation immediately after the accepted
clock-three binding is a genuine timely opening decision. -/
theorem optional_activation (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution observed : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨13, none, execution⟩))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (clock : execution.application.clock = 3)
    (timer : execution.application.activatedAt bobRevealEvent = some 3)
    (sampled : observed ∈ (execution.environmentStep app (.activate bob)).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨12, some bob, observed⟩)) ∧
      observed.application = execution.application ∧
        observed.network.inputs = execution.network.inputs ∧
          observed.application.config.cut.Ready bobRevealEvent ∧
            observed.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent ∧
              observed.application.clock = 3 := by
  have position : execution.environmentRecall.length = 13 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 13 = 26 at counted
    omega
  have done : bobBindEvent ∈ execution.application.publicView.observation.completionOrder :=
    (execution.application.config.history_exact bobBindEvent).mpr (ready.2 (by decide))
  have selected : (.activate bob : app.Command) ∈ (LateOpeningRuntimeService.scheduler
      weight nonnegative execution.environmentRecall
        (execution.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    rw [position]
    change _ ∈ (PMF.pure (if bobBindEvent ∈
      execution.application.publicView.observation.completionOrder
        then (.activate bob : app.Command) else .wait)).support
    rw [ite_eq_left done]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨observedTrace⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 execution observed (.activate bob)
      trace selected sampled
  have physical := activation_physical execution observed bob sampled
  refine ⟨⟨observedTrace⟩, physical, app.environmentStep_inputs execution observed
    (.activate bob) sampled, physical ▸ ready, ?_, physical ▸ clock⟩
  rw [physical]
  unfold State.WithinDeadline
  rw [timer, clock]
  decide

/-- A protected receiver service round retains exactly the inputs already
authored by the response, including after arbitrary earlier raw traffic. -/
theorem protected_round_inputs (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (response : app.Action) (players : Player → app.Policy) (next : app.Execution)
    (reached : next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players (execution.respond app bob response)).support) :
    next.network.inputs = (execution.respond app bob response).network.inputs := by
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have served := protected_response_scheduler weight nonnegative
    ⟨remaining, some bob, execution⟩ trace bob rfl response (Or.inl rfl)
  rw [served, PMF.mem_support_pure_iff] at selected
  subst command
  obtain ⟨middle, supported, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have passive := (latestAuthor_passive bob
    ((execution.respond app bob response).observeEnvironment app)).1
  rw [passive] at resumed
  cases (PMF.mem_support_pure_iff _ _).mp resumed
  exact app.environmentStep_inputs _ _ _ supported

private theorem late_command_actor (weight : ℝ) (nonnegative : 0 ≤ weight)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (late : 15 ≤ past.length)
    (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      past view).support) :
    command.actor? app = none ∨ command = .activate bob ∧ past.length = 19 := by
  change command ∈ (stageChoice weight nonnegative past.length view).support at selected
  generalize positionEq : past.length = position at selected late ⊢
  by_cases inside : position < 26
  · interval_cases position <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    all_goals subst command
    all_goals first
      | exact Or.inl rfl
      | exact Or.inl (latestAuthor_passive bob view).1
      | exact Or.inr ⟨rfl, rfl⟩
  · have outside : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | rfl | omega
    rw [outside, PMF.mem_support_pure_iff] at selected
    subst command
    exact Or.inl rfl

/-- After the early opening's service, the final callback is silent;
every later actual supported execution retains the exact authored inputs. -/
theorem after_opening_inputs (weight : ℝ) (nonnegative : 0 ≤ weight) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (count remaining : Nat) (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining + count, none, execution⟩))
    (late : 15 ≤ execution.environmentRecall.length)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) : final.network.inputs = execution.network.inputs := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨next, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have sourceTrace : (app.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
            (some ⟨remaining + count + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      obtain ⟨nextTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) players (remaining + count)
          execution next sourceTrace moved
      have length := app.round_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) players execution next moved
      have inherited := ih next nextTrace (by omega) continued
      apply inherited.trans
      obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨middle, supported, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have oldInputs := app.environmentStep_inputs execution middle command supported
      rcases late_command_actor weight nonnegative _ _ late command selected with passive | active
      · rw [passive] at resumed
        cases (PMF.mem_support_pure_iff _ _).mp resumed
        exact oldInputs
      · obtain ⟨rfl, position⟩ := active
        have physical := activation_physical execution middle bob supported
        have clock : middle.application.clock = 6 := by
          rw [physical, clock_history weight nonnegative
            ⟨remaining + count + 1, none, execution⟩ sourceTrace, position]
          decide
        have silent : answerPolicy answer (middle.recall bob) (middle.observe app bob) =
            PMF.pure ⟨none⟩ := answerPolicy_silent answer _ _
              (by change middle.application.clock ≠ 3; omega)
        change next ∈ ((players bob (middle.recall bob) (middle.observe app bob)).map
          (middle.respond app bob)).support at resumed
        rw [bobPolicy, silent, PMF.pure_map, PMF.mem_support_pure_iff] at resumed
        subst next
        exact oldInputs

private theorem binding_two_rounds (weight : ℝ) (nonnegative : 0 ≤ weight) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (execution next : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨15, none, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (clock : execution.application.clock = 3)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 2 execution).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some ⟨13, none, next⟩)) ∧
      next.application.config.store (.inr bobBindEvent) = some (.success answer) ∧
        next.application.config.cut.Ready bobRevealEvent ∧
          next.application.activatedAt bobRevealEvent = some 3 ∧
            next.application.clock = 3 ∧ CleanBindings next := by
  obtain ⟨first, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  simp only [ReactiveApplication.runRounds, PMF.bind_pure] at continued
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have position : execution.environmentRecall.length = 11 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 15 = 26 at counted
    omega
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    at selected
  rw [position, stageChoice, PMF.mem_support_pure_iff] at selected
  subst command
  obtain ⟨observed, sampled, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have selected : (.activate bob : app.Command) ∈ (LateOpeningRuntimeService.scheduler
      weight nonnegative execution.environmentRecall
        (execution.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    rw [position]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨observedTrace⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution observed (.activate bob)
      trace selected sampled
  have physical := activation_physical execution observed bob sampled
  have observedQuiet : SilentRecall observed := by
    intro entry member
    rw [app.environmentStep_recall execution observed (.activate bob) sampled] at member
    exact quiet entry member
  have observedReady := physical ▸ ready
  have observedTimely := physical ▸ timely
  have observedClock := physical ▸ clock
  have policy := answerPolicy_binding weight nonnegative answer 14 observed observedTrace
    observedQuiet observedReady observedClock
  change first ∈ ((players bob (observed.recall bob) (observed.observe app bob)).map
    (observed.respond app bob)).support at resumed
  rw [bobPolicy, policy, PMF.pure_map, PMF.mem_support_pure_iff] at resumed
  subst first
  obtain ⟨served, law, bound, _, revealReady, timer, clean, _⟩ := binding_round weight nonnegative
    14 observed observedTrace observedQuiet observedReady observedTimely answer
  rw [law players, PMF.mem_support_pure_iff] at continued
  subst next
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 observed bob
      (LateOpeningRuntimeBobSuffix.binding answer) observedTrace
  obtain ⟨servedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 13 _ served
      respondedTrace (by rw [law players]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have servedClock : served.application.clock = 3 := by
    have cursor := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) servedTrace
    change served.environmentRecall.length + 13 = 26 at cursor
    rw [clock_history weight nonnegative ⟨13, none, served⟩ servedTrace]
    have : served.environmentRecall.length = 13 := by omega
    rw [this]
    decide
  rw [observedClock] at timer
  exact ⟨⟨servedTrace⟩, bound, revealReady, timer, servedClock, clean⟩

theorem answer_opening_two_rounds (weight : ℝ) (nonnegative : 0 ≤ weight) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (execution next : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨13, none, execution⟩))
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timer : execution.application.activatedAt bobRevealEvent = some 3)
    (clock : execution.application.clock = 3) (clean : CleanBindings execution)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 2 execution).support) :
    ∃ origin candidate,
      Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨11, none, next⟩)) ∧
        next.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
          ((openingMessage origin candidate answer).id, true) ∈ next.receipts ∧
            ∀ message ∈ next.network.inputs, message.sender = bob →
              (∃ token, message.payload =
                ⟨.commitment bobBindEvent (bob, .prepared 0), none, token⟩ ∧
                (message.id, true) ∈ next.receipts) ∨
              message = openingMessage origin candidate answer := by
  obtain ⟨first, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  simp only [ReactiveApplication.runRounds, PMF.bind_pure] at continued
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have position : execution.environmentRecall.length = 13 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 13 = 26 at counted
    omega
  have done : bobBindEvent ∈ execution.application.publicView.observation.completionOrder :=
    (execution.application.config.history_exact bobBindEvent).mpr (ready.2 (by decide))
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    at selected
  rw [position] at selected
  change command ∈ (PMF.pure (if bobBindEvent ∈
    execution.application.publicView.observation.completionOrder
      then (.activate bob : app.Command) else .wait)).support at selected
  rw [ite_eq_left done, PMF.mem_support_pure_iff] at selected
  subst command
  obtain ⟨observed, sampled, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨⟨observedTrace⟩, physical, oldInputs, observedReady, observedTimely, observedClock⟩ :=
    optional_activation weight nonnegative execution observed trace ready clock timer sampled
  have observedBound : observed.application.config.store (.inr bobBindEvent) =
      some (.success answer) := physical ▸ bound
  obtain ⟨candidate, material, served, decision, emitted, law, published, accepted⟩ :=
    canonical_round weight nonnegative players 12 observed observedTrace answer observedBound
      observedReady observedTimely
  change first ∈ ((players bob (observed.recall bob) (observed.observe app bob)).map
    (observed.respond app bob)).support at resumed
  rw [bobPolicy, answerPolicy_opening answer observed observedReady observedClock, decision,
    PMF.pure_map, PMF.mem_support_pure_iff] at resumed
  subst first
  rw [law, PMF.mem_support_pure_iff] at continued
  subst next
  have servedReached : served ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players (observed.respond app bob ⟨some material⟩)).support := by
    rw [law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 observed bob ⟨some material⟩
      observedTrace
  obtain ⟨servedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 11 _ served
      respondedTrace servedReached
  have inputs : served.network.inputs = execution.network.inputs ++
      [(show Message Player app.Payload from openingMessage observed candidate answer)] := by
    rw [protected_round_inputs weight nonnegative 12 observed observedTrace
      ⟨some material⟩ players served servedReached]
    change observed.network.inputs ++ [⟨(bob, observed.network.nextSerial bob),
      app.packet (app.submit observed.application bob material) bob
        (observed.network.known bob) material⟩] = _
    rw [emitted, oldInputs]
    rfl
  refine ⟨observed, candidate, ⟨servedTrace⟩, published, accepted, ?_⟩
  intro message member owner
  rw [inputs, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · obtain ⟨token, content, receipt⟩ := clean message old owner
    refine Or.inl ⟨token, content, ?_⟩
    exact (app.receipt_policyInvariant players (message.id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 2 execution served receipt reached
  · exact Or.inr rfl

/-- An arbitrary selected first commitment and its next canonical opening
settle successfully with zero audit charge throughout the actual suffix. -/
theorem answer_continuation_clean (weight : ℝ) (nonnegative : 0 ≤ weight) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14
        (execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer))).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks sample)
          (app.finished final) bob = 0 := by
  have whole := reached
  obtain ⟨bound, binding, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨served, law, boundValue, _, revealReady, timer, clean, _⟩ := binding_round weight
    nonnegative 14 execution trace quiet ready timely answer
  rw [law players, PMF.mem_support_pure_iff] at binding
  subst bound
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob
      (LateOpeningRuntimeBobSuffix.binding answer) trace
  obtain ⟨boundTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 13 _ served respondedTrace
      (by rw [law players]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have cursor : execution.environmentRecall.length = 12 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 14 = 26 at counted
    omega
  have clock : execution.application.clock = 3 := by
    rw [clock_history weight nonnegative ⟨14, some bob, execution⟩ trace, cursor]
    decide
  rw [clock] at timer
  have boundClock : served.application.clock = 3 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) boundTrace
    change served.environmentRecall.length + 13 = 26 at counted
    have position : served.environmentRecall.length = 13 := by omega
    rw [clock_history weight nonnegative ⟨13, none, served⟩ boundTrace, position]
    decide
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 2 11] at rest
  obtain ⟨opened, opening, suffix⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
  obtain ⟨origin, candidate, ⟨openedTrace⟩, published, accepted, only⟩ :=
    answer_opening_two_rounds weight nonnegative answer players bobPolicy served opened boundTrace
      boundValue revealReady timer boundClock clean opening
  have late : 15 ≤ opened.environmentRecall.length := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) openedTrace
    change opened.environmentRecall.length + 11 = 26 at counted
    omega
  have inputs := after_opening_inputs weight nonnegative answer players bobPolicy 11 0 opened final
    openedTrace late suffix
  have finalPublished := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
      (.success answer)) players).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final published suffix
  have finalAccepted := (app.receipt_policyInvariant players
    ((openingMessage origin candidate answer).id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final accepted suffix
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final respondedTrace
      whole
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨0, none, final⟩ finalTrace
  have finalBound := bob_success_from_binding final.application _ valid.reachable answer
    finalPublished
  refine ⟨finalPublished, charge_zero weight nonnegative ⟨0, none, final⟩ finalTrace answer
    finalBound origin candidate finalAccepted ?_ sample authentic⟩
  intro message member owner
  rw [inputs] at member
  rcases only message member owner with ⟨token, content, receipt⟩ | same
  · refine Or.inl ⟨token, content, ?_⟩
    exact (app.receipt_policyInvariant players (message.id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final receipt suffix
  · exact Or.inr same

/-- The complete comparison continuation succeeds and has zero actual audit
charge against arbitrary future Alice actions and authentic evidence sampling. -/
theorem safe_continuation_clean (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bobPolicy : players bob = safePolicy)
    (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (empty : execution.recall bob = [])
    (unresolved : aliceEvent ∉ execution.application.config.cut.completed)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 21 (execution.respond app bob ⟨none⟩)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success safe) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks sample)
          (app.finished final) bob = 0 := by
  obtain ⟨quietTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 execution bob ⟨none⟩ trace
  have cursor : (execution.respond app bob ⟨none⟩).environmentRecall.length = 5 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 21 = 26 at counted
    change execution.environmentRecall.length = 5
    omega
  have quiet : SilentRecall (execution.respond app bob ⟨none⟩) := by
    intro entry member
    change entry ∈ execution.recall bob ++
      [⟨execution.observe app bob, ⟨none⟩, none⟩] at member
    simp only [empty, List.nil_append, List.mem_singleton] at member
    subst entry
    rfl
  have whole := reached
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 6 15] at reached
  obtain ⟨before, quietReached, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨⟨beforeTrace⟩, beforeQuiet, ready, timely, clock, _⟩ := before_binding weight nonnegative
    players _ before quietTrace cursor unresolved quiet quietReached
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 2 13] at rest
  obtain ⟨bound, binding, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
  obtain ⟨⟨boundTrace⟩, boundSafe, revealReady, timer, boundClock, clean⟩ :=
    binding_two_rounds weight nonnegative safe players bobPolicy before bound beforeTrace
      beforeQuiet ready timely clock binding
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 2 11] at rest
  obtain ⟨opened, opening, suffix⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
  obtain ⟨origin, candidate, ⟨openedTrace⟩, published, accepted, only⟩ :=
    answer_opening_two_rounds weight nonnegative safe players bobPolicy bound opened boundTrace
      boundSafe revealReady timer boundClock clean opening
  have late : 15 ≤ opened.environmentRecall.length := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) openedTrace
    change opened.environmentRecall.length + 11 = 26 at counted
    omega
  have inputs := after_opening_inputs weight nonnegative safe players bobPolicy 11 0 opened final
    openedTrace late suffix
  have finalPublished := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
      (.success safe)) players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        11 opened final published suffix
  have finalAccepted := (app.receipt_policyInvariant players
    ((openingMessage origin candidate safe).id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final accepted suffix
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 21 _ final quietTrace whole
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨0, none, final⟩ finalTrace
  have finalBound := bob_success_from_binding final.application _ valid.reachable safe
    finalPublished
  refine ⟨finalPublished, charge_zero weight nonnegative ⟨0, none, final⟩ finalTrace safe finalBound
    origin candidate finalAccepted ?_ sample authentic⟩
  intro message member owner
  rw [inputs] at member
  rcases only message member owner with ⟨token, content, receipt⟩ | same
  · refine Or.inl ⟨token, content, ?_⟩
    exact (app.receipt_policyInvariant players (message.id, true)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final receipt suffix
  · exact Or.inr same

/-- Silence now followed by this observable Safe policy has nonnegative
actual terminal payoff. No numerical reward, forfeit or collateral premise,
and no restriction on Alice's later raw policy, is required. -/
theorem safe_continuation_nonnegative (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bobPolicy : players bob = safePolicy)
    (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (empty : execution.recall bob = [])
    (unresolved : aliceEvent ∉ execution.application.config.cut.completed)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 21 (execution.respond app bob ⟨none⟩)).support) :
    0 ≤ LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob := by
  obtain ⟨published, clear⟩ := safe_continuation_clean weight nonnegative players bobPolicy
    execution final trace empty unresolved sample authentic reached
  obtain ⟨quietTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 execution bob ⟨none⟩ trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 21 _ final quietTrace reached
  have completed := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨0, none, final⟩ finalTrace
  have bound := bob_success_from_binding final.application _ valid.reachable safe published
  obtain ⟨aliceResult, aliceStored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal completed (.inr aliceEvent))
  have decoded := decode_terminalStateOf final.application bit label aliceResult (.success safe)
    (.success safe) valid.reachable.inputs_eq aliceStored bound published
  have readout : serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
      some (terminalStateOf bit label aliceResult (.success safe) (.success safe)) := by
    unfold serviceSourceReadout
    change (if final.application.config.cut.Terminal then
      decodeState? (terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left completed]
    exact decoded
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [clear, zero_mul, sub_zero, nativeBaseUtility_of_readout reward forfeit _ _ readout bob,
    sourceUtility_bob]
  have success : ((terminalStateOf bit label aliceResult (.success safe)
      (.success safe)).get bobPublication).isSuccess = true := rfl
  rw [ite_eq_left success, sub_zero]
  exact (bob_gross_bounds reward _).1

end Vegas.Examples.LateOpeningRuntimeBobSafeContinuation

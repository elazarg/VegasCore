/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingRuntime
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhaseServiceContract
import Vegas.Pending.PhaseFrontier
import Vegas.Pending.PhaseSeedClockEffects
import Vegas.Pending.PhaseSeedFreshness
import Vegas.Pending.PhaseReadyRequests
import Interaction.ReactiveSchedulerSeedSupport
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveResponseAccounting
import Interaction.ReactiveRecordedRounds

/-! # Concrete phase geometry and service for the private-seed construction -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem event_count : graph.order.eventCount = 4 := rfl

theorem binding_actors : graph.actor? aliceBinding = some alice ∧
    graph.actor? bobBinding = some bob := by
  constructor <;> rfl

theorem reveal_actors : graph.actor? aliceReveal = some alice ∧
    graph.actor? bobReveal = some bob := by
  constructor <;> rfl

theorem binding_layouts : graph.outputLayout aliceBinding = .binding alice .bool ∧
    graph.outputLayout bobBinding = .binding bob .bool := by
  constructor <;> rfl

theorem reveal_layouts : graph.outputLayout aliceReveal = .publication .bool ∧
    graph.outputLayout bobReveal = .publication .bool := by
  constructor <;> rfl

theorem binding_predecessors : graph.order.predecessors aliceBinding = ∅ ∧
    graph.order.predecessors bobBinding = ∅ := by
  constructor <;> decide

theorem reveals_independent :
    (toEventGraph program).IndependentReveals aliceReveal bobReveal := by
  constructor
  · trivial
  constructor
  · trivial
  constructor <;> decide

theorem reveal_predecessors :
    graph.order.predecessors aliceReveal = {aliceBinding, bobBinding} ∧
      graph.order.predecessors bobReveal = {aliceBinding, bobBinding} := by
  classical
  constructor
  · ext prior
    change (prior ∈ ((toEventGraph program).withMode .concurrentReveals).order.predecessors
      aliceReveal) ↔ prior ∈ ({aliceBinding, bobBinding} : Finset graph.EventId)
    rw [EventGraph.withMode_concurrentReveals_predecessors]
    constructor
    · intro member
      have earlier := (toEventGraph program).order.predecessor_lt member.1
      change prior.val < 2 at earlier
      fin_cases prior <;> simp_all [aliceBinding, bobBinding]
    · intro member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact ⟨by decide,
          EventGraph.IndependentReveals.not_of_not_publication_left (by decide)⟩
      · exact ⟨by decide,
          EventGraph.IndependentReveals.not_of_not_publication_left (by decide)⟩
  · ext prior
    change (prior ∈ ((toEventGraph program).withMode .concurrentReveals).order.predecessors
      bobReveal) ↔ prior ∈ ({aliceBinding, bobBinding} : Finset graph.EventId)
    rw [EventGraph.withMode_concurrentReveals_predecessors]
    constructor
    · intro member
      have earlier := (toEventGraph program).order.predecessor_lt member.1
      change prior.val < 3 at earlier
      fin_cases prior
      · simp [aliceBinding]
      · simp [bobBinding]
      · exact (member.2 reveals_independent).elim
      · change 3 < 3 at earlier
        omega
    · intro member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact ⟨by decide,
          EventGraph.IndependentReveals.not_of_not_publication_left (by decide)⟩
      · exact ⟨by decide,
          EventGraph.IndependentReveals.not_of_not_publication_left (by decide)⟩

def commitmentPhase : RuntimePhase graph where
  kind := .commitment
  low := 0
  high := 2
  nonempty := by decide
  bounded := by decide
  fields event lower upper := by
    fin_cases event
    · exact ⟨alice, .bool, rfl⟩
    · exact ⟨bob, .bool, rfl⟩
    · change 2 < 2 at upper
      omega
    · change 3 < 2 at upper
      omega
  sample_singleton impossible := by cases impossible

def publicationPhase : RuntimePhase graph where
  kind := .reveal
  low := 2
  high := 4
  nonempty := by decide
  bounded := by decide
  fields event lower upper := by
    fin_cases event
    · change 2 ≤ 0 at lower
      omega
    · change 2 ≤ 1 at lower
      omega
    · exact ⟨.bool, rfl⟩
    · exact ⟨.bool, rfl⟩
  sample_singleton impossible := by cases impossible

private theorem phase_kind_at_binding (phase : RuntimePhase graph)
    (event : graph.EventId) (owner : Player)
    (output : graph.outputLayout event = .binding owner .bool)
    (lower : phase.low ≤ event.val) (upper : event.val < phase.high) :
    phase.kind = .commitment := by
  have matching := phase.fields event lower upper
  rw [output] at matching
  cases kind : phase.kind <;> simp_all [RuntimePhaseKind.Matches]

private theorem phase_kind_at_publication (phase : RuntimePhase graph)
    (event : graph.EventId) (output : graph.outputLayout event = .publication .bool)
    (lower : phase.low ≤ event.val) (upper : event.val < phase.high) :
    phase.kind = .reveal := by
  have matching := phase.fields event lower upper
  rw [output] at matching
  cases kind : phase.kind <;> simp_all [RuntimePhaseKind.Matches]

/-- The actual chosen maximal compiled partition has these two concrete blocks. -/
theorem plan_phases : plan.phases = [commitmentPhase, publicationPhase] := by
  classical
  have adjacent := plan.adjacent
  have maximal := compiledRuntimePhasePlan_maximal program .concurrentReveals
  change plan.phases.IsChain _ at maximal
  cases phases : plan.phases with
  | nil =>
      have impossible := plan.empty phases
      change 4 = 0 at impossible
      omega
  | cons first rest =>
      have firstLow : first.low = 0 := plan.first first (by simp [phases])
      have firstKind : first.kind = .commitment :=
        phase_kind_at_binding first aliceBinding alice binding_layouts.1
          (by simp [firstLow, aliceBinding]) (by
            change 0 < first.high
            have := first.nonempty
            omega)
      have firstHigh : first.high ≤ 2 := by
        by_contra beyond
        have matching := first.fields aliceReveal (by simp [firstLow, aliceReveal])
          (by change 2 < first.high; omega)
        rw [firstKind, reveal_layouts.1] at matching
        simp only [RuntimePhaseKind.Matches] at matching
        obtain ⟨owner, payload, impossible⟩ := matching
        cases impossible
      cases rest with
      | nil =>
          have last := plan.last first (by simp [phases])
          change first.high = 4 at last
          omega
      | cons second rest =>
          rw [phases] at adjacent maximal
          have nextLow := (List.isChain_cons_cons.mp adjacent).1
          have different := (List.isChain_cons_cons.mp maximal).1
          have firstEnd : first.high = 2 := by
            by_contra unequal
            have one : first.high = 1 := by have := first.nonempty; omega
            have secondKind : second.kind = .commitment :=
              phase_kind_at_binding second bobBinding bob binding_layouts.2
                (by change second.low ≤ 1; omega) (by
                  change 1 < second.high
                  have := second.nonempty
                  omega)
            rcases different with unequalKind | sampled
            · exact unequalKind (firstKind.trans secondKind.symm)
            · rw [firstKind] at sampled
              cases sampled
          have secondLow : second.low = 2 := by omega
          have secondKind : second.kind = .reveal :=
            phase_kind_at_publication second aliceReveal reveal_layouts.1
              (by simp [secondLow, aliceReveal]) (by
                change 2 < second.high
                have := second.nonempty
                omega)
          cases rest with
          | nil =>
              have last := plan.last second (by simp [phases])
              change second.high = 4 at last
              have firstEq : first = commitmentPhase := by
                cases first
                simp_all [commitmentPhase]
              have secondEq : second = publicationPhase := by
                cases second
                simp_all [publicationPhase]
              rw [firstEq, secondEq]
          | cons third rest =>
              have nextAdjacent :=
                (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp adjacent).2).1
              have nextDifferent :=
                (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp maximal).2).1
              have thirdBound : third.high ≤ 4 := third.bounded
              have endThree : second.high = 3 := by
                have := second.nonempty
                have := third.nonempty
                omega
              have thirdKind : third.kind = .reveal :=
                phase_kind_at_publication third bobReveal reveal_layouts.2
                  (by change third.low ≤ 3; omega) (by
                    change 3 < third.high
                    have := third.nonempty
                    omega)
              rcases nextDifferent with unequalKind | sampled
              · exact (unequalKind (secondKind.trans thirdKind.symm)).elim
              · rw [secondKind] at sampled
                cases sampled

theorem initialState_eq : initialState =
    ⟨[commitmentPhase, publicationPhase], 0,
      ⟨State.initial (encodeInputs (Env.empty (CellVal simpleExpr))), ∅⟩,
      ⟨State.initial (encodeInputs (Env.empty (CellVal simpleExpr))), ∅⟩, []⟩ := by
  classical
  let native : EventGraphRuntime.State graph :=
    EventGraphRuntime.State.initial (encodeInputs (Env.empty (CellVal simpleExpr)))
  have drained : commitmentPhase.drain (⟨native, ∅⟩ : RecoveryState graph) = ⟨native, ∅⟩ := by
    apply RuntimePhase.drain_eq_of_clear
    intro event eligible
    rcases eligible.2 with ⟨_ready, excluded⟩
    cases actor : graph.actor? event <;> simp [actor] at excluded
  have unfinished : ¬ commitmentPhase.Finished (⟨native, ∅⟩ : RecoveryState graph) := by
    intro finished
    have inside : aliceBinding ∈ commitmentPhase.events := by
      apply (RuntimePhase.mem_events commitmentPhase aliceBinding).mpr
      change 0 ≤ 0 ∧ 0 < 2
      omega
    have member := finished inside
    change aliceBinding ∈ (EventOrder.Cut.empty graph.order).completed at member
    exact Finset.notMem_empty _ member
  change PhaseRuntimeState.settle plan.phases 0 ⟨native, ∅⟩ ⟨native, ∅⟩ [] = _
  rw [plan_phases, PhaseRuntimeState.settle, drained, ite_eq_right unfinished]

theorem initialState_attempt : initialState.attempt = originalAttempt := by
  rw [initialState_eq]
  rfl

theorem initial_bindings_ready :
    ready alice aliceBinding (initialExecution.observeEnvironment app) = true ∧
      ready bob bobBinding (initialExecution.observeEnvironment app) = true := by
  simp only [ready, decide_eq_true_eq]
  have valid := (PhaseRuntimeState.initial_invariant plan
    (encodeInputs (Env.empty (CellVal simpleExpr)))).1
  change PhaseRuntimeState.requests initialState.publicView alice
      ⟨initialState.attempt, aliceBinding⟩ ∧
    PhaseRuntimeState.requests initialState.publicView bob ⟨initialState.attempt, bobBinding⟩
  rw [initialState.requests_publicView valid, initialState.requests_publicView valid]
  rw [initialState_eq]
  constructor
  · refine ⟨rfl, ⟨commitmentPhase, rfl, ?_⟩, ?_, rfl, ?_⟩
    · decide
    · constructor
      · decide
      · rw [binding_predecessors.1]
        exact Finset.empty_subset _
    · simp
  · refine ⟨rfl, ⟨commitmentPhase, rfl, ?_⟩, ?_, rfl, ?_⟩
    · decide
    · constructor
      · decide
      · rw [binding_predecessors.2]
        exact Finset.empty_subset _
    · simp

theorem timely : runtime.AsyncTimely (fun _ => 0) (fun _ => 5) := by
  intro event _
  change 0 + 5 < 6
  decide

theorem raw_native_valid (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) :
    current.execution.application.Invariant
      (encodeInputs (Env.empty (CellVal simpleExpr))) := by
  exact (phaseApplication_invariant runtime leaks _).history initial horizon selected (by
    intro state supported
    rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
    subst state
    exact (PhaseRuntimeState.initial_invariant plan _).1) trace

theorem raw_phase_geometry (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) :
    current.execution.application.Frontier ∧ current.execution.application.Live ∧
      (current.execution.application.phases.IsChain fun first second =>
        first.kind ≠ second.kind ∨ first.kind = .sample) ∧
      ∀ event, ¬ current.execution.application.current.AutomaticReady event := by
  have ordered := serviceGraph_revealRelaxedOrdered setup .concurrentReveals
  have initialMaximal := compiledRuntimePhasePlan_maximal program .concurrentReveals
  change plan.phases.IsChain _ at initialMaximal
  have quiet := (phaseApplication_quiescent runtime leaks ordered).history initial horizon
    selected (by
      intro state supported
      rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
      subst state
      exact phaseApplication_initial_quiescent plan ordered initialMaximal _) trace
  have living := (phaseApplication_live runtime leaks).history initial horizon selected (by
    intro state supported
    rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
    subst state
    exact ⟨PhaseRuntimeState.initial_frontier plan _, PhaseRuntimeState.initial_live plan _⟩)
      trace
  exact ⟨quiet.1, living.2, quiet.2.1, quiet.2.2⟩

/-- Within either genuine independent phase, a still-uncompleted owned event
is actually ready. Excluded owners have already been drained automatically. -/
theorem raw_phase_event_ready (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (block : phase = commitmentPhase ∨ phase = publicationPhase)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (unfinished : event ∉ current.execution.application.current.native.config.cut.completed) :
    current.execution.application.current.native.config.cut.Ready event := by
  have geometry := raw_phase_geometry selected current trace
  have positioned := geometry.1.positioned
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp installed
  rw [phases] at positioned
  refine ⟨unfinished, ?_⟩
  intro predecessor member
  apply positioned.2.1 predecessor
  rcases block with rfl | rfl
  · have eventBound := (RuntimePhase.mem_events commitmentPhase event).mp inside
    change 0 ≤ event.val ∧ event.val < 2 at eventBound
    fin_cases event
    · change predecessor ∈ graph.order.predecessors aliceBinding at member
      rw [binding_predecessors.1] at member
      exact (Finset.notMem_empty predecessor member).elim
    · change predecessor ∈ graph.order.predecessors bobBinding at member
      rw [binding_predecessors.2] at member
      exact (Finset.notMem_empty predecessor member).elim
    · change 0 ≤ 2 ∧ 2 < 2 at eventBound
      omega
    · change 0 ≤ 3 ∧ 3 < 2 at eventBound
      omega
  · have eventBound := (RuntimePhase.mem_events publicationPhase event).mp inside
    change 2 ≤ event.val ∧ event.val < 4 at eventBound
    fin_cases event
    · change 2 ≤ 0 ∧ 0 < 4 at eventBound
      omega
    · change 2 ≤ 1 ∧ 1 < 4 at eventBound
      omega
    · change predecessor ∈ graph.order.predecessors aliceReveal at member
      rw [reveal_predecessors.1] at member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl <;> decide
    · change predecessor ∈ graph.order.predecessors bobReveal at member
      rw [reveal_predecessors.2] at member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl <;> decide

theorem raw_phase_event_request (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (block : phase = commitmentPhase ∨ phase = publicationPhase)
    (event : graph.EventId) (inside : event ∈ phase.events) (owner : Player)
    (actor : graph.actor? event = some owner)
    (unfinished : event ∉ current.execution.application.current.native.config.cut.completed) :
    current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩ := by
  have geometry := raw_phase_geometry selected current trace
  exact current.execution.application.request_of_ready
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) geometry.1 geometry.2.1
    geometry.2.2.1 geometry.2.2.2 event
    (raw_phase_event_ready selected current trace phase installed block event inside unfinished)
    owner actor

def clockTicks (past : List app.EnvironmentEntry) : Nat :=
  (past.map fun entry => PhaseSeedCalendar.commandTicks runtime leaks entry.command).sum

private theorem pendingCommand_ticks (identifier : MessageId Player)
    (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (pendingCommand identifier view) = 0 := by
  unfold pendingCommand
  split <;> rfl

private theorem activateReady_ticks (owner : Player) (event : graph.EventId)
    (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (activateReady owner event view) = 0 := by
  unfold activateReady
  split <;> rfl

private theorem earlyCommand_ticks (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (earlyCommand owner past view) = 0 := by
  unfold earlyCommand
  split
  · rfl
  · split
    · rfl
    · exact pendingCommand_ticks _ _

private theorem lateCommand_ticks (owner : Player) (seed : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (lateCommand owner seed clock past view) = 0 := by
  unfold lateCommand
  split
  · split
    · rfl
    · exact pendingCommand_ticks _ _
  · rfl

private theorem pollCommand_ticks (owner : Player) (seed wanted : Bool)
    (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (pollCommand owner seed wanted view) = 0 := by
  unfold pollCommand
  split
  · exact activateReady_ticks _ _ _
  · rfl

def originalTick (position : Nat) : Nat :=
  if position ∈ ({2, 3, 8, 11, 16, 19} : Finset Nat) then 1 else 0

theorem originalCommand_ticks (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks
        (originalCommand seeds position past view) = originalTick position := by
  match position with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
      18 | 19 | 20 | 21 =>
      simp only [originalCommand, originalTick, activateReady_ticks,
        pollCommand_ticks, earlyCommand_ticks, lateCommand_ticks]
      all_goals decide
  | n + 22 =>
      have different : n + 22 ∉ ({2, 3, 8, 11, 16, 19} : Finset Nat) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      simp only [originalCommand, originalTick, ite_eq_right different,
        PhaseSeedCalendar.commandTicks]

def originalClockFrom (start : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => originalTick start + originalClockFrom (start + 1) count

def originalClock (count : Nat) : Nat := originalClockFrom 0 count

private theorem clockTicks_of_original_commands (seeds : Seeds)
    (earlier past : List app.EnvironmentEntry)
    (commands : app.commandConsistentFrom choose seeds earlier past)
    (original : ∀ entry ∈ past, entry.beforeView.application.attempt = originalAttempt) :
    clockTicks past = originalClockFrom earlier.length past.length := by
  induction past generalizing earlier with
  | nil => rfl
  | cons entry rest ih =>
      have head := original entry (by simp)
      have chosen := commands.1
      rw [choose_original seeds earlier entry.beforeView head] at chosen
      have following := ih (earlier ++ [entry]) commands.2 (by
        intro later member
        exact original later (by simp [member]))
      simp only [clockTicks, List.map_cons, List.sum_cons, List.length_cons,
        originalClockFrom, ← chosen, originalCommand_ticks]
      simpa only [clockTicks, List.length_append, List.length_singleton] using
        congrArg (fun count => originalTick earlier.length + count) following

theorem originalClock_end : originalClock 22 = 6 := by decide

/-- Private preparation, leaks and inclusion never create extra elapsed time,
including on raw histories that reset or exhaust an attempt. -/
theorem raw_clock_history (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) :
    current.execution.application.current.native.clock =
      clockTicks current.execution.environmentRecall := by
  let input : graph.Inputs := encodeInputs (Env.empty (CellVal simpleExpr))
  let predicate : app.Execution → Prop := fun execution =>
    execution.application.Invariant input ∧
      execution.application.current.native.clock = clockTicks execution.environmentRecall
  have invariant : app.ServiceInvariant selected predicate := by
    constructor
    · intro execution owner action valid
      refine ⟨(phaseApplication_invariant runtime leaks input).respond execution owner action
        valid.1, ?_⟩
      rw [PhaseSeedCalendar.respond_clock runtime leaks execution valid.1 owner action,
        app.respond_environmentRecall]
      exact valid.2
    · intro execution next command valid _selected reached
      refine ⟨(phaseApplication_invariant runtime leaks input).environmentStep
        execution next command valid.1 reached, ?_⟩
      rw [PhaseSeedCalendar.environmentStep_clock runtime leaks execution next command
        valid.1 reached, app.environmentStep_environmentRecall execution next command reached]
      simpa only [clockTicks, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] using
          congrArg (fun clock => clock + PhaseSeedCalendar.commandTicks runtime leaks command)
            valid.2
  have valid := invariant.history initial horizon (by
    intro state supported
    rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
    subst state
    exact ⟨(PhaseRuntimeState.initial_invariant plan input).1, by
      simpa only [ReactiveApplication.Execution.initial, clockTicks, List.map_nil,
        List.sum_nil] using initialState_clock⟩) trace
  exact valid.2

theorem family_commands (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current)) :
    app.commandConsistentFrom choose seeds [] current.execution.environmentRecall := by
  exact (app.deterministic_transcript_invariant choose seeds).history initial horizon
    (by intro state _; trivial) trace

theorem earlier_original_attempt (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (entry : app.EnvironmentEntry) (member : entry ∈ current.execution.environmentRecall) :
    entry.beforeView.application.attempt = originalAttempt := by
  have past := PhaseSeedFreshness.namespacePast_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seeds) current trace
  have bounds := past.earlier entry member
  rw [original] at bounds
  cases address : entry.beforeView.application.attempt with
  | mk phase generation =>
      simp only [address, originalAttempt] at bounds
      have zeroPhase : phase = 0 := by omega
      have zeroGeneration : generation = 0 := by omega
      simp only [zeroPhase, zeroGeneration, originalAttempt]

theorem original_clock_index (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) :
    current.execution.application.current.native.clock =
      originalClock current.execution.environmentRecall.length := by
  rw [raw_clock_history (family seeds) current trace]
  exact clockTicks_of_original_commands seeds [] current.execution.environmentRecall
    (family_commands seeds current trace) (earlier_original_attempt seeds current trace original)

/-- A real original-attempt input at clock zero cannot lie after either
of the two initial clock advances, regardless of the raw response choices. -/
theorem original_zero_clock_index (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (zero : current.execution.application.current.native.clock = 0) :
    current.execution.environmentRecall.length ≤ 2 := by
  have clocks := raw_clock_history (family seeds) current trace
  have commands := family_commands seeds current trace
  cases recalled : current.execution.environmentRecall with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest =>
          cases rest with
          | nil => simp
          | cons third rest =>
              have old := earlier_original_attempt seeds current trace original third (by
                rw [recalled]
                simp)
              rw [recalled] at commands clocks
              have thirdCommand := commands.2.2.1
              change choose seeds [first, second] third.beforeView = third.command at thirdCommand
              rw [choose_original seeds [first, second] third.beforeView old] at thirdCommand
              change (.application .advanceClock : app.Command) = third.command at thirdCommand
              simp only [zero, clockTicks, List.map_cons, List.sum_cons,
                ← thirdCommand, PhaseSeedCalendar.commandTicks,
                EnvironmentCommand.clockTicks] at clocks
              omega

theorem responseCommand_silent (execution : app.Execution) (owner : Player)
    (past : List app.EnvironmentEntry) (entry : app.EnvironmentEntry)
    (serial : entry.beforeView.network.nextSerial owner = execution.network.nextSerial owner) :
    responseCommand owner (past ++ [entry])
      ((execution.respond app owner ⟨none⟩).observeEnvironment app) = .wait := by
  simp [responseCommand, ReactiveApplication.Execution.respond,
    ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView, serial]

theorem responseCommand_transmission (execution : app.Execution) (owner : Player)
    (past : List app.EnvironmentEntry) (entry : app.EnvironmentEntry)
    (command : entry.command = .activate owner)
    (serial : entry.beforeView.network.nextSerial owner = execution.network.nextSerial owner)
    (submission : app.Submission) :
    responseCommand owner (past ++ [entry])
      ((execution.respond app owner ⟨some submission⟩).observeEnvironment app) =
        .include (owner, execution.network.nextSerial owner) := by
  simp [responseCommand, ReactiveApplication.Execution.respond,
    ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView,
    MessageNetwork.submit, pendingCommand, command, serial]

theorem tailIndex_congr_attempt (past : List app.EnvironmentEntry)
    (first second : app.EnvironmentView)
    (same : first.application.attempt = second.application.attempt) :
    tailIndex past first = tailIndex past second := by
  simp only [tailIndex, same]

theorem tailIndex_fresh (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (fresh : ∀ entry ∈ past, entry.beforeView.application.attempt ≠ view.application.attempt) :
    tailIndex past view = 0 := by
  have absent : past.findIdx (fun entry =>
      entry.beforeView.application.attempt = view.application.attempt) = past.length := by
    apply List.findIdx_eq_length_of_false
    intro entry member
    exact decide_eq_false (fresh entry member)
  simp only [tailIndex, absent, Nat.sub_self]

theorem tailIndex_record (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command) :
    tailIndex (past ++ [⟨view, command⟩]) view = tailIndex past view + 1 := by
  have bounded := List.findIdx_le_length (p := fun entry : app.EnvironmentEntry =>
    entry.beforeView.application.attempt = view.application.attempt) (xs := past)
  have found : (⟨view, command⟩ :: ([] : List app.EnvironmentEntry)).findIdx
      (fun entry => entry.beforeView.application.attempt = view.application.attempt) = 0 := by
    simp only [List.findIdx_cons, decide_true, ite_eq_left True.intro]
  simp only [tailIndex, List.length_append, List.length_singleton, List.findIdx_append,
    found, Nat.zero_add]
  split <;> omega

/-- Retiring a full namespace starts the next actual block at index zero,
including rollback and exhausted restoration. -/
theorem tailIndex_after_retirement (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (next : app.Execution) (command : app.Command)
    (reached : next ∈ (current.execution.environmentStep app command).support)
    (changed : current.execution.application.attempt ≠ next.application.attempt) :
    tailIndex next.environmentRecall (next.observeEnvironment app) = 0 := by
  have namespaceFact := PhaseSeedFreshness.namespacePast_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seeds) current trace
  have fresh := PhaseSeedFreshness.fresh_after_environment runtime leaks current.execution next
    command namespaceFact reached changed
  apply tailIndex_fresh
  intro entry member equal
  exact fresh entry member equal.symm

theorem tailIndex_after_same_attempt (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support)
    (same : next.application.attempt = execution.application.attempt) :
    tailIndex next.environmentRecall (next.observeEnvironment app) =
      tailIndex execution.environmentRecall (execution.observeEnvironment app) + 1 := by
  rw [tailIndex_congr_attempt next.environmentRecall (next.observeEnvironment app)
    (execution.observeEnvironment app) same]
  rw [app.environmentStep_environmentRecall execution next command reached]
  exact tailIndex_record _ _ _

end Vegas.Examples.CommitSeedSignalling

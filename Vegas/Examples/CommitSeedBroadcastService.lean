/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRuntime
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhaseServiceContract
import Vegas.Pending.PhaseFrontier
import Vegas.Pending.PhaseSeedClockEffects
import Vegas.Pending.PhaseSeedFreshness
import Vegas.Pending.PhaseReadyRequests
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveRecordedRounds

/-! # Native phase geometry and elapsed clocks for the three-owner service -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

theorem event_count : graph.order.eventCount = 6 := rfl

theorem binding_actor (owner : Player) : graph.actor? (bindingEvent owner) = some owner := by
  fin_cases owner <;> rfl

theorem reveal_actor (owner : Player) : graph.actor? (revealEvent owner) = some owner := by
  fin_cases owner <;> rfl

theorem binding_predecessors (owner : Player) :
    graph.order.predecessors (bindingEvent owner) = ∅ := by
  fin_cases owner <;> decide

theorem reveals_independent (first second : Player) (different : first ≠ second) :
    (toEventGraph program).IndependentReveals (revealEvent first) (revealEvent second) := by
  fin_cases first <;> fin_cases second
  all_goals first
  | exact (different rfl).elim
  | (constructor
     · trivial
     constructor
     · trivial
     constructor <;> decide)

/-- Every publication waits for all bindings, and for no other publication. -/
theorem reveal_predecessors (owner : Player) (prior : graph.EventId) :
    prior ∈ graph.order.predecessors (revealEvent owner) ↔ prior.val < 3 := by
  classical
  change prior ∈ ((toEventGraph program).withMode .concurrentReveals).order.predecessors
    (revealEvent owner) ↔ _
  rw [EventGraph.withMode_concurrentReveals_predecessors]
  constructor
  · intro member
    by_contra outside
    have bounded : prior.val < 6 := prior.isLt
    let other : Player := ⟨prior.val - 3, by omega⟩
    have position : prior = revealEvent other := by
      apply Fin.ext
      change prior.val = prior.val - 3 + 3
      omega
    rw [position] at member
    by_cases same : other = owner
    · rw [same] at member
      have impossible := (toEventGraph program).order.predecessor_lt member.1
      exact (Nat.lt_irrefl _ impossible).elim
    · exact member.2 (reveals_independent other owner same)
  · intro before
    constructor
    · fin_cases owner <;> fin_cases prior
      all_goals first | (norm_num at before; done) | decide
    · apply EventGraph.IndependentReveals.not_of_not_publication_left
      change ¬ (graph.outputLayout prior).IsPublication
      fin_cases prior
      all_goals first | (norm_num at before; done) | decide

def commitmentPhase : RuntimePhase graph where
  kind := .commitment
  low := 0
  high := 3
  nonempty := by decide
  bounded := by decide
  fields event lower upper := by
    change Fin 6 at event
    fin_cases event
    · exact ⟨alice, .bool, rfl⟩
    · exact ⟨bob, .bool, rfl⟩
    · exact ⟨carol, .bool, rfl⟩
    all_goals norm_num at upper
  sample_singleton impossible := by cases impossible

def publicationPhase : RuntimePhase graph where
  kind := .reveal
  low := 3
  high := 6
  nonempty := by decide
  bounded := by decide
  fields event lower upper := by
    change Fin 6 at event
    fin_cases event
    · norm_num at lower
    · norm_num at lower
    · norm_num at lower
    · exact ⟨.bool, rfl⟩
    · exact ⟨.bool, rfl⟩
    · exact ⟨.bool, rfl⟩
  sample_singleton impossible := by cases impossible

private theorem phase_kind_binding (phase : RuntimePhase graph)
    (owner : Player) (lower : phase.low ≤ (bindingEvent owner).val)
    (upper : (bindingEvent owner).val < phase.high) : phase.kind = .commitment := by
  have matching := phase.fields (bindingEvent owner) lower upper
  change phase.kind.Matches (graph.layout (.inr (bindingEvent owner))) at matching
  rw [bindingEvent_layout] at matching
  cases kind : phase.kind <;> simp_all [RuntimePhaseKind.Matches]

private theorem phase_kind_publication (phase : RuntimePhase graph)
    (owner : Player) (lower : phase.low ≤ (revealEvent owner).val)
    (upper : (revealEvent owner).val < phase.high) : phase.kind = .reveal := by
  have matching := phase.fields (revealEvent owner) lower upper
  change phase.kind.Matches (graph.layout (.inr (revealEvent owner))) at matching
  rw [revealEvent_layout] at matching
  cases kind : phase.kind <;> simp_all [RuntimePhaseKind.Matches]

private theorem phase_kind_from_low (phase : RuntimePhase graph) :
    phase.kind = if phase.low < 3 then .commitment else .reveal := by
  by_cases before : phase.low < 3
  · rw [ite_eq_left before]
    exact phase_kind_binding phase ⟨phase.low, before⟩ (Nat.le_refl _) phase.nonempty
  · rw [ite_eq_right before]
    have bounded : phase.low < 6 := phase.nonempty.trans_le phase.bounded
    let owner : Player := ⟨phase.low - 3, by omega⟩
    have position : (revealEvent owner).val = phase.low := by
      change phase.low - 3 + 3 = phase.low
      omega
    exact phase_kind_publication phase owner (by rw [position]) (by
      rw [position]
      exact phase.nonempty)

/-- The maximal compiler-selected phase partition has exactly the two native blocks. -/
theorem plan_phases : plan.phases = [commitmentPhase, publicationPhase] := by
  classical
  have adjacent := plan.adjacent
  have maximal := compiledRuntimePhasePlan_maximal program .concurrentReveals
  change plan.phases.IsChain _ at maximal
  cases phases : plan.phases with
  | nil =>
      have impossible := plan.empty phases
      change 6 = 0 at impossible
      omega
  | cons first rest =>
      have firstLow : first.low = 0 := plan.first first (by simp [phases])
      have firstKind : first.kind = .commitment := by
        simpa only [firstLow, Nat.zero_lt_succ, ite_true] using phase_kind_from_low first
      have firstHigh : first.high ≤ 3 := by
        by_contra beyond
        have matching := first.fields (revealEvent alice) (by
          change first.low ≤ 3
          omega) (by change 3 < first.high; omega)
        change first.kind.Matches (graph.layout (.inr (revealEvent alice))) at matching
        rw [firstKind, revealEvent_layout] at matching
        obtain ⟨owner, payload, impossible⟩ := matching
        cases impossible
      cases rest with
      | nil =>
          have last := plan.last first (by simp [phases])
          change first.high = 6 at last
          omega
      | cons second rest =>
          rw [phases] at adjacent maximal
          have nextLow := (List.isChain_cons_cons.mp adjacent).1
          have different := (List.isChain_cons_cons.mp maximal).1
          have firstEnd : first.high = 3 := by
            by_contra unequal
            have below : second.low < 3 := by omega
            have secondKind : second.kind = .commitment := by
              simpa only [ite_eq_left below] using phase_kind_from_low second
            rcases different with unequalKind | sampled
            · exact unequalKind (firstKind.trans secondKind.symm)
            · rw [firstKind] at sampled
              cases sampled
          have secondLow : second.low = 3 := by omega
          have secondKind : second.kind = .reveal := by
            simpa only [secondLow, Nat.lt_irrefl, ite_false] using phase_kind_from_low second
          cases rest with
          | nil =>
              have last := plan.last second (by simp [phases])
              change second.high = 6 at last
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
              have after : ¬ third.low < 3 := by
                have := second.nonempty
                omega
              have thirdKind : third.kind = .reveal := by
                simpa only [ite_eq_right after] using phase_kind_from_low third
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
    have inside : bindingEvent alice ∈ commitmentPhase.events := by
      apply (RuntimePhase.mem_events commitmentPhase (bindingEvent alice)).mpr
      change 0 ≤ 0 ∧ 0 < 3
      omega
    have member := finished inside
    change bindingEvent alice ∈ (EventOrder.Cut.empty graph.order).completed at member
    exact Finset.notMem_empty _ member
  change PhaseRuntimeState.settle plan.phases 0 ⟨native, ∅⟩ ⟨native, ∅⟩ [] = _
  rw [plan_phases, PhaseRuntimeState.settle, drained, ite_eq_right unfinished]

theorem initialState_attempt : initialState.attempt = originalAttempt := by
  rw [initialState_eq]
  rfl

theorem initialState_clock : initialState.current.native.clock = 0 := by
  rw [initialState_eq]
  rfl

theorem initialState_candidate (owner : Player) (serial : Nat) :
    initialState.current.native.candidates.lookup (owner, .prepared serial) = .fresh := by
  rw [initialState_eq]
  exact State.initial_candidate _ owner (.prepared serial)

theorem initial_bindings_ready (owner : Player) :
    PhaseRuntimeState.requests initialState.publicView owner (originalCoordinate owner) := by
  have valid := (PhaseRuntimeState.initial_invariant plan
    (encodeInputs (Env.empty (CellVal simpleExpr)))).1
  rw [initialState.requests_publicView valid]
  rw [show originalCoordinate owner = ⟨initialState.attempt, bindingEvent owner⟩ by
    rw [initialState_attempt]; rfl]
  rw [initialState_eq]
  refine ⟨rfl, ⟨commitmentPhase, rfl, ?_⟩, ?_, binding_actor owner, ?_⟩
  · apply (RuntimePhase.mem_events commitmentPhase _).mpr
    change 0 ≤ owner.val ∧ owner.val < 3
    exact ⟨Nat.zero_le _, owner.isLt⟩
  · constructor
    · change bindingEvent owner ∉ (∅ : Finset graph.EventId)
      exact Finset.notMem_empty _
    · rw [binding_predecessors]
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
    rw [initial, PMF.mem_support_pure_iff] at supported
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
      rw [initial, PMF.mem_support_pure_iff] at supported
      subst state
      exact phaseApplication_initial_quiescent plan ordered initialMaximal _) trace
  have living := (phaseApplication_live runtime leaks).history initial horizon selected (by
    intro state supported
    rw [initial, PMF.mem_support_pure_iff] at supported
    subst state
    exact ⟨PhaseRuntimeState.initial_frontier plan _, PhaseRuntimeState.initial_live plan _⟩)
      trace
  exact ⟨quiet.1, living.2, quiet.2.1, quiet.2.2⟩


/-- Every unfinished event in either actual independent phase is ready. -/
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
  · have bound := (RuntimePhase.mem_events commitmentPhase event).mp inside
    change 0 ≤ event.val ∧ event.val < 3 at bound
    let owner : Player := ⟨event.val, bound.2⟩
    have named : event = bindingEvent owner := Fin.ext rfl
    rw [named, binding_predecessors] at member
    exact (Finset.notMem_empty _ member).elim
  · have bound := (RuntimePhase.mem_events publicationPhase event).mp inside
    change 3 ≤ event.val ∧ event.val < 6 at bound
    let owner : Player := ⟨event.val - 3, by omega⟩
    have named : event = revealEvent owner := by apply Fin.ext; change _ = event.val - 3 + 3; omega
    rw [named] at member
    exact (reveal_predecessors owner predecessor).mp member

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
  split_ifs
  all_goals first
  | rfl
  | (split
     · rfl
     · exact pendingCommand_ticks _ _)

private theorem pollCommand_ticks (owner : Player) (seed wanted : Bool)
    (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (pollCommand owner seed wanted view) = 0 := by
  unfold pollCommand
  split
  · exact activateReady_ticks _ _ _
  · rfl

def originalTick (position : Nat) : Nat :=
  if position ∈ ({3, 4, 17, 24, 25, 26} : Finset Nat) then 1 else 0

theorem originalCommand_ticks (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks
        (originalCommand seeds position past view) = originalTick position := by
  match position with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
      18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
      simp only [originalCommand, originalTick, activateReady_ticks,
        pollCommand_ticks, earlyCommand_ticks, lateCommand_ticks]
      all_goals decide
  | n + 30 =>
      have different : n + 30 ∉ ({3, 4, 17, 24, 25, 26} : Finset Nat) := by
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

theorem originalClock_end : originalClock 30 = 6 := by decide

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
    rw [initial, PMF.mem_support_pure_iff] at supported
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
  have compiledTrace : (app.protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon (family seeds)).Trace (some current) := by
    change (app.protocol (((PMF.pure (Env.empty (CellVal simpleExpr))).map encodeInputs).map
      (PhaseRuntimeState.initial plan)) horizon (family seeds)).Trace (some current)
    rw [PMF.pure_map, PMF.pure_map]
    exact trace
  have past := PhaseSeedFreshness.namespacePast_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seeds) current compiledTrace
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

end Vegas.Examples.CommitSeedBroadcast

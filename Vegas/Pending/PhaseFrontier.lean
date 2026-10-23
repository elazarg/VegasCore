/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication

/-! # Exact semantic frontiers across automatic phase installation

The saved state is the lower rank prefix of the installed phase. Its live state
stays inside that interval. On closure the next phase saves the exact upper
prefix, including after exhausted excluded-owner rebuilds.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The semantic position represented by a remaining phase suffix. -/
def Positioned (phases : List (RuntimePhase graph)) (entry current : RecoveryState graph) : Prop :=
  match phases with
  | [] => current.native.config.cut.IsPrefix graph.order.eventCount
  | phase :: _ => entry.native.config.cut.IsPrefix phase.low ∧
      current.native.config.cut.Within phase.low phase.high

/-- The descriptor suffix remains an ordered partition of the unexecuted ranks. -/
structure Frontier (state : PhaseRuntimeState graph) : Prop where
  adjacent : state.phases.IsChain fun before after => before.high = after.low
  last : ∀ phase ∈ state.phases.getLast?, phase.high = graph.order.eventCount
  positioned : Positioned state.phases state.entry state.current

omit [DecidableEq Player] in
/-- Saving a completed phase puts its successor at exactly the correct entry cut. -/
theorem positioned_next (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (state : RecoveryState graph)
    (adjacent : (phase :: remaining).IsChain fun before after => before.high = after.low)
    (last : ∀ final ∈ (phase :: remaining).getLast?, final.high = graph.order.eventCount)
    (finished : state.native.config.cut.IsPrefix phase.high) :
    Frontier (⟨remaining, 0, state, state, []⟩ : PhaseRuntimeState graph) := by
  refine ⟨adjacent.tail, ?_, ?_⟩
  · cases remaining with
    | nil => simp only [List.getLast?_nil, Option.not_mem_none, false_implies, implies_true]
    | cons next tail => simpa only [List.getLast?_cons_cons] using last
  · cases remaining with
    | nil =>
        have ending := last phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
        simpa only [Positioned, ending] using finished
    | cons next tail =>
        have boundary := adjacent.rel_head? (y := next) (by simp)
        have entry : state.native.config.cut.IsPrefix next.low := by
          simpa only [boundary] using finished
        exact ⟨entry, entry.within next.nonempty.le⟩

/-- Automatic settlement preserves exact checkpoint frontiers. There is no
semantic write into a successor phase before its descriptor is installed. -/
theorem settle_frontier (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (valid : Frontier (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    Frontier (settle phases generation entry current retired) := by
  induction phases generalizing generation entry current retired with
  | nil => exact valid
  | cons phase remaining ih =>
      obtain ⟨adjacent, last, saved, within⟩ := valid
      have drainedWithin := phase.drain_within current within
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          have restoredWithin : (restore entry (phase.drain current)).native.config.cut.Within
              phase.low phase.high := saved.within phase.nonempty.le
          have rebuiltWithin := phase.drain_within (restore entry (phase.drain current))
            restoredWithin
          split
          · exact ⟨adjacent, last, saved, rebuiltWithin⟩
          · rename_i exhausted
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner member
              by_contra missing
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨member, missing⟩⟩
            have rebuiltFinished := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            have next := positioned_next phase remaining _ adjacent last
              (phase.finished_prefix _ rebuiltWithin rebuiltFinished)
            exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩
        · have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ drainedWithin finished)
          exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩
      · exact ⟨adjacent, last, saved, drainedWithin⟩

/-- The unnormalized compiled partition starts at the empty semantic prefix. -/
theorem initial_checkpoint_frontier (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    Frontier (⟨plan.phases, 0, ⟨State.initial inputs, ∅⟩,
      ⟨State.initial inputs, ∅⟩, []⟩ : PhaseRuntimeState graph) := by
  refine ⟨plan.adjacent, plan.last, ?_⟩
  cases phases : plan.phases with
  | nil =>
      have noEvents := plan.empty phases
      constructor
      · omega
      · intro event
        exact Fin.elim0 (noEvents ▸ event)
  | cons phase remaining =>
      have low := plan.first phase (by simp only [phases, List.head?_cons,
        Option.mem_some_iff])
      have atLow : (State.initial inputs).config.cut.IsPrefix phase.low := by
        constructor
        · omega
        · intro event
          simp only [State.initial, Config.initial, EventOrder.Cut.empty, Finset.notMem_empty,
            low, Nat.not_lt_zero]
      exact ⟨atLow, atLow.within phase.nonempty.le⟩

/-- The actual compiled partition starts at the true empty semantic prefix. -/
theorem initial_frontier (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).Frontier :=
  settle_frontier _ _ _ _ _ (initial_checkpoint_frontier plan inputs)

omit [DecidableEq Player] in
/-- A supported graph event below the active high frontier retains its interval. -/
theorem native_step_within (phase : RuntimePhase graph) (before after : State graph)
    (within : before.config.cut.Within phase.low phase.high) (event : graph.EventId)
    (inside : event ∈ phase.events) (ready : before.config.cut.Ready event)
    (action : graph.Action event) (supported : after.config ∈
      (before.config.step event ready action).support) :
    after.config.cut.Within phase.low phase.high := by
  rw [Config.step_cut _ _ _ _ _ supported]
  exact within.complete event ready ((phase.mem_events event).mp inside).2

omit [DecidableEq Player] in
/-- Successful packet authorization supplies an installed descriptor and its
event, before any native inclusion is evaluated. -/
theorem allows_event (state : PhaseRuntimeState graph) (call : Payload graph)
    (allowed : state.allows call = true) :
    ∃ phase ∈ state.phases.head?, ∃ event, call.event? graph = some event ∧
      event ∈ phase.events := by
  unfold allows at allowed
  cases head : state.phases.head? <;> cases named : call.event? graph <;>
    simp only [head, named, Bool.false_eq_true, decide_eq_true_eq] at allowed
  exact ⟨_, rfl, _, rfl, allowed⟩

/-- Native inclusion cannot cross the current phase boundary. -/
theorem handle_frontier (runtime : EventGraphRuntime graph) (state next : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph)) (valid : state.Frontier)
    (accepted : state.handle runtime message = some next) : next.Frontier := by
  unfold handle at accepted
  split at accepted
  · rename_i allowed
    obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
    obtain ⟨phase, member, event, named, inside⟩ := allows_event state _ authorized
    obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
      handle_config_mem_step runtime state.current.native native _ rawAccepted
    have same : actual = event := Option.some.inj (actualNamed.symm.trans named)
    subst actual
    cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons current remaining =>
        simp only [phases, List.head?_cons, Option.mem_some_iff] at member
        subst current
        apply settle_frontier
        refine ⟨?_, ?_, ?_⟩
        · simpa only [phases] using valid.adjacent
        · simpa only [phases] using valid.last
        have positioned := valid.positioned
        rw [phases] at positioned
        exact ⟨positioned.1, native_step_within phase _ _ positioned.2 event inside
          ready action supported⟩
  · cases accepted


omit [DecidableEq Player] in
/-- Native commands either retain the semantic configuration or complete a
single installed event by its original graph transition law. -/
theorem command_effect (runtime : EventGraphRuntime graph) (state : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph) (native : State graph)
    (allowed : state.commandAllowed command = true)
    (reached : native ∈ (environmentStep runtime state.current.native command).support) :
    native.config = state.current.native.config ∨
      ∃ phase ∈ state.phases.head?, ∃ event ∈ phase.events,
        ∃ (ready : state.current.native.config.cut.Ready event) (action : graph.Action event),
          native.config ∈ (state.current.native.config.step event ready action).support := by
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at reached
      subst native
      exact Or.inl rfl
  | executeSample event =>
      obtain ⟨_, same | ⟨ready, action, supported, _⟩⟩ :=
        environmentStep_executeSample_config_activated runtime state.current.native native
          event reached
      · exact Or.inl same.1
      · right
        cases head : state.phases.head? with
        | none => simp only [commandAllowed, head, Option.any_none, Bool.false_eq_true] at allowed
        | some phase =>
            have inside : event ∈ phase.events := by
              simpa only [commandAllowed, head, Option.any_some, decide_eq_true_eq] using allowed
            exact ⟨phase, rfl, event, inside, ready, action, supported⟩
  | expire event =>
      obtain ⟨_, same | ⟨ready, action, supported, _⟩⟩ :=
        environmentStep_expire_config_activated runtime state.current.native native event reached
      · exact Or.inl same.1
      · right
        cases head : state.phases.head? with
        | none => simp only [commandAllowed, head, Option.any_none, Bool.false_eq_true] at allowed
        | some phase =>
            have inside : event ∈ phase.events := by
              simpa only [commandAllowed, head, Option.any_some, decide_eq_true_eq] using allowed
            exact ⟨phase, rfl, event, inside, ready, action, supported⟩

omit [DecidableEq Player] in
/-- Changing physical metadata without changing the configuration retains its phase position. -/
theorem Frontier.copy_current {state : PhaseRuntimeState graph} (valid : state.Frontier)
    (current : RecoveryState graph) (same : current.native.config = state.current.native.config) :
    Frontier { state with current } := by
  refine ⟨valid.adjacent, valid.last, ?_⟩
  have positioned := valid.positioned
  cases phases : state.phases <;> simp only [Positioned, phases] at positioned ⊢
  · simpa only [same] using positioned
  · exact ⟨positioned.1, by simpa only [same] using positioned.2⟩

/-- Actual environment laws retain the exact saved entry and bounded live cut,
including commands which trigger rollback or several automatic phase advances. -/
theorem environment_frontier (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (command : EnvironmentCommand graph)
    (valid : state.Frontier) (reached : next ∈ (state.environment runtime command).support) :
    next.Frontier := by
  unfold environment at reached
  split at reached
  · rename_i allowed
    rw [PMF.support_map] at reached
    obtain ⟨native, rawReached, rfl⟩ := reached
    apply settle_frontier
    rcases command_effect runtime state command native allowed rawReached with same |
      ⟨phase, member, event, inside, ready, action, supported⟩
    · exact valid.copy_current _ same
    · cases phases : state.phases with
      | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
      | cons current remaining =>
          simp only [phases, List.head?_cons, Option.mem_some_iff] at member
          subst current
          refine ⟨?_, ?_, ?_⟩
          · simpa only [phases] using valid.adjacent
          · simpa only [phases] using valid.last
          have positioned := valid.positioned
          rw [phases] at positioned
          exact ⟨positioned.1, native_step_within phase _ _ positioned.2 event inside
            ready action supported⟩
  · rw [PMF.mem_support_pure_iff] at reached
    subst next
    exact valid

/-- Private preparations preserve the exact semantic checkpoint and live cut. -/
theorem submit_frontier (state : PhaseRuntimeState graph) (who : Player)
    (submission : WitnessedSubmission graph) (valid : state.Frontier) :
    (state.submit who submission).Frontier := by
  apply valid.copy_current
  change (submitStep _ who _).config = _
  rw [submitStep_config, (submission.call.register_facts who state.current.native).1]

/-- A genuine initialized runtime has both native metadata and exact phase frontiers. -/
theorem initial_invariant (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).Invariant inputs ∧ (initial plan inputs).Frontier :=
  ⟨settle_invariant _ _ _ _ _ (State.initial_invariant inputs) (State.initial_invariant inputs),
    initial_frontier plan inputs⟩

omit [DecidableEq Player] in
/-- When no descriptor remains, every original graph event is semantically complete. -/
theorem Frontier.terminal {state : PhaseRuntimeState graph} (valid : state.Frontier)
    (finished : state.phases = []) : state.current.native.config.cut.Terminal := by
  have positioned := valid.positioned
  rw [finished] at positioned
  change state.current.native.config.cut.completed = Finset.univ
  apply Finset.eq_univ_of_forall
  intro event
  exact (positioned.2 event).mpr event.isLt

end Vegas.EventGraphRuntime.PhaseRuntimeState

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every actual application transition preserves exact phase entry snapshots
and prohibits semantic completion beyond the currently installed phase. -/
theorem phaseApplication_frontier (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.Frontier where
  submit state who submission valid := state.submit_frontier who submission valid
  handle state message next valid accepted :=
    state.handle_frontier runtime next message valid accepted
  environment state command next valid reached :=
    state.environment_frontier runtime next command valid reached

/-- The actual physical clock cannot decrease across phase closure or rollback. -/
theorem phaseApplication_clock_monotone (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation
      (fun before after => before.current.native.clock ≤ after.current.native.clock) where
  refl _ := le_rfl
  submit state who submission := by
    have same := (submitStep_publicView
      (submission.call.register state.current.native who) who submission.call.packet).trans
        (submission.call.register_facts who state.current.native).2
    change state.current.native.clock ≤ (submitStep _ who _).clock
    have clockEq := congrArg PublicView.clock same
    change (submitStep (submission.call.register state.current.native who) who
      submission.call.packet).clock = state.current.native.clock at clockEq
    exact clockEq.symm.le
  handle state message next accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      change state.current.native.clock ≤
        (PhaseRuntimeState.settle _ _ _ _ _).current.native.clock
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.2]
      change state.current.native.clock ≤ native.clock
      exact (handle_clock_activated runtime state.current.native native _ handled).1.symm.le
    · cases accepted
  environment state command next reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, reached, rfl⟩ := reached
      change state.current.native.clock ≤
        (PhaseRuntimeState.settle _ _ _ _ _).current.native.clock
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.2]
      change state.current.native.clock ≤ native.clock
      rw [environmentStep_clock runtime state.current.native native command reached]
      exact Nat.le_add_right _ _
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact le_rfl

end Vegas.EventGraphRuntime

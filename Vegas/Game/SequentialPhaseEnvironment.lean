/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseSettlement
import Vegas.Game.SequentialPhaseExpiry
import Vegas.Pending.PhaseSingletonTransition
import Vegas.Pending.PhaseCheckpointExclusion
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhasePlanSuffix

/-! # The actual sequential singleton environment kernel

Phase bookkeeping projects to the forced-exit environment on the complete
physical current state. This says nothing about the extra archived observations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem expire_completed_native (runtime : EventGraphRuntime graph)
    (before native : State graph) (event : graph.EventId)
    (supported : native ∈ (environmentStep runtime before (.expire event)).support)
    (unfinished : event ∉ before.config.cut.completed)
    (completed : event ∈ native.config.cut.completed) :
    ∃ (ready : before.config.cut.Ready event) (entered : Nat),
      before.activatedAt event = some entered ∧
        runtime.deadline event ≤ before.clock - entered ∧
        native = before.completeFailure event ready := by
  by_cases ready : before.config.cut.Ready event
  · cases activated : before.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime before event ready activated,
          PMF.mem_support_pure_iff] at supported
        subst native
        exact (unfinished completed).elim
    | some entered =>
        by_cases due : runtime.deadline event ≤ before.clock - entered
        · cases view : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              refine ⟨ready, entered, rfl, due, ?_⟩
              rw [environmentStep_expire_bind_eq runtime before event ready entered activated due
                owner payload outputEq codeEq view, PMF.mem_support_pure_iff] at supported
              simpa only [State.completeFailure, view] using supported
          | resolve owner payload binding checks outputEq codeEq =>
              refine ⟨ready, entered, rfl, due, ?_⟩
              rw [environmentStep_expire_resolve_eq runtime before event ready entered activated due
                owner payload binding checks outputEq codeEq view,
                PMF.mem_support_pure_iff] at supported
              simpa only [State.completeFailure, view] using supported
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq runtime before event ready entered activated due
                payload law outputEq codeEq view, PMF.mem_support_pure_iff] at supported
              subst native
              exact (unfinished completed).elim
        · rw [environmentStep_expire_of_not_due runtime before event ready entered activated due,
            PMF.mem_support_pure_iff] at supported
          subst native
          exact (unfinished completed).elim
  · rw [environmentStep_expire_of_not_ready runtime before event ready,
      PMF.mem_support_pure_iff] at supported
    subst native
    exact (unfinished completed).elim

namespace PhaseRuntimeState

private theorem normalize_environment_current_sequential
    (runtime : EventGraphRuntime graph.sequentialize)
    (state : PhaseRuntimeState graph.sequentialize)
    {inputs : graph.sequentialize.Inputs} (valid : state.current.native.Invariant inputs)
    (frontier : state.Frontier) (live : state.Live) (stored : state.StoredCheckpoint)
    (history : state.HistoryCheckpoint) (accepted : state.AcceptedCheckpointFrame)
    (exclusions : state.ExclusionRecord)
    (singletons : ∀ phase ∈ state.phases, phase.high = phase.low + 1)
    (command : EnvironmentCommand graph.sequentialize) (native : State graph.sequentialize)
    (allowed : state.commandAllowed command = true)
    (supported : native ∈ (environmentStep runtime state.current.native command).support) :
    ({ state with current := state.current.environmentResult command native } :
      PhaseRuntimeState graph.sequentialize).normalize.current =
      (state.current.environmentResult command native).drain := by
  let after := state.current.environmentResult command native
  have nextFrontier := frontier.after_effect after
    (state.command_effect runtime command native allowed supported)
  cases phases : state.phases with
  | nil =>
      have terminal := frontier.terminal phases
      have afterTerminal : after.native.config.cut.Terminal := by
        apply Finset.eq_univ_of_forall
        intro event
        apply environmentStep_completed_subset runtime state.current.native native command supported
        rw [terminal]
        exact Finset.mem_univ _
      have clear : ∀ event, ¬ after.AutomaticReady event := by
        intro event eligible
        exact eligible.1.1 (by rw [afterTerminal]; exact Finset.mem_univ _)
      change (settle [] state.generation state.entry after state.retired).current = after.drain
      rw [settle, RecoveryState.drain_eq_of_clear _ clear]
  | cons phase remaining =>
      have head : state.phases.head? = some phase := by rw [phases]; rfl
      let event : graph.EventId := ⟨phase.low, lt_of_lt_of_le phase.nonempty phase.bounded⟩
      have only : phase.events = {event} :=
        phase.events_eq_singleton (singletons phase (by rw [phases]; exact List.mem_cons_self))
      have unfinished : event ∉ state.current.native.config.cut.completed := by
        intro completed
        apply live phase (by rw [head]; rfl)
        intro other inside
        have same := Finset.mem_singleton.mp ((Finset.ext_iff.mp only _).mp inside)
        exact same ▸ completed
      have aligned := state.checkpoint_eq_of_singleton_unfinished frontier stored history accepted
        phase head event only unfinished
      have sameExcluded := exclusions.excluded_eq_of_same_config phase head aligned.1
      have initialFrontier : Frontier (⟨phase :: remaining, state.generation, state.entry,
          state.current, state.retired⟩ : PhaseRuntimeState graph.sequentialize) := by
        rw [← phases]
        exact frontier
      change (settle (phase :: remaining) state.generation state.entry after
        state.retired).current = after.drain
      by_cases unchanged : after.excluded = state.current.excluded
      · simpa only [phases] using
          settle_current_eq_drain_sequential state.phases state.generation state.entry after
            state.retired (sameExcluded.trans unchanged.symm) nextFrontier
      · cases command with
        | advanceClock => exact (unchanged rfl).elim
        | executeSample actual => exact (unchanged rfl).elim
        | expire actual =>
            have newly : actual ∉ state.current.native.config.cut.completed ∧
                actual ∈ native.config.cut.completed := by
              by_contra absent
              apply unchanged
              change (if actual ∉ state.current.native.config.cut.completed ∧
                  actual ∈ native.config.cut.completed then
                RecoveryState.excludeEvent state.current.excluded actual else _) = _
              rw [ite_eq_right absent]
            obtain ⟨ready, entered, activated, due, nativeEq⟩ :=
              expire_completed_native runtime state.current.native native actual supported
                newly.1 newly.2
            have inside : actual ∈ phase.events := by
              apply of_decide_eq_true
              simpa only [commandAllowed, phases, List.head?_cons, Option.any_some] using allowed
            have same : actual = event :=
              Finset.mem_singleton.mp ((Finset.ext_iff.mp only _).mp inside)
            subst actual
            by_cases kind : phase.kind = .commitment
            · have field := phase.fields event ((phase.mem_events event).mp inside).1
                ((phase.mem_events event).mp inside).2
              rw [kind] at field
              obtain ⟨owner, payload, binding⟩ := field
              have owned : graph.sequentialize.actor? event = some owner :=
                graph.sequentialize.actor?_of_outputLayout_binding binding
              have inserted : after.excluded = insert owner state.current.excluded := by
                change (if event ∉ state.current.native.config.cut.completed ∧
                    event ∈ native.config.cut.completed then
                  RecoveryState.excludeEvent state.current.excluded event else _) = _
                rw [ite_eq_left newly]
                simp only [RecoveryState.excludeEvent]
                change graph.actor? event = some owner at owned
                rw [owned]
              have fresh : owner ∉ state.entry.excluded := by
                intro member
                apply unchanged
                rw [inserted, Finset.insert_eq_of_mem (sameExcluded ▸ member)]
              change (settle (phase :: remaining) state.generation state.entry after
                state.retired).current = after.drain
              dsimp only [after]
              rw [nativeEq]
              exact settle_expire_binding_current_eq_drain_sequential phase remaining
                state.generation state.entry state.current state.retired valid
                initialFrontier event only ready owned kind fresh
                aligned.1 aligned.2
            · change (settle (phase :: remaining) state.generation state.entry after
                state.retired).current = after.drain
              exact settle_current_noncommit_singleton_eq_drain_sequential phase remaining
                state.generation state.entry
                after state.retired (by simpa only [phases] using nextFrontier) event only
                newly.2 kind

omit [DecidableEq Player] in
private theorem ready_command_allowed_sequential (state : PhaseRuntimeState graph.sequentialize)
    (frontier : state.Frontier) (live : state.Live) (event : graph.EventId)
    (ready : state.current.native.config.cut.Ready event) :
    state.commandAllowed (.executeSample event) = true ∧
      state.commandAllowed (.expire event) = true := by
  cases phases : state.phases with
  | nil =>
      have terminal := frontier.terminal phases
      exact (ready.1 (by rw [terminal]; exact Finset.mem_univ _)).elim
  | cons phase remaining =>
      have position := frontier.positioned
      rw [phases] at position
      have head : phase ∈ state.phases.head? := by rw [phases]; rfl
      have inside :=
        phase.ready_mem_sequential state.current position.2 (live phase head) event ready
      simpa only [commandAllowed, phases, List.head?_cons, Option.any_some] using
        And.intro (decide_eq_true inside) (decide_eq_true inside)

/-- Every actual environment command has exactly the forced-exit kernel after
projecting the phase engine to its complete physical current state. -/
theorem environment_current_sequential
    (runtime : EventGraphRuntime graph.sequentialize)
    (state : PhaseRuntimeState graph.sequentialize)
    {inputs : graph.sequentialize.Inputs} (valid : state.current.native.Invariant inputs)
    (frontier : state.Frontier) (live : state.Live) (stored : state.StoredCheckpoint)
    (history : state.HistoryCheckpoint) (accepted : state.AcceptedCheckpointFrame)
    (exclusions : state.ExclusionRecord)
    (singletons : ∀ phase ∈ state.phases, phase.high = phase.low + 1)
    (quiescent : ∀ event, ¬ state.current.AutomaticReady event)
    (command : EnvironmentCommand graph.sequentialize) :
    (state.environment runtime command).map PhaseRuntimeState.current =
      state.current.environment runtime command := by
  cases allowed : state.commandAllowed command with
  | true =>
      simp only [environment, allowed, ↓reduceIte, RecoveryState.environment, PMF.map_comp]
      apply map_congr_on_support _
      intro native supported
      exact normalize_environment_current_sequential runtime state valid frontier live stored
        history accepted exclusions singletons command native allowed supported
  | false =>
      cases command with
      | advanceClock => simp only [commandAllowed, Bool.true_eq_false] at allowed
      | executeSample event =>
          have notReady : ¬ state.current.native.config.cut.Ready event := by
            intro ready
            have permitted := (ready_command_allowed_sequential state frontier live event ready).1
            rw [allowed] at permitted
            cases permitted
          have nativeLaw := environmentStep_executeSample_of_not_ready runtime state.current.native
            event notReady
          simp only [environment, allowed, Bool.false_eq_true, ↓reduceIte, PMF.pure_map,
            RecoveryState.environment,
            nativeLaw, PMF.pure_map]
          change PMF.pure state.current = PMF.pure state.current.drain
          rw [state.current.drain_eq_of_clear quiescent]
      | expire event =>
          have notReady : ¬ state.current.native.config.cut.Ready event := by
            intro ready
            have permitted := (ready_command_allowed_sequential state frontier live event ready).2
            rw [allowed] at permitted
            cases permitted
          have nativeLaw := environmentStep_expire_of_not_ready runtime state.current.native event
            notReady
          have same : state.current.environmentResult (.expire event) state.current.native =
              state.current := by
            have impossible : ¬ (event ∉ state.current.native.config.cut.completed ∧
                event ∈ state.current.native.config.cut.completed) := fun both => both.1 both.2
            simp only [RecoveryState.environmentResult, ite_eq_right impossible]
          simp only [environment, allowed, Bool.false_eq_true, ↓reduceIte, PMF.pure_map,
            RecoveryState.environment,
            nativeLaw, PMF.pure_map, same]
          rw [state.current.drain_eq_of_clear quiescent]

end PhaseRuntimeState

/-- Initialized actual sequential singleton histories satisfy the complete
physical kernel correspondence under arbitrary raw responses and schedulers. -/
theorem phase_environment_current_sequential_history
    (runtime : EventGraphRuntime graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph.sequentialize))
    (plan : RuntimePhasePlan graph.sequentialize)
    (singletons : ∀ phase ∈ plan.phases, phase.high = phase.low + 1)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (command : EnvironmentCommand graph.sequentialize) :
    (control.execution.application.environment runtime command).map PhaseRuntimeState.current =
      control.execution.application.current.environment runtime command := by
  let app := phaseApplication runtime leaks
  have invariant : app.Invariant (fun state => ∃ draw, state.Invariant draw) := {
    submit := by
      rintro state who submission ⟨draw, valid⟩
      exact ⟨draw,
        (phaseApplication_invariant runtime leaks draw).submit state who submission valid⟩
    handle := by
      rintro state message next ⟨draw, valid⟩ accepted
      exact ⟨draw, (phaseApplication_invariant runtime leaks draw).handle state message next valid
        accepted⟩
    environment := by
      rintro state command next ⟨draw, valid⟩ supported
      exact ⟨draw, (phaseApplication_invariant runtime leaks draw).environment state command next
        valid supported⟩ }
  obtain ⟨draw, valid⟩ := invariant.history _ _ _ (fun state supported => by
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨draw, (PhaseRuntimeState.initial_invariant plan draw).1⟩) trace
  have live := (phaseApplication_live runtime leaks).history _ _ _ (fun state supported => by
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨PhaseRuntimeState.initial_frontier plan draw, PhaseRuntimeState.initial_live plan draw⟩)
    trace
  have quiet := (phaseApplication_quiescent_sequential runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact phaseApplication_initial_quiescent_sequential plan draw) trace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler trace
  exact PhaseRuntimeState.environment_current_sequential runtime control.execution.application
    valid.active live.1 live.2
    (phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler trace)
    (phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler trace)
    (phaseAcceptedCheckpointFrame_history runtime leaks plan inputs horizon scheduler trace)
    (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler trace)
    (fun phase member => singletons phase (suffix.subset member)) quiet.2 command

end Vegas.EventGraphRuntime

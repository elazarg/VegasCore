/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.SequentialPhaseServiceSetup
import Vegas.Game.SequentialPhaseTransition
import Vegas.Pending.PhaseSeedClockEffects
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseFiniteNature
import Interaction.ReactiveRawRoundTrace
import Vegas.Game.ServiceRosterAsync
import Vegas.Game.OnePacketSwapFiberSum
import Vegas.Game.OnePacketRetention
import Vegas.Game.OnePacketPublicInitialSignal
import GameTheoryExtensions.Analysis.QuasilinearSettlement
import Vegas.Game.ProgramPayoffs

/-! # A private Boolean publication with a complete physical phase service

A four-command scheduler activates the owner, receipts its optional packet,
advances the clock and expires an unfinished publication. The service proofs
cover every raw response, including malformed submissions and silence.
The original private prior has two outcomes, and the source pays two for true.
-/

noncomputable section

namespace Vegas.Examples.SequentialPhaseService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Protocol GameTheory.Math.Probability

private theorem sole_phase : plan.phases = [sequentialRuntimePhaseAt program event] := by
  simp only [sequentialRuntimePhasePlan]
  rw [List.ofFn_succ]
  rfl

private theorem phase_kind : (sequentialRuntimePhaseAt program event).kind ≠ .commitment := by
  have fields := (sequentialRuntimePhaseAt program event).fields event (by decide) (by decide)
  change RuntimePhaseKind.Matches _ (.publication (L := simpleExpr) .bool) at fields
  cases kind : (sequentialRuntimePhaseAt program event).kind <;> simp_all [RuntimePhaseKind.Matches]

private theorem settle_progress {G : Vegas.EventGraph Player simpleExpr}
    (phases : List (RuntimePhase G))
    (noncommit : ∀ phase ∈ phases, phase.kind ≠ .commitment)
    (generation : Nat) (entry current : RecoveryState G)
    (retired : List (RetiredCommitAttempt G)) {inputs : G.Inputs}
    (valid : current.native.Invariant inputs) :
    State.ServiceProgress inputs 0 current.native
        (PhaseRuntimeState.settle phases generation entry current retired).current.native ∧
      (PhaseRuntimeState.settle phases generation entry current retired).generation =
        generation := by
  induction phases generalizing entry current with
  | nil => exact ⟨.refl valid, rfl⟩
  | cons phase remaining ih =>
      have kind := noncommit phase (by simp)
      have progress := phase.drain_progress current valid
      simp only [PhaseRuntimeState.settle]
      split
      · simp only [kind, false_and, ↓reduceIte]
        obtain ⟨later, generationEq⟩ := ih
          (fun other member => noncommit other (by simp [member]))
          (phase.drain current) (phase.drain current) progress.invariant
        exact ⟨by simpa only [Nat.zero_add] using progress.trans later, generationEq⟩
      · exact ⟨progress, rfl⟩

private def Safe (inputs : compiled.Inputs) (state : app.State) : Prop :=
  state.Invariant inputs ∧ state.Frontier ∧ state.phases <:+ plan.phases ∧ state.generation = 0

private theorem noncommit {state : app.State} (suffix : state.phases <:+ plan.phases) :
    ∀ phase ∈ state.phases, phase.kind ≠ .commitment := by
  intro phase member
  have inside := suffix.subset member
  rw [sole_phase, List.mem_singleton] at inside
  exact inside ▸ phase_kind

private theorem normalize_facts (state : app.State) {inputs : compiled.Inputs}
    (valid : state.current.native.Invariant inputs) (suffix : state.phases <:+ plan.phases) :
    State.ServiceProgress inputs 0 state.current.native state.normalize.current.native ∧
      state.normalize.generation = state.generation :=
  settle_progress _ (noncommit suffix) _ _ _ _ valid

private theorem safe_invariant (inputs : compiled.Inputs) : app.Invariant (Safe inputs) where
  submit state who submission valid :=
    ⟨(phaseApplication_invariant runtime leaks inputs).submit _ _ _ valid.1,
      (phaseApplication_frontier runtime leaks).submit _ _ _ valid.2.1,
      valid.2.2.1, valid.2.2.2⟩
  handle state message next valid accepted := by
    refine ⟨(phaseApplication_invariant runtime leaks inputs).handle _ _ _ valid.1 accepted,
      (phaseApplication_frontier runtime leaks).handle _ _ _ valid.2.1 accepted,
      (phaseApplication_planSuffix runtime leaks plan).handle _ _ _ valid.2.2.1 accepted, ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have nextValid := handle_invariant runtime _ _ _ valid.1.active handled
      exact (normalize_facts
        ({ state with
          current := state.current.inclusionResult message.payload.packet.call native } :
          app.State) nextValid valid.2.2.1).2.trans valid.2.2.2
    · cases accepted
  environment state command next valid reached := by
    refine ⟨(phaseApplication_invariant runtime leaks inputs).environment _ _ _ valid.1 reached,
      (phaseApplication_frontier runtime leaks).environment _ _ _ valid.2.1 reached,
      (phaseApplication_planSuffix runtime leaks plan).environment _ _ _ valid.2.2.1 reached, ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
      have nextValid := environmentStep_invariant runtime _ _ _ valid.1.active moved
      exact (normalize_facts
        ({ state with current := state.current.environmentResult command native } : app.State)
          nextValid valid.2.2.1).2.trans valid.2.2.2
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid.2.2.2

private theorem native_progress : app.StepRelation (fun before after =>
    ∀ inputs, Safe inputs before → ∃ ticks,
      State.ServiceProgress inputs ticks before.current.native after.current.native) where
  refl _ inputs valid := ⟨0, .refl valid.1.active⟩
  submit state who submission inputs valid :=
    ⟨0, state.submit_progress who submission valid.1.active⟩
  handle state message next accepted inputs valid := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have first := handle_progress runtime inputs state.current.native native
        ⟨message.id, message.payload.packet.call⟩ valid.1.active handled
      have second := (normalize_facts
        ({ state with
          current := state.current.inclusionResult message.payload.packet.call native } :
          app.State) first.invariant valid.2.2.1).1
      exact ⟨_, first.trans second⟩
    · cases accepted
  environment state command next reached inputs valid := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
      have first : State.ServiceProgress inputs command.clockTicks state.current.native native :=
        ⟨environmentStep_invariant runtime _ _ _ valid.1.active moved,
          environmentStep_completed_subset runtime _ _ _ moved,
          environmentStep_clock runtime _ _ _ moved,
          fun other entered activated unfinished => environmentStep_activatedAt_of_not_completed
            runtime _ _ _ valid.1.active moved other entered activated unfinished⟩
      have second := (normalize_facts
        ({ state with current := state.current.environmentResult command native } : app.State)
          first.invariant valid.2.2.1).1
      exact ⟨_, first.trans second⟩
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨0, .refl valid.1.active⟩

private theorem active_attempt (state : app.State) {inputs : compiled.Inputs}
    (valid : Safe inputs state) (unfinished : event ∉ state.current.native.config.cut.completed) :
    state.attempt = ⟨0, 0⟩ := by
  have suffix := valid.2.2.1
  rw [sole_phase] at suffix
  cases phases : state.phases with
  | nil =>
    have terminal := valid.2.1.terminal phases
    exact (unfinished (by rw [terminal]; exact Finset.mem_univ _)).elim
  | cons phase remaining =>
    have member := valid.2.2.1.subset (show phase ∈ state.phases by simp [phases])
    rw [sole_phase, List.mem_singleton] at member
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some, valid.2.2.2]
    rw [member]
    rfl

private theorem environmentRecall_append (before after : app.Execution) (operation : app.Command)
    (moved : after ∈ (before.environmentStep app operation).support) :
    after.environmentRecall = before.environmentRecall ++
      [⟨before.observeEnvironment app, operation⟩] := by
  obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ moved
  rfl

private def Fresh (execution : app.Execution) : Prop :=
  ∃ state ∈ initial.support, execution = ReactiveApplication.Execution.initial app state

private def Activated (execution : app.Execution) : Prop :=
  ∃ before, Fresh before ∧ execution ∈ (before.environmentStep app (.activate owner)).support

private def Responded (execution : app.Execution) : Prop :=
  ∃ before, Activated before ∧ ∃ response : app.Action,
    execution = before.respond app owner response

private def Included (execution : app.Execution) : Prop :=
  ∃ before, Responded before ∧
    execution ∈ (before.environmentStep app (.include (owner, 0))).support

private def Ticked (execution : app.Execution) : Prop :=
  ∃ before, Included before ∧
    execution ∈ (before.environmentStep app (.application .advanceClock)).support

private def Expired (execution : app.Execution) : Prop :=
  ∃ before, Ticked before ∧
    execution ∈ (before.environmentStep app (.application (.expire event))).support

private def Shape (control : app.Control) : Prop :=
  (control.remaining = 4 ∧ control.actor = none ∧ Fresh control.execution) ∨
  (control.remaining = 3 ∧ control.actor = some owner ∧ Activated control.execution) ∨
  (control.remaining = 3 ∧ control.actor = none ∧ Responded control.execution) ∨
  (control.remaining = 2 ∧ control.actor = none ∧ Included control.execution) ∨
  (control.remaining = 1 ∧ control.actor = none ∧ Ticked control.execution) ∨
  (control.remaining = 0 ∧ control.actor = none ∧ Expired control.execution)

private theorem fresh_length {execution : app.Execution} (fresh : Fresh execution) :
    execution.environmentRecall.length = 0 := by
  obtain ⟨state, _, rfl⟩ := fresh
  rfl

private theorem activated_length {execution : app.Execution} (active : Activated execution) :
    execution.environmentRecall.length = 1 := by
  obtain ⟨before, fresh, moved⟩ := active
  rw [environmentRecall_append _ _ _ moved, List.length_append, List.length_singleton,
    fresh_length fresh]

private theorem responded_length {execution : app.Execution} (responded : Responded execution) :
    execution.environmentRecall.length = 1 := by
  obtain ⟨before, active, response, rfl⟩ := responded
  rw [app.respond_environmentRecall]
  exact activated_length active

private theorem included_length {execution : app.Execution} (included : Included execution) :
    execution.environmentRecall.length = 2 := by
  obtain ⟨before, responded, moved⟩ := included
  rw [environmentRecall_append _ _ _ moved, List.length_append, List.length_singleton,
    responded_length responded]

private theorem ticked_length {execution : app.Execution} (ticked : Ticked execution) :
    execution.environmentRecall.length = 3 := by
  obtain ⟨before, included, moved⟩ := ticked
  rw [environmentRecall_append _ _ _ moved, List.length_append, List.length_singleton,
    included_length included]

private theorem expired_length {execution : app.Execution} (expired : Expired execution) :
    execution.environmentRecall.length = 4 := by
  obtain ⟨before, ticked, moved⟩ := expired
  rw [environmentRecall_append _ _ _ moved, List.length_append, List.length_singleton,
    ticked_length ticked]

private theorem environment_transition (remaining position : Nat) (execution : app.Execution)
    (length : execution.environmentRecall.length = position)
    (joint : Player → Option app.Action) (after : app.ProtocolState)
    (reached : after ∈ (app.transition initial horizon scheduler
      (some ⟨remaining + 1, none, execution⟩) joint).support) :
    ∃ next, after = some ⟨remaining, (command position).actor? app, next⟩ ∧
      next ∈ (execution.environmentStep app (command position)).support := by
  change after ∈ ((scheduler execution.environmentRecall
    (execution.observeEnvironment app)).bind _).support at reached
  rw [scheduler, length, PMF.pure_bind] at reached
  obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ reached
  exact ⟨next, rfl, moved⟩

private theorem shape_transition (control : app.Control) (after : app.ProtocolState)
    (shape : Shape control) (joint : Player → Option app.Action)
    (nonterminal : ¬ app.terminal (some control))
    (reached : after ∈ (app.transition initial horizon scheduler (some control) joint).support) :
    after.elim False Shape := by
  rcases control with ⟨remaining, actor, execution⟩
  rcases shape with fresh | activated | responded | included | ticked | expired
  · rcases fresh with ⟨rfl, rfl, fresh⟩
    obtain ⟨next, rfl, moved⟩ := environment_transition 3 0 execution
      (fresh_length fresh) joint after reached
    exact Or.inr (Or.inl ⟨rfl, rfl, execution, fresh, moved⟩)
  · rcases activated with ⟨rfl, rfl, activated⟩
    change after ∈ (PMF.pure (some ⟨3, none,
      execution.respond app owner ((joint owner).getD ⟨none⟩)⟩)).support at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, execution, activated, _, rfl⟩))
  · rcases responded with ⟨rfl, rfl, responded⟩
    obtain ⟨next, rfl, moved⟩ := environment_transition 2 1 execution
      (responded_length responded) joint after reached
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, execution, responded, moved⟩)))
  · rcases included with ⟨rfl, rfl, included⟩
    obtain ⟨next, rfl, moved⟩ := environment_transition 1 2 execution
      (included_length included) joint after reached
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, rfl, execution, included, moved⟩))))
  · rcases ticked with ⟨rfl, rfl, ticked⟩
    obtain ⟨next, rfl, moved⟩ := environment_transition 0 3 execution
      (ticked_length ticked) joint after reached
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, rfl, execution, ticked, moved⟩))))
  · exact (nonterminal ⟨expired.1, expired.2.1⟩).elim

private theorem shape_history {control : app.Control}
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) : Shape control := by
  have shapes : ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      state.elim True Shape := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
      change target ∈ (app.transition initial horizon scheduler source joint).support at reached
      cases source with
      | none =>
        obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
        exact Or.inl ⟨rfl, rfl, state, supported, rfl⟩
      | some current =>
        have result := shape_transition current target ih joint legal.1 reached
        cases target with
        | none => trivial
        | some next => exact result
  exact shapes trace

private def Good (execution : app.Execution) : Prop :=
  ∃ inputs, Safe inputs execution.application ∧
    (event ∉ execution.application.current.native.config.cut.completed →
      execution.application.current.native.activatedAt event = some 0)

private theorem fresh_good {execution : app.Execution} (fresh : Fresh execution) :
    Good execution ∧ execution.application.current.native.clock = 0 := by
  obtain ⟨state, supported, rfl⟩ := fresh
  obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ supported
  have current := PhaseRuntimeState.initial_current_sequential plan inputs
  have noCommit : ∀ phase ∈ plan.phases, phase.kind ≠ .commitment := by
    intro phase member
    rw [sole_phase, List.mem_singleton] at member
    exact member ▸ phase_kind
  have generation := (settle_progress plan.phases noCommit 0
    ⟨State.initial inputs, ∅⟩ ⟨State.initial inputs, ∅⟩ [] (State.initial_invariant inputs)).2
  refine ⟨⟨inputs, ⟨PhaseRuntimeState.initial_invariant plan inputs |>.1,
      PhaseRuntimeState.initial_frontier plan inputs,
      PhaseRuntimeState.settle_suffix .., generation⟩, ?_⟩, ?_⟩
  · change event ∉ (PhaseRuntimeState.initial plan inputs).current.native.config.cut.completed → _
    intro _
    change (PhaseRuntimeState.initial plan inputs).current.native.activatedAt event = some 0
    rw [current]
    simp only [State.initial, State.refreshActivated]
    have ready : (EventGraph.Config.initial inputs).cut.Ready event := by
      change event ∉ (∅ : Finset compiled.EventId) ∧
        (∅ : Finset compiled.EventId) ⊆ ∅
      exact ⟨by simp, Finset.Subset.refl _⟩
    rw [dite_eq_left ready]
    rfl
  · change (PhaseRuntimeState.initial plan inputs).current.native.clock = 0
    rw [current]
    rfl

private theorem good_environment {before after : app.Execution} (good : Good before)
    (operation : app.Command) (moved : after ∈ (before.environmentStep app operation).support) :
    Good after := by
  obtain ⟨inputs, valid, activated⟩ := good
  obtain ⟨ticks, progress⟩ :=
    native_progress.environmentStep before after operation moved inputs valid
  exact ⟨inputs, (safe_invariant inputs).environmentStep before after operation valid moved,
    fun unfinished => progress.activated event 0
      (activated (fun done => unfinished (progress.completed done))) unfinished⟩

private theorem good_respond {before : app.Execution} (good : Good before) (response : app.Action) :
    Good (before.respond app owner response) := by
  obtain ⟨inputs, valid, activated⟩ := good
  obtain ⟨ticks, progress⟩ := native_progress.respond before owner response inputs valid
  exact ⟨inputs, (safe_invariant inputs).respond before owner response valid,
    fun unfinished => progress.activated event 0
      (activated (fun done => unfinished (progress.completed done))) unfinished⟩

private theorem activated_good {execution : app.Execution} (active : Activated execution) :
    Good execution ∧ execution.application.current.native.clock = 0 := by
  obtain ⟨before, fresh, moved⟩ := active
  obtain ⟨good, clock⟩ := fresh_good fresh
  obtain ⟨inputs, valid, activated⟩ := good
  refine ⟨good_environment ⟨inputs, valid, activated⟩ _ moved, ?_⟩
  rw [PhaseSeedCalendar.environmentStep_clock runtime leaks before execution _ valid.1 moved,
    clock]
  rfl

private theorem responded_good {execution : app.Execution} (responded : Responded execution) :
    Good execution ∧ execution.application.current.native.clock = 0 := by
  obtain ⟨before, active, response, rfl⟩ := responded
  obtain ⟨good, clock⟩ := activated_good active
  obtain ⟨inputs, valid, activated⟩ := good
  refine ⟨good_respond ⟨inputs, valid, activated⟩ response, ?_⟩
  rw [PhaseSeedCalendar.respond_clock runtime leaks before valid.1 owner response, clock]

private theorem included_good {execution : app.Execution} (included : Included execution) :
    Good execution ∧ execution.application.current.native.clock = 0 := by
  obtain ⟨before, responded, moved⟩ := included
  obtain ⟨good, clock⟩ := responded_good responded
  obtain ⟨inputs, valid, activated⟩ := good
  refine ⟨good_environment ⟨inputs, valid, activated⟩ _ moved, ?_⟩
  rw [PhaseSeedCalendar.environmentStep_clock runtime leaks before execution _ valid.1 moved,
    clock]
  rfl

private theorem ticked_good {execution : app.Execution} (ticked : Ticked execution) :
    Good execution ∧ execution.application.current.native.clock = 1 := by
  obtain ⟨before, included, moved⟩ := ticked
  obtain ⟨good, clock⟩ := included_good included
  obtain ⟨inputs, valid, activated⟩ := good
  refine ⟨good_environment ⟨inputs, valid, activated⟩ _ moved, ?_⟩
  rw [PhaseSeedCalendar.environmentStep_clock runtime leaks before execution _ valid.1 moved,
    clock]
  rfl

private theorem expired_good {execution : app.Execution} (expired : Expired execution) :
    Good execution ∧ execution.application.current.native.clock = 1 := by
  obtain ⟨before, ticked, moved⟩ := expired
  obtain ⟨good, clock⟩ := ticked_good ticked
  obtain ⟨inputs, valid, activated⟩ := good
  refine ⟨good_environment ⟨inputs, valid, activated⟩ _ moved, ?_⟩
  rw [PhaseSeedCalendar.environmentStep_clock runtime leaks before execution _ valid.1 moved,
    clock]
  rfl

private theorem ready_of_unfinished (state : EventGraphRuntime.State compiled)
    (unfinished : event ∉ state.config.cut.completed) : state.config.cut.Ready event :=
  ⟨unfinished, by change ∅ ⊆ state.config.cut.completed; exact Finset.empty_subset _⟩

private theorem terminal_of_done (state : EventGraphRuntime.State compiled)
    (done : event ∈ state.config.cut.completed) : state.config.cut.Terminal := by
  apply Finset.eq_univ_of_forall
  intro other
  have bound : other.val < 1 := other.isLt
  have same : other = event := Fin.ext (by change other.val = 0; omega)
  exact same ▸ done

private theorem expired_terminal {execution : app.Execution} (expired : Expired execution) :
    execution.application.current.native.config.cut.Terminal := by
  obtain ⟨before, ticked, moved⟩ := expired
  obtain ⟨⟨inputs, valid, activated⟩, clock⟩ := ticked_good ticked
  obtain ⟨_, progress⟩ := native_progress.environmentStep before execution _ moved inputs valid
  by_cases done : event ∈ before.application.current.native.config.cut.completed
  · exact terminal_of_done _ (progress.completed done)
  · have suffix := valid.2.2.1
    have phasePresent : ∃ phase ∈ before.application.phases.head?, event ∈ phase.events := by
      cases phases : before.application.phases with
      | nil =>
        have terminal := valid.2.1.terminal phases
        exact (done (by rw [terminal]; exact Finset.mem_univ _)).elim
      | cons phase remaining =>
        have member := suffix.subset (show phase ∈ before.application.phases by simp [phases])
        rw [sole_phase, List.mem_singleton] at member
        refine ⟨phase, by simp, ?_⟩
        rw [member, sequentialRuntimePhaseAt_events]
        exact Finset.mem_singleton_self _
    have allowed : before.application.commandAllowed (.expire event) = true := by
      obtain ⟨phase, member, inside⟩ := phasePresent
      simp only [PhaseRuntimeState.commandAllowed, Option.any_eq_true]
      exact ⟨phase, member, decide_eq_true inside⟩
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at moved
    obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ moved
    change state ∈ (before.application.environment runtime (.expire event)).support at supported
    rw [PhaseRuntimeState.environment, ite_eq_left allowed, PMF.support_map] at supported
    obtain ⟨native, nativeMoved, rfl⟩ := supported
    have completed := environmentStep_expire_complete runtime before.application.current.native
      native event (ready_of_unfinished _ done) rfl 0 (activated done)
        (by rw [clock]) nativeMoved
    have normalized := (normalize_facts
      ({ before.application with current :=
        before.application.current.environmentResult (.expire event) native } : app.State)
      (environmentStep_invariant runtime _ _ _ valid.1.active nativeMoved) valid.2.2.1).1
    exact terminal_of_done _ (normalized.completed completed)

private theorem fresh_ready {execution : app.Execution} (fresh : Fresh execution) :
    execution.application.current.native.config.cut.Ready event := by
  obtain ⟨state, supported, rfl⟩ := fresh
  obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ supported
  change (PhaseRuntimeState.initial plan inputs).current.native.config.cut.Ready event
  rw [PhaseRuntimeState.initial_current_sequential plan inputs]
  change event ∉ (∅ : Finset compiled.EventId) ∧
    (∅ : Finset compiled.EventId) ⊆ ∅
  exact ⟨by simp, Finset.Subset.refl _⟩

private def RecordedActivation (execution : app.Execution) : Prop :=
  ∃ before, Fresh before ∧
    ⟨before.observeEnvironment app, (.activate owner : app.Command)⟩ ∈ execution.environmentRecall

private theorem activated_record {execution : app.Execution} (active : Activated execution) :
    RecordedActivation execution := by
  obtain ⟨before, fresh, moved⟩ := active
  refine ⟨before, fresh, ?_⟩
  rw [environmentRecall_append _ _ _ moved]
  exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem responded_record {execution : app.Execution} (responded : Responded execution) :
    RecordedActivation execution := by
  obtain ⟨before, active, response, rfl⟩ := responded
  simpa only [RecordedActivation, app.respond_environmentRecall] using activated_record active

private theorem record_environment {before after : app.Execution}
    (recorded : RecordedActivation before) (operation : app.Command)
    (moved : after ∈ (before.environmentStep app operation).support) :
    RecordedActivation after := by
  obtain ⟨original, fresh, member⟩ := recorded
  refine ⟨original, fresh, ?_⟩
  rw [environmentRecall_append _ _ _ moved]
  exact List.mem_append_left _ member

private theorem included_record {execution : app.Execution} (included : Included execution) :
    RecordedActivation execution := by
  obtain ⟨before, responded, moved⟩ := included
  exact record_environment (responded_record responded) _ moved

private theorem ticked_record {execution : app.Execution} (ticked : Ticked execution) :
    RecordedActivation execution := by
  obtain ⟨before, included, moved⟩ := ticked
  exact record_environment (included_record included) _ moved

private theorem opportunity_of_record {execution : app.Execution}
    (good : Good execution) (recorded : RecordedActivation execution) :
    PhaseService.OpportunityAt runtime leaks execution (fun _ => 0) := by
  intro requested actor entered acting ready activated _elapsed
  have same : requested = event := Fin.ext (by
    have bound : requested.val < 1 := requested.isLt
    change requested.val = 0
    omega)
  subst requested
  cases actor
  have unfinished := ((execution.application.current.native.publicView_eventReady event).mp ready).1
  obtain ⟨inputs, valid, timer⟩ := good
  have enteredEq : entered = 0 := Option.some.inj (activated.symm.trans (timer unfinished))
  subst entered
  obtain ⟨before, fresh, member⟩ := recorded
  obtain ⟨⟨originalInputs, originalValid, originalTimer⟩, _⟩ := fresh_good fresh
  have originalReady := fresh_ready fresh
  refine ⟨⟨before.observeEnvironment app, .activate owner⟩, member, rfl, ?_, ?_, ?_⟩
  · change before.application.attempt = execution.application.attempt
    rw [active_attempt _ originalValid originalReady.1, active_attempt _ valid unfinished]
  · exact (before.application.current.native.publicView_eventReady event).mpr originalReady
  · exact originalTimer originalReady.1

private theorem zero_clock_opportunity {execution : app.Execution}
    (clock : execution.application.current.native.clock = 0) :
    PhaseService.OpportunityAt runtime leaks execution (fun _ => 0) := by
  intro _ _ entered _ _ _ elapsed
  change entered + 0 < execution.application.current.native.clock at elapsed
  omega

private theorem activated_network_recall {execution : app.Execution}
    (active : Activated execution) :
    execution.network = .empty ∧ execution.recall owner = [] := by
  obtain ⟨before, ⟨state, _, rfl⟩, moved⟩ := active
  simp only [ReactiveApplication.Execution.environmentStep,
    show app.observePending = leaks from rfl, leaks, PMF.pure_map,
    MessageNetwork.learn_empty] at moved
  cases (PMF.mem_support_pure_iff _ _).mp moved
  exact ⟨rfl, rfl⟩

private theorem responded_emitted {execution : app.Execution} (responded : Responded execution)
    (entry : app.PlayerEntry) (member : entry ∈ execution.recall owner)
    (message : Message Player (CommitAttemptPacket compiled))
    (sent : entry.emitted = some message) :
    message.id = (owner, 0) ∧
      execution.network.lookup message.id = some message := by
  obtain ⟨before, active, ⟨transmission⟩, rfl⟩ := responded
  obtain ⟨network, pastEmpty⟩ := activated_network_recall active
  cases transmission with
  | none =>
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte, pastEmpty,
      List.nil_append, List.mem_singleton] at member
    subst entry
    cases sent
  | some submission =>
    simp only [ReactiveApplication.Execution.respond, network, MessageNetwork.submit,
      MessageNetwork.empty, ↓reduceIte, pastEmpty, List.nil_append, List.mem_singleton] at member
    subst entry
    cases Option.some.inj sent
    exact ⟨rfl, by simp [ReactiveApplication.Execution.respond, network, MessageNetwork.submit,
      MessageNetwork.empty, MessageNetwork.lookup]⟩

private def Receipted (execution : app.Execution) : Prop :=
  ∀ entry ∈ execution.recall owner, ∀ message, entry.emitted = some message →
    ∃ accepted, (message.id, accepted) ∈ execution.receipts

private theorem included_receipted {execution : app.Execution} (included : Included execution) :
    Receipted execution := by
  obtain ⟨before, responded, moved⟩ := included
  intro entry member message sent
  have sameRecall := app.environmentStep_recall before execution _ moved
  rw [sameRecall] at member
  obtain ⟨identified, found⟩ := responded_emitted responded entry member message sent
  rw [identified] at found
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
  cases (PMF.mem_support_pure_iff _ _).mp moved
  refine ⟨(before.application.handle runtime message).isSome, ?_⟩
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  rw [identified]
  exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem receipted_environment {before after : app.Execution}
    (receipted : Receipted before) (operation : app.Command)
    (moved : after ∈ (before.environmentStep app operation).support) : Receipted after := by
  intro entry member message sent
  rw [app.environmentStep_recall before after operation moved] at member
  obtain ⟨accepted, receipt⟩ := receipted entry member message sent
  exact ⟨accepted,
    (app.environmentStep_receipts_prefix before after operation moved).subset receipt⟩

private theorem ticked_receipted {execution : app.Execution} (ticked : Ticked execution) :
    Receipted execution := by
  obtain ⟨before, included, moved⟩ := ticked
  exact receipted_environment (included_receipted included) _ moved

private theorem expired_receipted {execution : app.Execution} (expired : Expired execution) :
    Receipted execution := by
  obtain ⟨before, ticked, moved⟩ := expired
  exact receipted_environment (ticked_receipted ticked) _ moved

private theorem inclusion_of_receipted {execution : app.Execution}
    (receipted : Receipted execution) :
    PhaseService.ProtectedInclusionAt runtime leaks execution (fun _ => 0) := by
  intro _ actor _ earlier later entry message split sent _ _ _ _ _ _ _ _
  cases actor
  exact receipted entry (by rw [split]; simp) message sent

private theorem empty_recall_receipted {execution : app.Execution}
    (pastEmpty : execution.recall owner = []) : Receipted execution := by
  intro entry member
  rw [pastEmpty] at member
  cases member

private theorem responded_entry_clock {execution : app.Execution}
    (responded : Responded execution) (entry : app.PlayerEntry)
    (member : entry ∈ execution.recall owner) :
    entry.beforeView.application.1.publicView.clock = 0 := by
  obtain ⟨before, active, ⟨transmission⟩, rfl⟩ := responded
  have pastEmpty := (activated_network_recall active).2
  have clock := (activated_good active).2
  cases transmission <;>
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte, pastEmpty,
      List.nil_append, List.mem_singleton] at member <;>
    subst entry <;> exact clock

private theorem responded_inclusion {execution : app.Execution}
    (responded : Responded execution) :
    PhaseService.ProtectedInclusionAt runtime leaks execution (fun _ => 0) := by
  intro _ actor _ earlier later entry _ split _ _ _ _ _ _ _ _ elapsed
  cases actor
  have clock := (responded_good responded).2
  have entryClock := responded_entry_clock responded entry (by rw [split]; simp)
  change entry.beforeView.application.1.publicView.clock + 0 <
    execution.application.current.native.clock at elapsed
  omega

theorem opportunity : PhaseService.Opportunity runtime leaks initial horizon scheduler
    (fun _ => 0) := by
  intro control trace
  rcases shape_history trace with fresh | active | responded | included | ticked | expired
  · exact zero_clock_opportunity (fresh_good fresh.2.2).2
  · exact zero_clock_opportunity (activated_good active.2.2).2
  · exact zero_clock_opportunity (responded_good responded.2.2).2
  · exact zero_clock_opportunity (included_good included.2.2).2
  · exact opportunity_of_record (ticked_good ticked.2.2).1 (ticked_record ticked.2.2)
  · intro requested _ _ _ ready _ _
    have terminal := expired_terminal expired.2.2
    have unfinished :=
      ((control.execution.application.current.native.publicView_eventReady requested).mp ready).1
    exact (unfinished (by rw [terminal]; exact Finset.mem_univ _)).elim

theorem protectedInclusion : PhaseService.ProtectedInclusion runtime leaks initial horizon scheduler
    (fun _ => 0) := by
  intro control trace
  rcases shape_history trace with fresh | active | responded | included | ticked | expired
  · obtain ⟨state, _, same⟩ := fresh.2.2
    exact inclusion_of_receipted (empty_recall_receipted (by rw [same]; rfl))
  · exact inclusion_of_receipted (empty_recall_receipted
      (activated_network_recall active.2.2).2)
  · exact responded_inclusion responded.2.2
  · exact inclusion_of_receipted (included_receipted included.2.2)
  · exact inclusion_of_receipted (ticked_receipted ticked.2.2)
  · exact inclusion_of_receipted (expired_receipted expired.2.2)

theorem completesPlay : PhaseService.CompletesPlay runtime leaks initial horizon scheduler := by
  intro control trace terminal
  have exhausted := terminal.1
  rcases shape_history trace with fresh | active | responded | included | ticked | expired
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact expired_terminal expired.2.2

theorem timely : runtime.AsyncTimely (fun _ => 0) (fun _ => 0) := by
  intro requested _
  change 0 + 0 < requested.val + 1
  omega

theorem physical_contract : PhaseService.AsyncContract runtime leaks initial horizon scheduler
    (fun _ => 0) (fun _ => 0) := ⟨opportunity, protectedInclusion, completesPlay⟩

def bounds : MessageBounds compiled where
  candidateCount := 1
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

theorem outputValues : bounds.CoversOutputValues := by
  intro requested
  have bound : requested.val < 1 := requested.isLt
  have same : requested = event := Fin.ext (by change requested.val = 0; omega)
  subst requested
  change ∀ bit : Bool, (⟨.bool, bit⟩ : Raw simpleExpr) ∈ bounds.values
  intro bit
  exact Finset.mem_image.mpr ⟨bit, Finset.mem_univ _, rfl⟩

theorem inputValues : bounds.CoversInputValues := by
  intro input actor payload layout
  change Fin 1 at input
  fin_cases input
  change (.binding owner .bool : EventField Player simpleExpr) = .binding actor payload at layout
  cases layout
  intro bit
  exact Finset.mem_image.mpr ⟨bit, Finset.mem_univ _, rfl⟩

theorem candidateCapacity : ∀ who, bindingEventCount compiled who < bounds.candidateCount := by
  intro who
  cases who
  decide

def outcome (bit : Bool) : PublicOutcome program :=
  Env.cons (.success bit) (Env.empty _)

theorem nonconstant_payment :
    transferAmount (program.publicPayoffs (outcome true)) owner = 2 ∧
      transferAmount (program.publicPayoffs (outcome false)) owner = 0 := by
  decide

theorem terminal_execution_exists : ∃ control : app.Control,
    Nonempty ((app.protocol initial horizon scheduler).Trace (some control)) ∧
      app.terminal (some control) ∧
        control.execution.application.current.native.config.cut.Terminal := by
  obtain ⟨execution, supported⟩ :=
    (app.roundsFrom initial scheduler (fun _ => app.silentPolicy) horizon).support_nonempty
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom initial horizon scheduler
    (fun _ => app.silentPolicy) horizon (Nat.le_refl _) execution supported
  refine ⟨⟨0, none, execution⟩, ?_, ⟨rfl, rfl⟩, ?_⟩
  · exact ⟨by simpa only [Nat.sub_self] using trace⟩
  · exact completesPlay _ (by simpa only [Nat.sub_self] using trace) ⟨rfl, rfl⟩

instance : Finite setup.intendedProtocol.History :=
  setup.intended_finite_history (by trivial)

def signal (_state : State simpleExpr context) : Unit := ()

private theorem splice_eq (who : Player) (mine others : State simpleExpr context) :
    splice who mine others = mine := by
  cases who
  funext name kind member
  cases member with
  | here => rfl
  | there absent => nomatch absent

theorem independent : setup.PrivateInputsIndependentGiven signal := by
  intro who first second _
  rw [splice_eq, splice_eq]

theorem observable : setup.PublicInitialSignal signal := by
  intro _ _ _
  rfl

theorem wellFormed : setup.WellFormed where
  initialValues initial supported := by
    obtain ⟨bit, _, rfl⟩ := PMF.support_map .. ▸ supported
    intro name actor payload cell
    cases cell with
    | here => exact ⟨bit, rfl⟩
    | there absent => nomatch absent
  guardsSatisfiable _ _ := trivial

def initialState (bit : Bool) : app.State :=
  PhaseRuntimeState.initial plan (setup.eventInputs (sourceInitial bit))

theorem initialState_supported (bit : Bool) : initialState bit ∈ initial.support := by
  rw [initial, PMF.support_map, PMF.support_map]
  refine ⟨setup.eventInputs (sourceInitial bit), ?_, rfl⟩
  refine ⟨sourceInitial bit, ?_, rfl⟩
  change sourceInitial bit ∈ ((PMF.uniformOfFintype Bool).map sourceInitial).support
  rw [PMF.support_map]
  exact ⟨bit, by simp, rfl⟩

theorem owner_decision_exists (bit : Bool) : ∃ control : app.Control,
    Nonempty ((app.protocol initial horizon scheduler).Trace (some control)) ∧
      control.actor = some owner ∧
        control.execution.application = initialState bit ∧
          control.execution.application.current.native.config.cut.Ready event := by
  let starting := ReactiveApplication.Execution.initial app (initialState bit)
  have fresh : Fresh starting := ⟨initialState bit, initialState_supported bit, rfl⟩
  have zeroSupport : starting ∈
      (app.roundsFrom initial scheduler (fun _ => app.silentPolicy) 0).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨initialState bit, initialState_supported bit, ?_⟩
    simp only [ReactiveApplication.runRounds, PMF.mem_support_pure_iff]
    rfl
  obtain ⟨started⟩ := app.raw_trace_roundsFrom initial horizon scheduler
    (fun _ => app.silentPolicy) 0 (Nat.zero_le _) starting zeroSupport
  obtain ⟨execution, moved⟩ := (starting.environmentStep app (.activate owner)).support_nonempty
  obtain ⟨activated⟩ := app.raw_trace_environment initial horizon scheduler 3 starting execution
    (.activate owner) started
    (by change _ ∈ (PMF.pure (.activate owner : app.Command)).support; simp) moved
  refine ⟨⟨3, some owner, execution⟩, ⟨activated⟩, rfl, ?_, ?_⟩
  all_goals
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at moved
    obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ moved
  · rfl
  · change starting.application.current.native.config.cut.Ready event
    exact fresh_ready fresh

end Vegas.Examples.SequentialPhaseService

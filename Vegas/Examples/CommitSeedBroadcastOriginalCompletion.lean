/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastService
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseServiceRounds
import Vegas.Pending.PhaseExpiryExclusion
import Vegas.Pending.PhaseBindingReceiptResolution
import Interaction.ReactiveReceiptBoundary
import Interaction.ReactiveRawRoundTrace

/-! # Physical completion and receipt laws of the private-seed scheduler -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

private theorem original_of_namespace_bounds (before after : CommitAttemptId)
    (progress : before.generation ≤ after.generation ∧ before.phase ≤ after.phase)
    (original : after = originalAttempt) : before = originalAttempt := by
  rw [original] at progress
  rcases before with ⟨phase, generation⟩
  change generation ≤ 0 ∧ phase ≤ 0 at progress
  have generations : generation = 0 := by omega
  have phases : phase = 0 := by omega
  subst generation
  subst phase
  rfl

/-- Every raw prefix still in the first full attempt has monotone native
completion and retains the original ready timers. Player responses are
unrestricted; no count-clean or intended-play premise is used. -/
theorem original_service_progress (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) :
    ∃ ticks, EventGraphRuntime.State.ServiceProgress originalInput ticks
      initialState.current.native current.execution.application.current.native := by
  let predicate : app.Execution → Prop := fun execution =>
    execution.application.Invariant originalInput ∧ execution.application.Ordered ∧
      (execution.application.attempt = originalAttempt →
        ∃ ticks, EventGraphRuntime.State.ServiceProgress originalInput ticks
          initialState.current.native execution.application.current.native)
  have invariant : app.ServiceInvariant selected predicate := by
    constructor
    · intro execution owner action valid
      have afterValid := (phaseApplication_invariant runtime leaks originalInput).respond
        execution owner action valid.1
      have ordered := (phaseApplication_seedOrder runtime leaks).respond
        execution owner action valid.2.1
      refine ⟨afterValid, ordered, ?_⟩
      intro afterOriginal
      have namespaceProgress := (phaseApplication_namespace_progress runtime leaks).respond
        execution owner action valid.2.1
      have beforeOriginal := original_of_namespace_bounds _ _ namespaceProgress afterOriginal
      have same := beforeOriginal.trans afterOriginal.symm
      obtain ⟨priorTicks, priorProgress⟩ := valid.2.2 beforeOriginal
      obtain ⟨nextTicks, nextProgress⟩ := (phaseApplication_serviceProgress runtime leaks).respond
        execution owner action originalInput valid.1 valid.2.1 same
      exact ⟨priorTicks + nextTicks, priorProgress.trans nextProgress⟩
    · intro execution next command valid _selected reached
      have afterValid := (phaseApplication_invariant runtime leaks originalInput).environmentStep
        execution next command valid.1 reached
      have ordered := (phaseApplication_seedOrder runtime leaks).environmentStep
        execution next command valid.2.1 reached
      refine ⟨afterValid, ordered, ?_⟩
      intro afterOriginal
      have namespaceProgress := (phaseApplication_namespace_progress runtime leaks).environmentStep
        execution next command reached valid.2.1
      have beforeOriginal := original_of_namespace_bounds _ _ namespaceProgress afterOriginal
      have same := beforeOriginal.trans afterOriginal.symm
      obtain ⟨priorTicks, priorProgress⟩ := valid.2.2 beforeOriginal
      obtain ⟨nextTicks, nextProgress⟩ :=
        (phaseApplication_serviceProgress runtime leaks).environmentStep execution next command
          reached originalInput valid.1 valid.2.1 same
      exact ⟨priorTicks + nextTicks, priorProgress.trans nextProgress⟩
  have started : ∀ state ∈ initial.support,
      predicate (ReactiveApplication.Execution.initial app state) := by
    intro state supported
    rw [initial, PMF.mem_support_pure_iff] at supported
    subst state
    exact ⟨(PhaseRuntimeState.initial_invariant plan originalInput).1,
      PhaseRuntimeState.initial_ordered plan originalInput,
      fun _ => ⟨0, .refl (PhaseRuntimeState.initial_invariant plan originalInput).1.active⟩⟩
  exact (invariant.history initial horizon started trace).2.2 original

private theorem original_initial_timer (owner : Player) :
    initialState.current.native.activatedAt (bindingEvent owner) = some 0 := by
  rw [initialState_eq]
  change EventGraphRuntime.State.refreshActivated
    (Config.initial originalInput) 0 (fun _ => none) (bindingEvent owner) = some 0
  have ready : (Config.initial originalInput).cut.Ready (bindingEvent owner) := by
    constructor
    · exact Finset.notMem_empty _
    · rw [binding_predecessors]
      exact Finset.empty_subset _
  unfold EventGraphRuntime.State.refreshActivated
  rw [dite_eq_left ready]
  rw [binding_actor]
  rfl

theorem original_timer (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) (owner : Player)
    (unfinished : bindingEvent owner ∉
      current.execution.application.current.native.config.cut.completed) :
    current.execution.application.current.native.activatedAt (bindingEvent owner) = some 0 := by
  obtain ⟨_ticks, progress⟩ := original_service_progress selected current trace original
  exact progress.activated (bindingEvent owner) 0 (original_initial_timer owner) unfinished

theorem original_phases (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) :
    current.execution.application.phases = [commitmentPhase, publicationPhase] := by
  have compiledTrace : (app.protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon selected).Trace (some current) := by
    change (app.protocol (((PMF.pure (Env.empty (CellVal simpleExpr))).map encodeInputs).map
      (PhaseRuntimeState.initial plan)) horizon selected).Trace (some current)
    rw [PMF.pure_map, PMF.pure_map]
    exact trace
  have suffix := phasePlanSuffix_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon selected compiledTrace
  rw [plan_phases] at suffix
  rcases List.suffix_cons_iff.mp suffix with same | suffix
  · exact same
  · rcases List.suffix_cons_iff.mp suffix with same | suffix
    · have impossible := congrArg CommitAttemptId.phase original
      change (current.execution.application.phases.head?.map RuntimePhase.low).getD
        graph.order.eventCount = 0 at impossible
      rw [same] at impossible
      change 3 = 0 at impossible
      omega
    · have empty := List.suffix_nil.mp suffix
      have impossible := congrArg CommitAttemptId.phase original
      change (current.execution.application.phases.head?.map RuntimePhase.low).getD
        graph.order.eventCount = 0 at impossible
      rw [empty] at impossible
      change 6 = 0 at impossible
      omega

theorem original_expiry_clock (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) (owner : Player)
    (position : current.execution.environmentRecall.length = 27 + owner.val) :
    current.execution.application.current.native.clock = 6 := by
  rw [original_clock_index seeds current trace original, position]
  fin_cases owner <;> decide

theorem original_expiry_resolves (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) (owner : Player)
    (position : current.execution.environmentRecall.length = 27 + owner.val)
    (next : app.Execution)
    (reached : next ∈ (current.execution.environmentStep app
      (.application (.expire (bindingEvent owner)))).support) :
    (originalCoordinate owner).Resolved next.application := by
  have valid := raw_native_valid (family seeds) current trace
  have geometry := raw_phase_geometry (family seeds) current trace
  have ordered : current.execution.application.Ordered := geometry.1.adjacent
  by_cases done : bindingEvent owner ∈
      current.execution.application.current.native.config.cut.completed
  · exact (phaseApplication_resolution runtime leaks (originalCoordinate owner)).environmentStep
      current.execution next (.application (.expire (bindingEvent owner))) reached originalInput
        valid ordered (Or.inr (Or.inr ⟨original.symm, done⟩))
  · have phases := original_phases (family seeds) current trace original
    have installed : current.execution.application.phases.head? = some commitmentPhase := by
      rw [phases]
      rfl
    have inside : bindingEvent owner ∈ commitmentPhase.events := by
      apply (RuntimePhase.mem_events commitmentPhase _).mpr
      exact ⟨Nat.zero_le _, owner.isLt⟩
    have request := raw_phase_event_request (family seeds) current trace commitmentPhase
      installed (Or.inl rfl) (bindingEvent owner) inside owner (binding_actor owner) done
    have timer := original_timer (family seeds) current trace original owner done
    have clock := original_expiry_clock seeds current trace original owner position
    have moved : next.application ∈ (current.execution.application.environment runtime
        (.expire (bindingEvent owner))).support := by
      have applicationReached := reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
        at applicationReached
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ applicationReached
      exact supported
    have resolved := current.execution.application.expire_resolves_of_request runtime
      next.application valid ordered request (by
        rw [timer, Option.getD_some, clock]
        change 6 ≤ 6 - 0
        decide) moved
    rw [original] at resolved
    exact CommitAttemptEvent.Resolved.of_step (originalCoordinate owner)
      current.execution.application next.application original.symm
      ((phaseApplication_namespace_progress runtime leaks).environmentStep current.execution next
        (.application (.expire (bindingEvent owner))) reached ordered) resolved

private theorem original_resolved_when_retired (state : PhaseRuntimeState graph)
    (retired : state.attempt ≠ originalAttempt) (event : graph.EventId) :
    (⟨originalAttempt, event⟩ : CommitAttemptEvent graph).Resolved state := by
  by_cases generation : 0 < state.attempt.generation
  · exact Or.inl generation
  by_cases phase : 0 < state.attempt.phase
  · exact Or.inr (Or.inl phase)
  apply False.elim
  apply retired
  cases address : state.attempt with
  | mk phaseValue generationValue =>
      simp only [address] at generation phase
      have generations : generationValue = 0 := by omega
      have phases : phaseValue = 0 := by omega
      simp only [generations, phases, originalAttempt]

private theorem original_expired_history (seeds : Seeds) (owner : Player) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current =>
        28 + owner.val ≤ current.execution.environmentRecall.length →
          (originalCoordinate owner).Resolved current.execution.application) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          change 28 + owner.val ≤ 0 → _
          intro impossible
          omega
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          have valid := raw_native_valid (family seeds) ⟨remaining, active, execution⟩ prior
          have geometry := raw_phase_geometry (family seeds) ⟨remaining, active, execution⟩ prior
          have ordered : execution.application.Ordered := geometry.1.adjacent
          change 28 + owner.val ≤ execution.environmentRecall.length → _ at ih
          cases active with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              change 28 + owner.val ≤
                (execution.respond app who ((joint who).getD ⟨none⟩)).environmentRecall.length → _
              intro enough
              rw [app.respond_environmentRecall] at enough
              exact (phaseApplication_resolution runtime leaks (originalCoordinate owner)).respond
                execution who ((joint who).getD ⟨none⟩) originalInput valid ordered (ih enough)
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  change 28 + owner.val ≤ next.environmentRecall.length → _
                  intro enough
                  have length := app.environmentStep_environmentRecall execution next command
                    supported
                  have counts : next.environmentRecall.length =
                      execution.environmentRecall.length + 1 := by
                    rw [length, List.length_append, List.length_singleton]
                  by_cases earlier : 28 + owner.val ≤ execution.environmentRecall.length
                  · exact (phaseApplication_resolution runtime leaks
                      (originalCoordinate owner)).environmentStep execution next command supported
                        originalInput valid ordered (ih earlier)
                  · have index : execution.environmentRecall.length = 27 + owner.val := by omega
                    by_cases original : execution.application.attempt = originalAttempt
                    · have selectedEq : command = choose seeds execution.environmentRecall
                          (execution.observeEnvironment app) := by
                        exact (PMF.mem_support_pure_iff _ _).mp selected
                      have commandEq : command = .application (.expire (bindingEvent owner)) := by
                        rw [selectedEq, choose_original seeds execution.environmentRecall
                          (execution.observeEnvironment app) original, index]
                        fin_cases owner <;> rfl
                      rw [commandEq] at supported
                      exact original_expiry_resolves seeds ⟨remaining + 1, none, execution⟩ prior
                        original owner index next supported
                    · exact (phaseApplication_resolution runtime leaks
                        (originalCoordinate owner)).environmentStep execution next command supported
                          originalInput valid ordered (original_resolved_when_retired
                            execution.application original (bindingEvent owner))

/-- All original bindings have actually resolved by the thirtieth command,
under every legal raw player continuation. -/
theorem original_bindings_resolved (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (enough : 30 ≤ current.execution.environmentRecall.length) (owner : Player) :
    (originalCoordinate owner).Resolved current.execution.application := by
  have bound := owner.isLt
  exact original_expired_history seeds owner trace (by omega)

/-- The first namespace is retired by actual inclusion, expiry and normalization. -/
theorem original_attempt_retired (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (enough : 30 ≤ current.execution.environmentRecall.length) :
    current.execution.application.attempt ≠ originalAttempt := by
  intro original
  have completed (owner : Player) : bindingEvent owner ∈
      current.execution.application.current.native.config.cut.completed := by
    have resolved := original_bindings_resolved seeds current trace enough owner
    rcases resolved with generation | phase | ⟨_same, completed⟩
    · rw [original] at generation
      change 0 < 0 at generation
      omega
    · rw [original] at phase
      change 0 < 0 at phase
      omega
    · exact completed
  have geometry := raw_phase_geometry (family seeds) current trace
  have phases := original_phases (family seeds) current trace original
  apply geometry.2.1 commitmentPhase (by rw [phases]; rfl)
  intro event inside
  have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
  change 0 ≤ event.val ∧ event.val < 3 at interval
  let owner : Player := ⟨event.val, interval.2⟩
  have named : event = bindingEvent owner := Fin.ext rfl
  rw [named]
  exact completed owner

end Vegas.Examples.CommitSeedBroadcast

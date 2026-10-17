/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingService
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseServiceRounds
import Vegas.Pending.PhaseExpiryExclusion
import Vegas.Pending.PhaseBindingReceiptResolution
import Interaction.ReactiveReceiptBoundary
import Interaction.ReactiveRawRoundTrace

/-! # Physical completion and receipt laws of the private-seed scheduler -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

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
    rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
    subst state
    exact ⟨(PhaseRuntimeState.initial_invariant plan originalInput).1,
      PhaseRuntimeState.initial_ordered plan originalInput,
      fun _ => ⟨0, .refl (PhaseRuntimeState.initial_invariant plan originalInput).1.active⟩⟩
  exact (invariant.history initial horizon started trace).2.2 original

private theorem original_initial_timer (event : graph.EventId)
    (binding : event = aliceBinding ∨ event = bobBinding) :
    initialState.current.native.activatedAt event = some 0 := by
  rw [initialState_eq]
  change EventGraphRuntime.State.refreshActivated
    (Config.initial originalInput) 0 (fun _ => none) event = some 0
  have ready : (Config.initial originalInput).cut.Ready event := by
    constructor
    · exact Finset.notMem_empty event
    · rcases binding with rfl | rfl
      · rw [binding_predecessors.1]
        exact Finset.empty_subset _
      · rw [binding_predecessors.2]
        exact Finset.empty_subset _
  unfold EventGraphRuntime.State.refreshActivated
  rw [dite_eq_left ready]
  rcases binding with rfl | rfl <;> rfl

theorem original_timer (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (event : graph.EventId) (binding : event = aliceBinding ∨ event = bobBinding)
    (unfinished : event ∉ current.execution.application.current.native.config.cut.completed) :
    current.execution.application.current.native.activatedAt event = some 0 := by
  obtain ⟨_ticks, progress⟩ := original_service_progress selected current trace original
  exact progress.activated event 0 (original_initial_timer event binding) unfinished

/-- The first namespace cannot have skipped to the reveal descriptor or
silently installed another source interval. -/
theorem original_phases (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) :
    current.execution.application.phases = [commitmentPhase, publicationPhase] := by
  have suffix := phasePlanSuffix_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon selected trace
  rw [plan_phases] at suffix
  rcases List.suffix_cons_iff.mp suffix with same | suffix
  · exact same
  · rcases List.suffix_cons_iff.mp suffix with same | suffix
    · have impossible := congrArg CommitAttemptId.phase original
      change (current.execution.application.phases.head?.map RuntimePhase.low).getD
        graph.order.eventCount = 0 at impossible
      rw [same] at impossible
      change 2 = 0 at impossible
      omega
    · have empty := List.suffix_nil.mp suffix
      have impossible := congrArg CommitAttemptId.phase original
      change (current.execution.application.phases.head?.map RuntimePhase.low).getD
        graph.order.eventCount = 0 at impossible
      rw [empty] at impossible
      change 4 = 0 at impossible
      omega

/-- The two original expiry commands act at clock six, not at a clock reset
chosen by a later retry. -/
theorem original_expiry_clock (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (position : current.execution.environmentRecall.length = 20 ∨
      current.execution.environmentRecall.length = 21) :
    current.execution.application.current.native.clock = 6 := by
  rw [original_clock_index seeds current trace original]
  rcases position with position | position <;> rw [position] <;> decide

/-- Each actual original expiry resolves its own old coordinate, including
when that command itself triggers rollback or exhausted restoration. -/
theorem original_expiry_resolves (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (owner : Player) (event : graph.EventId)
    (binding : event = aliceBinding ∨ event = bobBinding)
    (actor : graph.actor? event = some owner)
    (position : current.execution.environmentRecall.length = 20 ∨
      current.execution.environmentRecall.length = 21)
    (next : app.Execution)
    (reached : next ∈
      (current.execution.environmentStep app (.application (.expire event))).support) :
    (⟨originalAttempt, event⟩ : CommitAttemptEvent graph).Resolved next.application := by
  have valid := raw_native_valid (family seeds) current trace
  have geometry := raw_phase_geometry (family seeds) current trace
  have ordered : current.execution.application.Ordered := geometry.1.adjacent
  by_cases done : event ∈ current.execution.application.current.native.config.cut.completed
  · exact (phaseApplication_resolution runtime leaks ⟨originalAttempt, event⟩).environmentStep
      current.execution next (.application (.expire event)) reached originalInput valid ordered
        (Or.inr (Or.inr ⟨original.symm, done⟩))
  · have phases := original_phases (family seeds) current trace original
    have installed : current.execution.application.phases.head? = some commitmentPhase := by
      rw [phases]
      rfl
    have inside : event ∈ commitmentPhase.events := by
      rcases binding with rfl | rfl <;> decide
    have request := raw_phase_event_request (family seeds) current trace commitmentPhase
      installed (Or.inl rfl) event inside owner actor done
    have timer := original_timer (family seeds) current trace original event binding done
    have clock := original_expiry_clock seeds current trace original position
    have moved : next.application ∈
        (current.execution.application.environment runtime (.expire event)).support := by
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
    exact CommitAttemptEvent.Resolved.of_step ⟨originalAttempt, event⟩
      current.execution.application next.application original.symm
      ((phaseApplication_namespace_progress runtime leaks).environmentStep current.execution next
        (.application (.expire event)) reached ordered) resolved

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

private theorem original_expired_history (seeds : Seeds) (owner : Player)
    (event : graph.EventId) (expiryPosition : Nat)
    (position : (event = aliceBinding ∧ expiryPosition = 20) ∨
      (event = bobBinding ∧ expiryPosition = 21))
    (actor : graph.actor? event = some owner) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current =>
        expiryPosition + 1 ≤ current.execution.environmentRecall.length →
          (⟨originalAttempt, event⟩ : CommitAttemptEvent graph).Resolved
            current.execution.application) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          change expiryPosition + 1 ≤ 0 → _
          intro impossible
          omega
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          have valid := raw_native_valid (family seeds) ⟨remaining, active, execution⟩ prior
          have geometry := raw_phase_geometry (family seeds) ⟨remaining, active, execution⟩ prior
          have ordered : execution.application.Ordered := geometry.1.adjacent
          change expiryPosition + 1 ≤ execution.environmentRecall.length → _ at ih
          cases active with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              change expiryPosition + 1 ≤
                (execution.respond app who ((joint who).getD ⟨none⟩)).environmentRecall.length → _
              intro enough
              rw [app.respond_environmentRecall] at enough
              exact (phaseApplication_resolution runtime leaks ⟨originalAttempt, event⟩).respond
                execution who ((joint who).getD ⟨none⟩) originalInput valid ordered (ih enough)
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  change expiryPosition + 1 ≤ next.environmentRecall.length → _
                  intro enough
                  have length := app.environmentStep_environmentRecall execution next command
                    supported
                  have counts : next.environmentRecall.length =
                      execution.environmentRecall.length + 1 := by
                    rw [length, List.length_append, List.length_singleton]
                  by_cases earlier : expiryPosition + 1 ≤ execution.environmentRecall.length
                  · exact (phaseApplication_resolution runtime leaks
                      ⟨originalAttempt, event⟩).environmentStep execution next command supported
                        originalInput valid ordered (ih earlier)
                  · have index : execution.environmentRecall.length = expiryPosition := by omega
                    by_cases original : execution.application.attempt = originalAttempt
                    · have selectedEq : command = choose seeds execution.environmentRecall
                          (execution.observeEnvironment app) := by
                        exact (PMF.mem_support_pure_iff _ _).mp selected
                      have commandEq : command = .application (.expire event) := by
                        rw [selectedEq, choose_original seeds execution.environmentRecall
                          (execution.observeEnvironment app) original, index]
                        rcases position with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
                      rw [commandEq] at supported
                      apply original_expiry_resolves seeds ⟨remaining + 1, none, execution⟩
                        prior original owner event
                      · exact position.elim (fun row => Or.inl row.1) (fun row => Or.inr row.1)
                      · exact actor
                      · exact position.elim (fun row => Or.inl (index.trans row.2))
                          (fun row => Or.inr (index.trans row.2))
                      · exact supported
                    · exact (phaseApplication_resolution runtime leaks
                        ⟨originalAttempt, event⟩).environmentStep execution next command supported
                          originalInput valid ordered
                            (original_resolved_when_retired execution.application original event)

/-- The actual scheduler has physically resolved both first-attempt bindings
after its twenty-two original command slots, under arbitrary raw responses. -/
theorem original_bindings_resolved (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (enough : 22 ≤ current.execution.environmentRecall.length) :
    (originalCoordinate alice).Resolved current.execution.application ∧
      (originalCoordinate bob).Resolved current.execution.application := by
  constructor
  · exact original_expired_history seeds alice aliceBinding 20
      (Or.inl ⟨rfl, rfl⟩) binding_actors.1 trace (by omega)
  · exact original_expired_history seeds bob bobBinding 21
      (Or.inr ⟨rfl, rfl⟩) binding_actors.2 trace enough

/-- First-attempt padding cannot persist after its last expiry. The genuine
normalizer has already advanced or installed the survivor's fresh retry. -/
theorem original_attempt_retired (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (enough : 22 ≤ current.execution.environmentRecall.length) :
    current.execution.application.attempt ≠ originalAttempt := by
  intro original
  have results := original_bindings_resolved seeds current trace enough
  have completed (event : graph.EventId)
      (resolved : (⟨originalAttempt, event⟩ : CommitAttemptEvent graph).Resolved
        current.execution.application) :
      event ∈ current.execution.application.current.native.config.cut.completed := by
    rcases resolved with generation | phase | ⟨_same, completed⟩
    · rw [original] at generation
      change 0 < 0 at generation
      omega
    · rw [original] at phase
      change 0 < 0 at phase
      omega
    · exact completed
  have firstDone := completed aliceBinding results.1
  have secondDone := completed bobBinding results.2
  have geometry := raw_phase_geometry (family seeds) current trace
  have phases := original_phases (family seeds) current trace original
  apply geometry.2.1 commitmentPhase (by rw [phases]; rfl)
  intro event inside
  have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
  change 0 ≤ event.val ∧ event.val < 2 at interval
  fin_cases event
  · exact firstDone
  · exact secondDone
  · change 0 ≤ 2 ∧ 2 < 2 at interval
    omega
  · change 0 ≤ 3 ∧ 3 < 2 at interval
    omega

end Vegas.Examples.CommitSeedSignalling

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingContract
import Vegas.Pending.PhaseSeedBudget

/-! # Deadline completion of the actual protected continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

theorem raw_phases_cases (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) :
    current.execution.application.phases = [commitmentPhase, publicationPhase] ∨
      current.execution.application.phases = [publicationPhase] ∨
      current.execution.application.phases = [] := by
  have suffix := phasePlanSuffix_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon selected trace
  rw [plan_phases] at suffix
  rcases List.suffix_cons_iff.mp suffix with same | suffix
  · exact Or.inl same
  · rcases List.suffix_cons_iff.mp suffix with same | suffix
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (List.suffix_nil.mp suffix))

theorem raw_same_attempt_phases (selected : app.Scheduler)
    (first second : app.Control)
    (firstTrace : (app.protocol initial horizon selected).Trace (some first))
    (secondTrace : (app.protocol initial horizon selected).Trace (some second))
    (same : first.execution.application.attempt = second.execution.application.attempt) :
    first.execution.application.phases = second.execution.application.phases := by
  have lows := congrArg CommitAttemptId.phase same
  change (first.execution.application.phases.head?.map RuntimePhase.low).getD 4 =
    (second.execution.application.phases.head?.map RuntimePhase.low).getD
      4 at lows
  rcases raw_phases_cases selected first firstTrace with firstPhases | firstPhases | firstPhases
  all_goals
    rcases raw_phases_cases selected second secondTrace with
      secondPhases | secondPhases | secondPhases
  all_goals
    rw [firstPhases, secondPhases] at lows
    first
    | exact firstPhases.trans secondPhases.symm
    | norm_num [commitmentPhase, publicationPhase] at lows

private def blockElapsed (kind : RuntimePhaseKind) (position : Nat) : Nat :=
  match kind with
  | .commitment => min (position - 2) 6
  | .reveal => min (position - 4) 6
  | .sample => 0

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

private theorem responseCommand_ticks (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (responseCommand owner past view) = 0 := by
  cases last : past.getLast? with
  | none => simp only [responseCommand, last, PhaseSeedCalendar.commandTicks]
  | some entry =>
      simp only [responseCommand, last]
      split
      · exact pendingCommand_ticks _ _
      · rfl

private theorem block_elapsed_step (kind : RuntimePhaseKind) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    blockElapsed kind (position + 1) ≤ blockElapsed kind position +
      PhaseSeedCalendar.commandTicks runtime leaks
        (match kind with
        | .commitment => retryCommand position past view
        | .reveal => revealCommand position past view
        | .sample => .wait) := by
  cases kind with
  | commitment =>
      match position with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
          simp only [blockElapsed, retryCommand]
          try rw [activateReady_ticks]
          try rw [responseCommand_ticks]
          decide
      | 8 =>
          change min (8 + 1 - 2) 6 ≤ min (8 - 2) 6 + 0
          decide
      | position + 9 =>
          rw [retryCommand_bound _ _ _ (by omega)]
          change min (position + 9 + 1 - 2) 6 ≤ min (position + 9 - 2) 6 + 0
          omega
  | reveal =>
      match position with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 =>
          simp only [blockElapsed, revealCommand]
          try rw [activateReady_ticks]
          try rw [responseCommand_ticks]
          decide
      | position + 12 =>
          rw [revealCommand_bound _ _ _ (by omega)]
          change min (position + 12 + 1 - 4) 6 ≤ min (position + 12 - 4) 6 + 0
          omega
  | sample => change 0 ≤ 0; omega

private def TailTimers (execution : app.Execution) : Prop :=
  execution.application.attempt ≠ originalAttempt →
    ∀ (phase : RuntimePhase graph), execution.application.phases.head? = some phase →
    ∀ event ∈ phase.events, ∀ entered,
      event ∉ execution.application.current.native.config.cut.completed →
      execution.application.current.native.activatedAt event = some entered →
      entered + blockElapsed phase.kind
        (tailIndex execution.environmentRecall (execution.observeEnvironment app)) ≤
          execution.application.current.native.clock

private theorem timers_progress (seeds : Seeds) (before : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some before))
    (after : app.Execution) (ticks : Nat)
    (progress : EventGraphRuntime.State.ServiceProgress originalInput ticks
      before.execution.application.current.native after.application.current.native)
    (same : before.execution.application.attempt = after.application.attempt)
    (phases : before.execution.application.phases = after.application.phases)
    (age : ∀ phase, before.execution.application.phases.head? = some phase →
      blockElapsed phase.kind (tailIndex after.environmentRecall (after.observeEnvironment app)) ≤
        blockElapsed phase.kind (tailIndex before.execution.environmentRecall
          (before.execution.observeEnvironment app)) + ticks)
    (timers : TailTimers before.execution) : TailTimers after := by
  intro notOriginal phase installed event inside entered unfinished stamp
  have beforeNotOriginal : before.execution.application.attempt ≠ originalAttempt := by
    intro original
    exact notOriginal (same.symm.trans original)
  have installedBefore : before.execution.application.phases.head? = some phase := by
    rw [phases]
    exact installed
  have blocks : phase = commitmentPhase ∨ phase = publicationPhase := by
    rcases raw_phases_cases (family seeds) before trace with all | reveal | empty
    · rw [all] at installedBefore
      exact Or.inl (Option.some.inj installedBefore).symm
    · rw [reveal] at installedBefore
      exact Or.inr (Option.some.inj installedBefore).symm
    · rw [empty] at installedBefore
      cases installedBefore
  have beforeUnfinished :
      event ∉ before.execution.application.current.native.config.cut.completed :=
    fun done => unfinished (progress.completed done)
  have readyBefore := raw_phase_event_ready (family seeds) before trace phase installedBefore
    blocks event inside beforeUnfinished
  have valid := raw_native_valid (family seeds) before trace
  have acting : (graph.actor? event).isSome = true := by
    change Fin 4 at event
    fin_cases event
    · change (graph.actor? aliceBinding).isSome = true
      rw [binding_actors.1]; rfl
    · change (graph.actor? bobBinding).isSome = true
      rw [binding_actors.2]; rfl
    · change (graph.actor? aliceReveal).isSome = true
      rw [reveal_actors.1]; rfl
    · change (graph.actor? bobReveal).isSome = true
      rw [reveal_actors.2]; rfl
  obtain ⟨beforeEntered, beforeStamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff event).mpr ⟨readyBefore, acting⟩)
  have afterStamp := progress.activated event beforeEntered beforeStamp unfinished
  have enteredEq : beforeEntered = entered := Option.some.inj (afterStamp.symm.trans stamp)
  subst beforeEntered
  have priorAge := timers beforeNotOriginal phase installedBefore event inside entered
    beforeUnfinished beforeStamp
  have grows := age phase installedBefore
  have clock := progress.clock
  omega

/-- Every unfinished tail event has aged by the actual clock advances of its
current namespace's command block. No prescribed response law is assumed. -/
theorem raw_tail_timers (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => TailTimers current.execution) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      have targetTrace := prior.extend joint legal reached
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
          subst state
          intro impossible
          exact (impossible initialState_attempt).elim
      | some before =>
          rcases before with ⟨remaining, active, execution⟩
          have valid := raw_native_valid (family seeds) ⟨remaining, active, execution⟩ prior
          have geometry := raw_phase_geometry (family seeds) ⟨remaining, active, execution⟩ prior
          have ordered : execution.application.Ordered := geometry.1.adjacent
          cases active with
          | some owner =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              let action := (joint owner).getD (⟨none⟩ : app.Action)
              let after := execution.respond app owner action
              have same : execution.application.attempt = after.application.attempt := by
                rcases action with ⟨submission⟩
                cases submission <;> rfl
              have phases : execution.application.phases = after.application.phases := by
                rcases action with ⟨submission⟩
                cases submission <;> rfl
              obtain ⟨ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).respond
                execution owner action originalInput valid ordered same
              apply timers_progress seeds ⟨remaining, some owner, execution⟩ prior after ticks
                progress same phases _ ih
              intro phase installed
              have index : tailIndex after.environmentRecall (after.observeEnvironment app) =
                  tailIndex execution.environmentRecall (execution.observeEnvironment app) := by
                rw [app.respond_environmentRecall]
                exact tailIndex_congr_attempt _ _ _ same.symm
              change blockElapsed phase.kind
                  (tailIndex after.environmentRecall (after.observeEnvironment app)) ≤
                blockElapsed phase.kind
                  (tailIndex execution.environmentRecall (execution.observeEnvironment app)) + ticks
              rw [index]
              omega
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  by_cases same : execution.application.attempt = next.application.attempt
                  · by_cases original : next.application.attempt = originalAttempt
                    · intro notOriginal
                      exact (notOriginal original).elim
                    · obtain ⟨ticks, progress⟩ :=
                        (phaseApplication_serviceProgress runtime leaks).environmentStep
                          execution next command supported originalInput valid ordered same
                      have phases := raw_same_attempt_phases (family seeds)
                        ⟨remaining + 1, none, execution⟩ _ prior targetTrace same
                      apply timers_progress seeds ⟨remaining + 1, none, execution⟩ prior next ticks
                        progress same phases _ ih
                      intro phase installed
                      have selectedEq : command = choose seeds execution.environmentRecall
                          (execution.observeEnvironment app) :=
                        (PMF.mem_support_pure_iff _ _).mp selected
                      have beforeNotOriginal : execution.application.attempt ≠ originalAttempt :=
                        fun originalBefore => original (same.symm.trans originalBefore)
                      have chooseEq : command = match phase.kind with
                          | .commitment => retryCommand (tailIndex execution.environmentRecall
                              (execution.observeEnvironment app)) execution.environmentRecall
                                (execution.observeEnvironment app)
                          | .reveal => revealCommand (tailIndex execution.environmentRecall
                              (execution.observeEnvironment app)) execution.environmentRecall
                                (execution.observeEnvironment app)
                          | .sample => .wait := by
                        have retiredView : (execution.observeEnvironment app).application.attempt ≠
                            originalAttempt := beforeNotOriginal
                        have phaseView : (execution.observeEnvironment app).application.phase =
                            some (phase.kind, phase.low, phase.high) := by
                          change execution.application.phases.head?.map
                            (fun installed => (installed.kind, installed.low, installed.high)) = _
                          rw [installed]
                          rfl
                        rw [selectedEq, choose, ite_eq_right retiredView, phaseView]
                        cases phase.kind <;> rfl
                      have index := tailIndex_after_same_attempt execution next command supported
                        same.symm
                      have step := block_elapsed_step phase.kind
                        (tailIndex execution.environmentRecall (execution.observeEnvironment app))
                        execution.environmentRecall (execution.observeEnvironment app)
                      have physicalClock := PhaseSeedCalendar.environmentStep_clock runtime leaks
                        execution next command valid supported
                      have ticksEq : ticks =
                          PhaseSeedCalendar.commandTicks runtime leaks command :=
                        Nat.add_left_cancel (progress.clock.symm.trans physicalClock)
                      rw [chooseEq] at ticksEq
                      change blockElapsed phase.kind
                          (tailIndex next.environmentRecall (next.observeEnvironment app)) ≤
                        blockElapsed phase.kind (tailIndex execution.environmentRecall
                          (execution.observeEnvironment app)) + ticks
                      rw [index, ticksEq]
                      exact step
                  · intro _notOriginal phase _installed event _inside entered _unfinished stamp
                    have index := tailIndex_after_retirement seeds
                      ⟨remaining + 1, none, execution⟩ prior next command supported same
                    have nativeInvariant := phaseApplication_invariant runtime leaks originalInput
                    have validAfter := nativeInvariant.environmentStep
                      execution next command valid supported
                    have bounded := validAfter.active.activated_le event entered stamp
                    rw [index]
                    cases phase.kind <;> simpa only [blockElapsed, Nat.zero_sub,
                      min_eq_left (by omega : 0 ≤ 6), Nat.add_zero] using bounded

/-- At the actual expiry slots, every still-unfinished tail event has reached
its original deadline, even if this is a retry with a nonzero entry clock. -/
theorem tail_expiry_resolves (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (notOriginal : current.execution.application.attempt ≠ originalAttempt)
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (block : phase = commitmentPhase ∨ phase = publicationPhase)
    (owner : Player) (event : graph.EventId) (inside : event ∈ phase.events)
    (actor : graph.actor? event = some owner)
    (position : (phase = commitmentPhase ∧
        tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app) = 8) ∨
      (phase = publicationPhase ∧
        (tailIndex current.execution.environmentRecall
            (current.execution.observeEnvironment app) = 10 ∨
          tailIndex current.execution.environmentRecall
            (current.execution.observeEnvironment app) = 11)))
    (next : app.Execution)
    (reached : next ∈
      (current.execution.environmentStep app (.application (.expire event))).support) :
    (⟨current.execution.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
      next.application := by
  have valid := raw_native_valid (family seeds) current trace
  have geometry := raw_phase_geometry (family seeds) current trace
  have ordered : current.execution.application.Ordered := geometry.1.adjacent
  by_cases done : event ∈ current.execution.application.current.native.config.cut.completed
  · exact (phaseApplication_resolution runtime leaks
      ⟨current.execution.application.attempt, event⟩).environmentStep
        current.execution next (.application (.expire event)) reached originalInput valid ordered
          (Or.inr (Or.inr ⟨rfl, done⟩))
  · have requested := raw_phase_event_request (family seeds) current trace phase installed block
      event inside owner actor done
    have ready := requested.2.2.1
    obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
      ((valid.active.activated_iff event).mpr ⟨ready, by rw [actor]; rfl⟩)
    have aged := raw_tail_timers seeds trace notOriginal phase installed event inside entered
      done stamp
    have elapsed : blockElapsed phase.kind
        (tailIndex current.execution.environmentRecall (current.execution.observeEnvironment app))
          = 6 := by
      rcases position with ⟨rfl, index⟩ | ⟨rfl, index | index⟩ <;>
        rw [index] <;> rfl
    rw [elapsed] at aged
    have moved : next.application ∈
        (current.execution.application.environment runtime (.expire event)).support := by
      have applicationReached := reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
        at applicationReached
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ applicationReached
      exact supported
    have resolved := current.execution.application.expire_resolves_of_request runtime
      next.application valid ordered requested (by
        rw [stamp, Option.getD_some]
        change 6 ≤ _
        omega) moved
    exact CommitAttemptEvent.Resolved.of_step
      ⟨current.execution.application.attempt, event⟩ current.execution.application
        next.application rfl
        ((phaseApplication_namespace_progress runtime leaks).environmentStep
          current.execution next (.application (.expire event)) reached ordered) resolved

end Vegas.Examples.CommitSeedSignalling

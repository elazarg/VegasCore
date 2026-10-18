/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalCompletion
import Vegas.Pending.PhaseSeedBudget
import Vegas.Pending.PhaseRequestOrigin

/-! # Deadline completion of the actual protected continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

theorem raw_phases_cases (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) :
    current.execution.application.phases = [commitmentPhase, publicationPhase] ∨
      current.execution.application.phases = [publicationPhase] ∨
      current.execution.application.phases = [] := by
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
  change (first.execution.application.phases.head?.map RuntimePhase.low).getD 6 =
    (second.execution.application.phases.head?.map RuntimePhase.low).getD
      6 at lows
  rcases raw_phases_cases selected first firstTrace with firstPhases | firstPhases | firstPhases
  all_goals
    rcases raw_phases_cases selected second secondTrace with
      secondPhases | secondPhases | secondPhases
  all_goals
    rw [firstPhases, secondPhases] at lows
    first
    | exact firstPhases.trans secondPhases.symm
    | norm_num [commitmentPhase, publicationPhase] at lows

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
  have compiledTrace : (app.protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon (family seeds)).Trace (some current) := by
    change (app.protocol (((PMF.pure (Env.empty (CellVal simpleExpr))).map encodeInputs).map
      (PhaseRuntimeState.initial plan)) horizon (family seeds)).Trace (some current)
    rw [PMF.pure_map, PMF.pure_map]
    exact trace
  have namespaceFact := PhaseSeedFreshness.namespacePast_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seeds) current compiledTrace
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

private theorem event_actor_exists (event : graph.EventId) :
    ∃ owner, graph.actor? event = some owner := by
  change Fin 6 at event
  fin_cases event
  · exact ⟨alice, rfl⟩
  · exact ⟨bob, rfl⟩
  · exact ⟨carol, rfl⟩
  · exact ⟨alice, rfl⟩
  · exact ⟨bob, rfl⟩
  · exact ⟨carol, rfl⟩

private def blockElapsed (kind : RuntimePhaseKind) (position : Nat) : Nat :=
  match kind with
  | .commitment | .reveal => min (position - 6) 6
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
    blockElapsed kind (position + 1) = blockElapsed kind position +
      PhaseSeedCalendar.commandTicks runtime leaks
        (match kind with
        | .commitment => tailCommand bindingEvent position past view
        | .reveal => tailCommand revealEvent position past view
        | .sample => .wait) := by
  cases kind with
  | commitment | reveal =>
      match position with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 =>
          simp only [blockElapsed, tailCommand]
          try rw [activateReady_ticks]
          try rw [responseCommand_ticks]
          decide
      | position + 15 =>
          change min (position + 15 + 1 - 6) 6 = min (position + 15 - 6) 6 + 0
          omega
  | sample => rfl

private def TailTimers (execution : app.Execution) : Prop :=
  execution.application.attempt ≠ originalAttempt →
    ∀ (phase : RuntimePhase graph), execution.application.phases.head? = some phase →
    ∀ event ∈ phase.events, ∀ entered,
      event ∉ execution.application.current.native.config.cut.completed →
      execution.application.current.native.activatedAt event = some entered →
      entered + blockElapsed phase.kind
        (tailIndex execution.environmentRecall (execution.observeEnvironment app)) ≤
          execution.application.current.native.clock

private def ExactTailTimers (execution : app.Execution) : Prop :=
  execution.application.attempt ≠ originalAttempt →
    ∀ (phase : RuntimePhase graph), execution.application.phases.head? = some phase →
    ∀ event ∈ phase.events, ∀ entered,
      event ∉ execution.application.current.native.config.cut.completed →
      execution.application.current.native.activatedAt event = some entered →
      entered + blockElapsed phase.kind
        (tailIndex execution.environmentRecall (execution.observeEnvironment app)) =
          execution.application.current.native.clock

private theorem timers_progress (seeds : Seeds) (before : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some before))
    (after : app.Execution) (ticks : Nat)
    (progress : EventGraphRuntime.State.ServiceProgress originalInput ticks
      before.execution.application.current.native after.application.current.native)
    (same : before.execution.application.attempt = after.application.attempt)
    (phases : before.execution.application.phases = after.application.phases)
    (age : ∀ phase, before.execution.application.phases.head? = some phase →
      blockElapsed phase.kind (tailIndex after.environmentRecall (after.observeEnvironment app)) =
        blockElapsed phase.kind (tailIndex before.execution.environmentRecall
          (before.execution.observeEnvironment app)) + ticks)
    (timers : ExactTailTimers before.execution) : ExactTailTimers after := by
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
    obtain ⟨owner, actor⟩ := event_actor_exists event
    rw [actor]
    rfl
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

private theorem raw_exact_tail_timers (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => ExactTailTimers current.execution) := by
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
          rw [initial, PMF.mem_support_pure_iff] at supported
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
                  (tailIndex after.environmentRecall (after.observeEnvironment app)) =
                blockElapsed phase.kind
                  (tailIndex execution.environmentRecall (execution.observeEnvironment app)) + ticks
              rw [index]
              have noTicks := PhaseSeedCalendar.respond_clock runtime leaks execution valid owner
                action
              have clock := progress.clock
              change (execution.respond app owner action).application.current.native.clock =
                execution.application.current.native.clock + ticks at clock
              rw [noTicks] at clock
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
                          | .commitment => tailCommand bindingEvent
                              (tailIndex execution.environmentRecall
                                (execution.observeEnvironment app)) execution.environmentRecall
                                  (execution.observeEnvironment app)
                          | .reveal => tailCommand revealEvent
                              (tailIndex execution.environmentRecall
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
                          (tailIndex next.environmentRecall (next.observeEnvironment app)) =
                        blockElapsed phase.kind (tailIndex execution.environmentRecall
                          (execution.observeEnvironment app)) + ticks
                      rw [index, ticksEq]
                      exact step
                  · intro _notOriginal phase installed event inside entered unfinished stamp
                    have index := tailIndex_after_retirement seeds
                      ⟨remaining + 1, none, execution⟩ prior next command supported same
                    have nativeInvariant := phaseApplication_invariant runtime leaks originalInput
                    have validAfter := nativeInvariant.environmentStep
                      execution next command valid supported
                    have bounded := validAfter.active.activated_le event entered stamp
                    have blocks : phase = commitmentPhase ∨ phase = publicationPhase := by
                      rcases raw_phases_cases (family seeds) _ targetTrace with all | reveal | empty
                      · rw [all] at installed
                        exact Or.inl (Option.some.inj installed).symm
                      · rw [reveal] at installed
                        exact Or.inr (Option.some.inj installed).symm
                      · rw [empty] at installed
                        cases installed
                    obtain ⟨owner, acting⟩ := event_actor_exists event
                    have requested := raw_phase_event_request (family seeds) _ targetTrace phase
                      installed blocks event inside owner acting unfinished
                    have physicalClock := PhaseSeedCalendar.environmentStep_clock runtime leaks
                      execution next command valid supported
                    have recent : next.application.current.native.clock ≤ entered := by
                      by_cases advancing : command = .application .advanceClock
                      · have origin := PhaseSeedScheduler.advanceClock_request_origin runtime leaks
                          execution next
                          (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) valid
                          geometry.1 geometry.2.1 geometry.2.2.1 geometry.2.2.2
                          (advancing ▸ supported) owner _ entered requested stamp
                        rcases origin with old | recent
                        · exact (same (old.1.1.symm.trans requested.1)).elim
                        · rw [advancing] at physicalClock
                          change next.application.current.native.clock =
                            execution.application.current.native.clock + 1 at physicalClock
                          omega
                      · have origin := PhaseSeedScheduler.environmentStep_request_origin
                          runtime leaks execution next command
                          (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) valid
                          geometry.1 geometry.2.1 geometry.2.2.1 geometry.2.2.2 supported owner _
                          entered requested stamp
                        rcases origin with old | recent
                        · exact (same (old.1.1.symm.trans requested.1)).elim
                        · have zero : PhaseSeedCalendar.commandTicks runtime leaks command = 0 := by
                            cases command with
                            | wait => rfl
                            | activate who => rfl
                            | «include» identifier => rfl
                            | application operation =>
                                cases operation with
                                | advanceClock => exact (advancing rfl).elim
                                | executeSample event => rfl
                                | expire event => rfl
                          rw [zero, Nat.add_zero] at physicalClock
                          exact physicalClock.trans_le recent
                    have enteredEq : entered = next.application.current.native.clock :=
                      Nat.le_antisymm bounded recent
                    rw [index]
                    cases phase.kind <;> simpa only [blockElapsed, Nat.zero_sub,
                      min_eq_left (by omega : 0 ≤ 6), Nat.add_zero] using enteredEq

/-- Every unfinished tail event has aged by the actual clock advances of its
current namespace's command block. No prescribed response law is assumed. -/
theorem raw_tail_timers (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => TailTimers current.execution) := by
  intro state trace
  cases state with
  | none => trivial
  | some current =>
      intro retired phase installed event inside entered unfinished stamp
      exact Nat.le_of_eq (raw_exact_tail_timers seeds trace retired phase installed event inside
        entered unfinished stamp)

/-- Each still-requesting tail coordinate measures its own actual original
entry age, independent of the absolute clock at which its retry began. -/
theorem tail_request_elapsed (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate) :
    PhaseSeedScheduler.elapsed runtime leaks coordinate
        (current.execution.observeEnvironment app) =
      min (tailIndex current.execution.environmentRecall
        (current.execution.observeEnvironment app) - 6) 6 := by
  obtain ⟨phase, member, inside⟩ := request.2.1
  have installed : current.execution.application.phases.head? = some phase :=
    Option.mem_def.mp member
  have valid := raw_native_valid (family seeds) current trace
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff coordinate.event).mpr ⟨request.2.2.1, by
      rw [request.2.2.2.1]; rfl⟩)
  have aged := raw_exact_tail_timers seeds trace (by rwa [← request.1]) phase installed
    coordinate.event inside entered request.2.2.1.1 stamp
  have blocks : phase = commitmentPhase ∨ phase = publicationPhase := by
    rcases raw_phases_cases (family seeds) current trace with all | reveal | empty
    · rw [all] at installed
      exact Or.inl (Option.some.inj installed).symm
    · rw [reveal] at installed
      exact Or.inr (Option.some.inj installed).symm
    · rw [empty] at installed
      cases installed
  change current.execution.application.current.native.clock -
    (current.execution.application.current.native.activatedAt coordinate.event).getD
      current.execution.application.current.native.clock = _
  rw [stamp, Option.getD_some, ← aged]
  rcases blocks with rfl | rfl
  all_goals change entered + min _ 6 - entered = min _ 6
  all_goals omega

theorem tail_expiry_resolves (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (notOriginal : current.execution.application.attempt ≠ originalAttempt)
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (block : phase = commitmentPhase ∨ phase = publicationPhase)
    (owner : Player) (event : graph.EventId) (inside : event ∈ phase.events)
    (actor : graph.actor? event = some owner)
    (position : 12 ≤ tailIndex current.execution.environmentRecall
      (current.execution.observeEnvironment app))
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
      rcases block with rfl | rfl
      all_goals change min (_ - 6) 6 = 6
      all_goals omega
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

end Vegas.Examples.CommitSeedBroadcast

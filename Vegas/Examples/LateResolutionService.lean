/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceGeometricTiming
import Vegas.Expr.Simple
import Vegas.Pending.ReactiveAsyncContract
import Interaction.ReactiveOwnerSelection
import Vegas.Game.ServiceRosterAsync

/-! # A source resolution with a censored second opportunity

The fixed compiled setup has an authentic initial binding, two deterministic
public samples, and one owned resolution. Its public scheduler satisfies all
three asynchronous contract clauses at every legal raw history. It includes
any first event-addressed response at clock zero, but includes only withholding
on the second opportunity at clock one, before expiry at clock three.

This module certifies the service contract and its timing budget. It does not
assert a source equilibrium or compare terminal continuation payoffs.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

abbrev Player := Fin 1
abbrev owner : Player := 0
abbrev initialCtx : SourceCtx Player simpleExpr := [(0, .commitment owner .bool)]

def program : SourceProgram Player simpleExpr initialCtx {0} :=
  .sample 1 (payload := .bool) (by decide) (.weighted (.pure true)) <|
  .sample 2 (payload := .bool) (by decide) (.weighted (.pure true)) <|
  .reveal 3 owner 0 (by decide) (.there (.there .here)) (by decide) <|
  .ret [(owner, .ite (.isSuccess (.var 3 .here)) (.constInt 1) (.constInt 0))]

def sourceInitial : State simpleExpr initialCtx :=
  Env.cons (.success true) (Env.empty _)

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := PMF.pure sourceInitial
  obligations := {0}
  program := program
  accounts := rfl

abbrev nativeGraph := graph setup
abbrev sample0 : nativeGraph.EventId := ⟨0, by decide⟩
abbrev sample1 : nativeGraph.EventId := ⟨1, by decide⟩
abbrev resolution : nativeGraph.EventId := ⟨2, by decide⟩

def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun _ _ => PMF.pure ∅

abbrev app := application setup leaks

def latest (view : app.EnvironmentView) : app.Command :=
  (runtime setup).reactiveLatest leaks resolution owner view

def latestWithhold (view : app.EnvironmentView) : app.Command := by
  classical
  exact
  match view.network.pending.reverse.find? (fun message =>
      decide (message.sender = owner ∧ message.payload.call = .withhold resolution ∧
        view.Unpublished app message.id)) with
  | none => .wait
  | some message => .include message.id

/-- Two samples, a protected response at clock zero, and a second response at
clock one. The public scheduler includes only withholding on the second turn,
then advances to clock three and expires any still-ready resolution. -/
def stageCommand (stage : Nat) (view : app.EnvironmentView) : app.Command :=
  match stage with
  | 0 => .application (.executeSample sample0)
  | 1 => .application (.executeSample sample1)
  | 2 => .activate owner
  | 3 => latest view
  | 4 => .application .advanceClock
  | 5 => .activate owner
  | 6 => latestWithhold view
  | 7 | 8 => .application .advanceClock
  | 9 => .application (.expire resolution)
  | _ => .wait

def scheduler : app.Scheduler := fun history view => PMF.pure (stageCommand history.length view)

def horizon : Nat := 10
def delay : nativeGraph.EventId → Nat := fun _ => 0
def bound : nativeGraph.EventId → Nat := fun _ => 2

@[simp] theorem sample0_actor : nativeGraph.actor? sample0 = none := rfl
@[simp] theorem sample1_actor : nativeGraph.actor? sample1 = none := rfl
@[simp] theorem resolution_actor : nativeGraph.actor? resolution = some owner := rfl

theorem timely : AsyncTimely (runtime setup) delay bound := by
  intro event owned
  change Fin 3 at event
  fin_cases event
  · change false = true at owned
    contradiction
  · change false = true at owned
    contradiction
  · change 0 + 2 < 3
    decide

def stageClock (stage : Nat) : Nat :=
  if stage ≤ 4 then 0 else if stage ≤ 7 then 1 else if stage ≤ 8 then 2 else 3

def recallCount (stage : Nat) (actor : Option Player) : Nat :=
  if stage ≤ 2 then 0 else if stage = 3 then if actor.isSome then 0 else 1
  else if stage ≤ 5 then 1 else if stage = 6 then if actor.isSome then 1 else 2 else 2

structure Phase (control : app.Control) : Prop where
  budget : control.remaining + control.execution.environmentRecall.length = horizon
  bounded : control.execution.environmentRecall.length ≤ horizon
  clock : control.execution.application.clock =
    stageClock control.execution.environmentRecall.length
  prefix0 : control.execution.environmentRecall.length = 0 →
    control.execution.application.config.cut.IsPrefix 0
  prefix1 : control.execution.environmentRecall.length = 1 →
    control.execution.application.config.cut.IsPrefix 1
  laterPrefix : 2 ≤ control.execution.environmentRecall.length →
    control.execution.application.config.cut.IsPrefix 2 ∨
      control.execution.application.config.cut.IsPrefix 3
  terminalPrefix : control.execution.environmentRecall.length = horizon →
    control.execution.application.config.cut.IsPrefix 3
  entered : control.execution.application.config.cut.IsPrefix 2 →
    control.execution.application.activatedAt resolution = some 0
  opportunity : 3 ≤ control.execution.environmentRecall.length →
    control.execution.application.config.cut.IsPrefix 2 →
    OwnerActivatedSince (runtime setup) leaks control.execution.environmentRecall
      resolution owner 0
  activation : control.actor.isSome →
    control.execution.environmentRecall.length = 3 ∨
      control.execution.environmentRecall.length = 6
  recallCount : (control.execution.recall owner).length =
    recallCount control.execution.environmentRecall.length control.actor
  responseClock : ∀ entry ∈ control.execution.recall owner,
    entry.beforeView.application.publicView.clock = 0 ∨
      entry.beforeView.application.publicView.clock = 1
  receipt0 : 4 ≤ control.execution.environmentRecall.length →
    ∀ entry ∈ control.execution.recall owner,
      entry.beforeView.application.publicView.clock = 0 →
      ∀ message, entry.emitted = some message →
        message.payload.call.event? nativeGraph = some resolution →
        ∃ accepted, (message.id, accepted) ∈ control.execution.receipts

def phaseInvariant : app.ProtocolState → Prop
  | none => True
  | some control => Phase control

theorem phase_initial (state : app.State) (supported : state ∈ (initialLaw setup).support) :
    Phase ⟨horizon, none, ReactiveApplication.Execution.initial app state⟩ := by
  obtain ⟨initial, selected, rfl⟩ := PMF.support_map .. ▸ supported
  have same := (PMF.mem_support_pure_iff _ _).mp selected
  subst initial
  have empty : (EventGraphRuntime.State.initial
      (setup.eventInputs sourceInitial)).config.cut.IsPrefix 0 :=
    EventOrder.Cut.empty_isPrefix _
  refine {
    budget := rfl
    bounded := by simp [ReactiveApplication.Execution.initial, horizon]
    clock := rfl
    prefix0 := fun _ => empty
    prefix1 := by simp [ReactiveApplication.Execution.initial]
    laterPrefix := by simp [ReactiveApplication.Execution.initial]
    terminalPrefix := by simp [ReactiveApplication.Execution.initial, horizon]
    entered := ?_
    opportunity := by simp [ReactiveApplication.Execution.initial]
    activation := by simp
    recallCount := rfl
    responseClock := by simp [ReactiveApplication.Execution.initial]
    receipt0 := by simp [ReactiveApplication.Execution.initial] }
  intro ordered
  have impossible : sample0 ∈ (EventGraphRuntime.State.initial
      (setup.eventInputs sourceInitial)).config.cut.completed := (ordered.2 sample0).mpr (by decide)
  change sample0 ∈ (∅ : Finset nativeGraph.EventId) at impossible
  simp at impossible

theorem phase_respond (control : app.Control) (phase : Phase control)
    (who : Player) (active : control.actor = some who) (response : app.Action) :
    Phase { control with
      actor := none
      execution := control.execution.respond app who response } := by
  have whoEq : who = owner := Subsingleton.elim _ _
  subst who
  obtain ⟨configEq, publicEq⟩ :=
    (runtime setup).reactive_respond_application leaks control.execution owner response
  have clockEq := congrArg PublicView.clock publicEq
  have enteredEq := congrArg PublicView.activatedAt publicEq
  change (control.execution.respond app owner response).application.clock =
    control.execution.application.clock at clockEq
  change (control.execution.respond app owner response).application.activatedAt =
    control.execution.application.activatedAt at enteredEq
  have recallEq := app.respond_environmentRecall control.execution owner response
  have receiptsEq := app.respond_receipts control.execution owner response
  have stage := phase.activation (by rw [active]; rfl)
  have currentClock : control.execution.application.clock = 0 ∨
      control.execution.application.clock = 1 := by
    rw [phase.clock]
    rcases stage with first | second
    · simp [first, stageClock]
    · simp [second, stageClock]
  refine {
    budget := by simpa only [recallEq] using phase.budget
    bounded := by simpa only [recallEq] using phase.bounded
    clock := by simpa only [clockEq, recallEq] using phase.clock
    prefix0 := by simpa only [configEq, recallEq] using phase.prefix0
    prefix1 := by simpa only [configEq, recallEq] using phase.prefix1
    laterPrefix := by simpa only [configEq, recallEq] using phase.laterPrefix
    terminalPrefix := by simpa only [configEq, recallEq] using phase.terminalPrefix
    entered := by simpa only [configEq, enteredEq] using phase.entered
    opportunity := by simpa only [configEq, recallEq] using phase.opportunity
    activation := by simp
    recallCount := ?_
    responseClock := ?_
    receipt0 := ?_ }
  · have length := app.respond_recall_length control.execution owner owner response
    rw [length, phase.recallCount, recallEq, active]
    rcases stage with first | second
    · simp [first, recallCount]
    · simp [second, recallCount]
  · intro entry member
    rcases app.respond_entry_origin control.execution owner owner response entry member with
      prior | ⟨_, fresh⟩
    · exact phase.responseClock entry prior
    · rw [fresh]
      exact currentClock
  · intro late entry member zero message emitted named
    rw [recallEq] at late
    rcases app.respond_entry_origin control.execution owner owner response entry member with
      prior | ⟨_, fresh⟩
    · rw [receiptsEq]
      exact phase.receipt0 late entry prior zero message emitted named
    · rw [fresh] at zero
      have clockNow := phase.clock
      rcases stage with first | second
      · omega
      · simp only [second, stageClock, show ¬ 6 ≤ 4 by decide, ↓reduceIte,
          show 6 ≤ 7 by decide] at clockNow
        have : control.execution.application.clock = 0 := zero
        omega

theorem latest_actor_none (view : app.EnvironmentView) : (latest view).actor? app = none := by
  unfold latest reactiveLatest
  split <;> rfl

theorem latestWithhold_actor_none (view : app.EnvironmentView) :
    (latestWithhold view).actor? app = none := by
  unfold latestWithhold
  split <;> rfl

theorem stageCommand_tick_iff (stage : Nat) (beforeEnd : stage < horizon)
    (view : app.EnvironmentView) :
    stageCommand stage view = .application .advanceClock ↔
      stage = 4 ∨ stage = 7 ∨ stage = 8 := by
  change stage < 10 at beforeEnd
  interval_cases stage <;> simp only [stageCommand, false_or,
    Nat.reduceEqDiff, true_or, or_self]
  all_goals first
    | (unfold latest reactiveLatest; split <;> simp)
    | (unfold latestWithhold; split <;> simp)
    | simp

theorem environment_effect (execution next : app.Execution) (command : app.Command)
    (moved : next ∈ (execution.environmentStep app command).support) :
    (command = .application .advanceClock ∧
      next.application.config = execution.application.config ∧
      next.application.activatedAt = execution.application.activatedAt ∧
      next.application.clock = execution.application.clock + 1) ∨
      GraphStep execution.application next.application := by
  cases command with
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact Or.inr (GraphStep.refl _)
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact Or.inr (GraphStep.refl _)
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact Or.inr (graphStep_includePending (runtime setup) leaks execution id)
  | application command =>
      have supported := (applicationStep_facts execution next command moved).1
      cases command with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff _ _] at supported
          rw [supported]
          exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      | executeSample event =>
          exact Or.inr (graphStep_executeSample (runtime setup) _ _ event supported)
      | expire event =>
          exact Or.inr (graphStep_expire (runtime setup) _ _ event supported)

theorem graphStep_full (before after : EventGraphRuntime.State nativeGraph)
    (ordered : before.config.cut.IsPrefix 3) (step : GraphStep before after) :
    after.config = before.config ∧ after.clock = before.clock ∧
      after.activatedAt = before.activatedAt := by
  rcases step with unchanged | ⟨event, ready, _, _, _, _⟩
  · exact unchanged
  · exact (ready.1 ((ordered.2 event).mpr event.isLt)).elim

theorem graphStep_later (before after : EventGraphRuntime.State nativeGraph)
    (ordered : before.config.cut.IsPrefix 2 ∨ before.config.cut.IsPrefix 3)
    (step : GraphStep before after) :
    (after.config.cut.IsPrefix 2 ∨ after.config.cut.IsPrefix 3) ∧
      after.clock = before.clock ∧
      (after.config.cut.IsPrefix 2 → after.activatedAt = before.activatedAt) := by
  rcases ordered with current | complete
  · rcases step.prefix setup resolution current with unchanged | completed
    · rw [unchanged.1]
      exact ⟨Or.inl current, unchanged.2.1, fun _ => unchanged.2.2⟩
    · exact ⟨Or.inr completed.1, completed.2.1, fun previous =>
        (isPrefix_succ_false resolution previous completed.1).elim⟩
  · obtain ⟨same, clockEq, activatedEq⟩ := graphStep_full before after complete step
    rw [same]
    exact ⟨Or.inr complete, clockEq, fun _ => activatedEq⟩

theorem phase_environment_clock (control : app.Control) (phase : Phase control)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (beforeEnd : control.execution.environmentRecall.length < horizon) :
    next.application.clock = stageClock next.environmentRecall.length := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have chosen : command = stageCommand control.execution.environmentRecall.length
      (control.execution.observeEnvironment app) := (PMF.mem_support_pure_iff _ _).mp selected
  have effect := environment_effect control.execution next command moved
  have tickIff : command = .application .advanceClock ↔
      control.execution.environmentRecall.length = 4 ∨
        control.execution.environmentRecall.length = 7 ∨
        control.execution.environmentRecall.length = 8 := by
    rw [chosen]
    exact stageCommand_tick_iff _ beforeEnd _
  rw [length]
  rcases effect with ⟨tick, _, _, clockEq⟩ | unchanged
  · rw [clockEq, phase.clock]
    rcases tickIff.mp tick with index | index | index <;> simp [index, stageClock]
  · have clockEq : next.application.clock = control.execution.application.clock := by
      rcases unchanged with ⟨_, same, _⟩ | ⟨_, _, _, _, same, _⟩ <;> exact same
    have noTick : command ≠ .application .advanceClock := by
      intro tick
      rw [tick] at moved
      have physical := (applicationStep_facts control.execution next _ moved).1
      simp only [environmentStep, PMF.mem_support_pure_iff _ _] at physical
      rw [physical] at clockEq
      change control.execution.application.clock + 1 =
        control.execution.application.clock at clockEq
      omega
    have excluded := mt tickIff.mpr noTick
    rw [clockEq, phase.clock]
    generalize stageEq : control.execution.environmentRecall.length = stage at beforeEnd excluded ⊢
    change stage < 10 at beforeEnd
    interval_cases stage <;> simp_all [stageClock]

theorem phase_environment_prefix (control : app.Control) (phase : Phase control)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support) :
    (next.environmentRecall.length = 1 → next.application.config.cut.IsPrefix 1) ∧
      (2 ≤ next.environmentRecall.length →
        next.application.config.cut.IsPrefix 2 ∨ next.application.config.cut.IsPrefix 3) := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have chosen : command = stageCommand control.execution.environmentRecall.length
      (control.execution.observeEnvironment app) := (PMF.mem_support_pure_iff _ _).mp selected
  by_cases first : control.execution.environmentRecall.length = 0
  · have chosenSample : command = .application (.executeSample sample0) := by
      simpa only [first, stageCommand] using chosen
    rw [chosenSample] at moved
    have current := phase.prefix0 first
    have ready := (ready_iff_rank setup _ 0 current sample0).mpr rfl
    have physical := (applicationStep_facts control.execution next _ moved).1
    have cutEq := (executeSample_completes (runtime setup) _ _ sample0 sample0_actor
      ready physical).1
    refine ⟨fun _ => ?_, fun late => False.elim (by omega)⟩
    rw [cutEq]
    exact current.complete_at sample0 ready rfl
  by_cases second : control.execution.environmentRecall.length = 1
  · have chosenSample : command = .application (.executeSample sample1) := by
      simpa only [second, stageCommand] using chosen
    rw [chosenSample] at moved
    have current := phase.prefix1 second
    have ready := (ready_iff_rank setup _ 1 current sample1).mpr rfl
    have physical := (applicationStep_facts control.execution next _ moved).1
    have cutEq := (executeSample_completes (runtime setup) _ _ sample1 sample1_actor
      ready physical).1
    refine ⟨fun impossible => False.elim (by omega), fun _ => Or.inl ?_⟩
    rw [cutEq]
    exact current.complete_at sample1 ready rfl
  refine ⟨fun impossible => False.elim (by omega), fun _ => ?_⟩
  have current := phase.laterPrefix (by omega)
  rcases environment_effect control.execution next command moved with
    ⟨_, configEq, _, _⟩ | actual
  · rw [configEq]
    exact current
  · exact (graphStep_later _ _ current actual).1

theorem phase_environment_backwards (control : app.Control) (phase : Phase control)
    (next : app.Execution) (command : app.Command)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (later : 2 ≤ control.execution.environmentRecall.length)
    (current : next.application.config.cut.IsPrefix 2) :
    control.execution.application.config.cut.IsPrefix 2 ∧
      next.application.activatedAt = control.execution.application.activatedAt := by
  have before := phase.laterPrefix later
  rcases environment_effect control.execution next command moved with
    ⟨_, configEq, activatedEq, _⟩ | actual
  · exact ⟨configEq ▸ current, activatedEq⟩
  rcases before with unfinished | complete
  · exact ⟨unfinished, (graphStep_later _ _ (Or.inl unfinished) actual).2.2 current⟩
  · obtain ⟨same, _, _⟩ := graphStep_full _ _ complete actual
    rw [same] at current
    exact (isPrefix_succ_false resolution current complete).elim

theorem phase_environment_entered (control : app.Control) (phase : Phase control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (beforeEnd : control.execution.environmentRecall.length < horizon)
    (current : next.application.config.cut.IsPrefix 2) :
    next.application.activatedAt resolution = some 0 := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have chosen : command = stageCommand control.execution.environmentRecall.length
      (control.execution.observeEnvironment app) := (PMF.mem_support_pure_iff _ _).mp selected
  by_cases first : control.execution.environmentRecall.length = 0
  · have before := (phase_environment_prefix control phase next command selected moved).1
      (by omega)
    exact (isPrefix_succ_false sample1 before current).elim
  by_cases second : control.execution.environmentRecall.length = 1
  · have sampleEq : command = .application (.executeSample sample1) := by
      simpa only [second, stageCommand] using chosen
    rw [sampleEq] at moved
    have physical := (applicationStep_facts control.execution next _ moved).1
    obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler trace).1
    have afterInvariant := environmentStep_invariant (runtime setup) _ _ _ invariant physical
    have ready := (ready_iff_rank setup _ 2 current resolution).mpr rfl
    obtain ⟨entered, activated⟩ := afterInvariant.activatedAt_eq_some_of_ready_actor resolution
      ready (by rw [resolution_actor]; rfl)
    have early := afterInvariant.activated_le resolution entered activated
    have clockEq := phase_environment_clock control phase next command selected
      (sampleEq ▸ moved) beforeEnd
    have zeroClock : next.application.clock = 0 := by
      rw [clockEq, length, second]
      rfl
    rw [zeroClock] at early
    have zero : entered = 0 := by omega
    simpa only [zero] using activated
  obtain ⟨before, activatedEq⟩ := phase_environment_backwards control phase next command moved
    (by omega) current
  rw [activatedEq]
  exact phase.entered before

theorem phase_environment_opportunity (control : app.Control) (phase : Phase control)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (late : 3 ≤ next.environmentRecall.length)
    (current : next.application.config.cut.IsPrefix 2) :
    OwnerActivatedSince (runtime setup) leaks next.environmentRecall resolution owner 0 := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  obtain ⟨before, _⟩ := phase_environment_backwards control phase next command moved
    (by omega) current
  rw [appended]
  by_cases fresh : control.execution.environmentRecall.length = 2
  · have chosen : command = .activate owner := by
      have actual := (PMF.mem_support_pure_iff _ _).mp selected
      simpa only [fresh, stageCommand] using actual
    refine ⟨⟨control.execution.observeEnvironment app, command⟩,
      List.mem_append_right _ (List.mem_singleton_self _), chosen, phase.entered before, ?_⟩
    exact (EventGraphRuntime.State.publicView_eventReady _ resolution).mpr
      ((ready_iff_rank setup _ 2 before resolution).mpr rfl)
  exact ownerActivatedSince_append (phase.opportunity (by omega) before) _

theorem phase_environment_terminal (control : app.Control) (phase : Phase control)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (atEnd : next.environmentRecall.length = horizon) :
    next.application.config.cut.IsPrefix 3 := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have stage : control.execution.environmentRecall.length = 9 := by
    change next.environmentRecall.length = 10 at atEnd
    omega
  have chosen : command = .application (.expire resolution) := by
    have actual := (PMF.mem_support_pure_iff _ _).mp selected
    simpa only [stage, stageCommand] using actual
  rw [chosen] at moved
  have physical := (applicationStep_facts control.execution next _ moved).1
  rcases phase.laterPrefix (by omega) with unfinished | complete
  · have ready := (ready_iff_rank setup _ 2 unfinished resolution).mpr rfl
    have activated := phase.entered unfinished
    have clockEq : control.execution.application.clock = 3 := by
      rw [phase.clock, stage]
      rfl
    have due : (runtime setup).deadline resolution ≤ control.execution.application.clock - 0 := by
      change 3 ≤ _
      omega
    have cutEq := (expire_completes (runtime setup) _ _ resolution owner resolution_actor ready
      0 activated due physical).1
    rw [cutEq]
    exact unfinished.complete_at resolution ready rfl
  · have notReady : ¬ control.execution.application.config.cut.Ready resolution := by
      intro ready
      exact ready.1 ((complete.2 resolution).mpr (by decide))
    rw [environmentStep_expire_of_not_ready (runtime setup) _ resolution notReady,
      PMF.mem_support_pure_iff _ _] at physical
    rw [physical]
    exact complete

theorem phase_environment_receipt0 (control : app.Control) (phase : Phase control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (idle : control.actor = none)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (late : 4 ≤ next.environmentRecall.length)
    (entry : app.PlayerEntry) (member : entry ∈ next.recall owner)
    (zero : entry.beforeView.application.publicView.clock = 0)
    (message : Message Player (WitnessedPacket nativeGraph))
    (emitted : entry.emitted = some message)
    (named : message.payload.call.event? nativeGraph = some resolution) :
    ∃ accepted, (message.id, accepted) ∈ next.receipts := by
  have recallEq := app.environmentStep_recall control.execution next command moved
  rw [recallEq] at member
  by_cases included : 4 ≤ control.execution.environmentRecall.length
  · obtain ⟨accepted, receipt⟩ := phase.receipt0 included entry member zero message emitted named
    have persisted := app.environmentStep_receipts_prefix control.execution next command moved
    exact ⟨accepted, persisted.subset receipt⟩
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have stage : control.execution.environmentRecall.length = 3 := by omega
  have oneEntry : (control.execution.recall owner).length = 1 := by
    rw [phase.recallCount, stage, idle]
    rfl
  obtain ⟨only, onlyEq⟩ := List.length_eq_one_iff.mp oneEntry
  have same : entry = only := by simpa only [onlyEq, List.mem_singleton] using member
  subst entry
  obtain ⟨_, origins, recalled, retained, sound⟩ :=
    roster_trace_facts setup leaks horizon scheduler trace
  by_cases published : message.id ∈ control.execution.network.ledger.map Message.id
  · obtain ⟨accepted, receipt⟩ := receipt_of_published control.execution sound _ published
    have persisted := app.environmentStep_receipts_prefix control.execution next command moved
    exact ⟨accepted, persisted.subset receipt⟩
  have authored : message.sender = owner := Subsingleton.elim _ _
  obtain ⟨pending, latestEq⟩ := reactiveLatest_sole (runtime setup) leaks control.execution origins
    recalled retained resolution owner [] [] only message onlyEq emitted authored named
    (by simp) published
  have chosen : command = .include message.id := by
    have actual := (PMF.mem_support_pure_iff _ _).mp selected
    simpa only [stage, stageCommand, latest, latestEq] using actual
  rw [chosen] at moved
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
  cases (PMF.mem_support_pure_iff _ _).mp moved
  exact includePending_receipt_of_pending (runtime setup) leaks control.execution message pending

theorem phase_environment (control : app.Control) (phase : Phase control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (idle : control.actor = none) (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support) :
    Phase ⟨remaining, command.actor? app, next⟩ := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have beforeEnd : control.execution.environmentRecall.length < horizon := by
    have budget := phase.budget
    rw [counted] at budget
    omega
  have budget : remaining + next.environmentRecall.length = horizon := by
    have total := phase.budget
    rw [counted] at total
    omega
  have prefixFacts := phase_environment_prefix control phase next command selected moved
  have recallEq := app.environmentStep_recall control.execution next command moved
  have chosen : command = stageCommand control.execution.environmentRecall.length
      (control.execution.observeEnvironment app) := (PMF.mem_support_pure_iff _ _).mp selected
  refine {
    budget := budget
    bounded := by
      change next.environmentRecall.length ≤ horizon
      omega
    clock := phase_environment_clock control phase next command selected moved beforeEnd
    prefix0 := by
      change next.environmentRecall.length = 0 → _
      intro impossible
      omega
    prefix1 := prefixFacts.1
    laterPrefix := prefixFacts.2
    terminalPrefix := phase_environment_terminal control phase next command selected moved
    entered := phase_environment_entered control phase trace next command selected moved beforeEnd
    opportunity := phase_environment_opportunity control phase next command selected moved
    activation := ?_
    recallCount := ?_
    responseClock := ?_
    receipt0 := phase_environment_receipt0 control phase trace idle next command selected moved }
  · intro active
    rw [chosen] at active
    rw [length]
    generalize stageEq : control.execution.environmentRecall.length = stage at beforeEnd active ⊢
    change stage < 10 at beforeEnd
    interval_cases stage <;> simp only [stageCommand] at active
    all_goals first
      | (solve | simp [latest_actor_none] at active)
      | (solve | simp [latestWithhold_actor_none] at active)
      | simp_all [ReactiveApplication.Command.actor?]
  · rw [recallEq, phase.recallCount, idle, length, chosen]
    generalize stageEq : control.execution.environmentRecall.length = stage at beforeEnd ⊢
    change stage < 10 at beforeEnd
    interval_cases stage <;> simp only [stageCommand]
    all_goals first
      | (rw [latest_actor_none]; rfl)
      | (rw [latestWithhold_actor_none]; rfl)
      | rfl
  · intro entry member
    rw [recallEq] at member
    exact phase.responseClock entry member

theorem phase_transition (before after : app.ProtocolState)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace before)
    (valid : phaseInvariant before) (joint : Player → Option app.Action)
    (reached : after ∈ (app.transition (initialLaw setup) horizon scheduler before joint).support) :
    phaseInvariant after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact phase_initial state supported
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact phase_respond _ valid who rfl _
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, realized⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ realized
              exact phase_environment _ valid trace rfl remaining rfl next command selected moved

theorem phase_history : ∀ {state}
    (_trace : (app.protocol (initialLaw setup) horizon scheduler).Trace state), phaseInvariant state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      phase_transition _ _ prior (phase_history prior) joint reached

theorem owned_event (event : nativeGraph.EventId) (who : Player)
    (owned : nativeGraph.actor? event = some who) : event = resolution := by
  change Fin 3 at event
  fin_cases event
  · change none = some who at owned
    contradiction
  · change none = some who at owned
    contradiction
  · rfl

theorem stageClock_le_three (stage : Nat) : stageClock stage ≤ 3 := by
  unfold stageClock
  split_ifs <;> omega

theorem opportunity : Opportunity (runtime setup) leaks (initialLaw setup) horizon scheduler
    delay := by
  intro control trace event who entered owned ready activated due
  have eventEq := owned_event event who owned
  subst event
  have whoEq : who = owner := Subsingleton.elim _ _
  subst who
  have phase : Phase control := phase_history trace
  have stage : 3 ≤ control.execution.environmentRecall.length := by
    have clockEq := phase.clock
    change entered + 0 < control.execution.application.clock at due
    by_contra earlier
    have zero : stageClock control.execution.environmentRecall.length = 0 := by
      unfold stageClock
      rw [ite_eq_left (by omega)]
    rw [zero] at clockEq
    omega
  rcases phase.laterPrefix (by omega) with current | complete
  · have started := phase.entered current
    have same : entered = 0 := by simpa only [started, Option.some.injEq] using activated.symm
    subst entered
    exact phase.opportunity stage current
  · have semanticReady := (EventGraphRuntime.State.publicView_eventReady _ resolution).mp ready
    exact (semanticReady.1 ((complete.2 resolution).mpr (by decide))).elim

theorem protectedInclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon
    scheduler bound := by
  intro control trace event who owned earlier later entry message recalled emitted authored named
    _ready _sole _unfinished due
  have eventEq := owned_event event who owned
  subst event
  have whoEq : who = owner := Subsingleton.elim _ _
  rw [whoEq] at owned recalled authored
  have phase : Phase control := phase_history trace
  have member : entry ∈ control.execution.recall owner := by rw [recalled]; simp
  have clockBound : control.execution.application.clock ≤ 3 := by
    rw [phase.clock]
    exact stageClock_le_three _
  have zero : entry.beforeView.application.publicView.clock = 0 := by
    rcases phase.responseClock entry member with zero | one
    · exact zero
    · change entry.beforeView.application.publicView.clock + 2 <
        control.execution.application.clock at due
      omega
  have included : 4 ≤ control.execution.environmentRecall.length := by
    change entry.beforeView.application.publicView.clock + 2 <
      control.execution.application.clock at due
    by_contra early
    have clockZero : control.execution.application.clock = 0 := by
      rw [phase.clock]
      unfold stageClock
      rw [ite_eq_left (by omega)]
    omega
  exact phase.receipt0 included entry member zero message emitted named

theorem completesPlay :
    CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler := by
  intro control trace terminal
  have phase : Phase control := phase_history trace
  obtain ⟨ended, _⟩ := terminal
  have finalStage : control.execution.environmentRecall.length = horizon := by
    have budget := phase.budget
    rw [ended] at budget
    omega
  exact (phase.terminalPrefix finalStage).terminal

/-- All three scheduler obligations quantify over the complete raw protocol:
wrong-event packets, malformed content and fresh retries remain allowed. -/
theorem contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
    delay bound := ⟨opportunity, protectedInclusion, completesPlay⟩

end Vegas.LateResolutionService

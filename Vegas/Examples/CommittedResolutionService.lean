/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterAsync
import Vegas.Game.SourceServiceCanonicalSerial
import Vegas.Game.SourceServiceAudit
import Vegas.Expr.Simple
import GameTheoryExtensions.Math.Probability.Uniform
import Interaction.ReactiveScheduleClock
import Interaction.ReactiveServiceInvariant
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.EventOpponentFrame

/-! A concrete public controller with a late Alice opportunity. -/

noncomputable section

namespace Vegas.Examples.CommittedResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol

abbrev Player := Fin 2
abbrev alice : Player := 0
abbrev bob : Player := 1

def initialCtx : SourceCtx Player simpleExpr :=
  [(0, .commitment alice .bool), (1, .commitment bob .bool)]

def program : SourceProgram Player simpleExpr initialCtx {0, 1} :=
  .sample 2 (payload := .bool) (by decide) (.weighted (.pure true)) <|
  .reveal 3 alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 4 bob 1 (by decide) (.there (.there (.there .here))) (by decide) <|
  .ret []

def sourceInitial (high : Bool) : State simpleExpr initialCtx :=
  Env.cons (.success high) <| Env.cons (.success true) <| Env.empty _

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := mix (1 / 4) (by norm_num) (by norm_num)
    (PMF.pure (sourceInitial true)) (PMF.pure (sourceInitial false))
  obligations := {0, 1}
  program := program
  accounts := rfl

abbrev nativeGraph := graph setup
abbrev sampleEvent : nativeGraph.EventId := ⟨0, by decide⟩
abbrev aliceEvent : nativeGraph.EventId := ⟨1, by decide⟩
abbrev bobEvent : nativeGraph.EventId := ⟨2, by decide⟩

def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun _ _ => PMF.pure ∅

abbrev app := application setup leaks

def stageChoice (position : Nat) (view : app.EnvironmentView) : PMF app.Command :=
  match position with
  | 0 => PMF.pure (.application (.executeSample sampleEvent))
  | 1 => PMF.pure (.activate alice)
  | 2 => PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view)
  | 3 | 6 => PMF.pure (.application .advanceClock)
  | 4 => PMF.pure (.activate alice)
  | 5 => mix (3 / 4) (by norm_num) (by norm_num)
      (PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view)) (PMF.pure .wait)
  | 7 => PMF.pure (.application (.expire aliceEvent))
  | 8 => PMF.pure (.activate alice)
  | 9 => PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view)
  | 10 => PMF.pure (.activate bob)
  | 11 => PMF.pure ((runtime setup).reactiveLatest leaks bobEvent bob view)
  | 12 | 13 | 14 => PMF.pure (.application .advanceClock)
  | 15 => PMF.pure (.application (.expire bobEvent))
  | _ => PMF.pure .wait

def scheduler : app.Scheduler := fun past view =>
  stageChoice past.length view

def horizon : Nat := 16
def delay (event : nativeGraph.EventId) : Nat := if event = bobEvent then 2 else 0
def bound (event : nativeGraph.EventId) : Nat := if event = aliceEvent then 1 else 0

theorem timely : AsyncTimely (runtime setup) delay bound := by
  intro event owned
  change Fin 3 at event
  fin_cases event
  · change false = true at owned
    contradiction
  · change 0 + 1 < 2
    decide
  · change 2 + 0 < 3
    decide

instance finiteInitial : setup.FiniteInitialLaw where
  support_finite := by
    apply ((Set.finite_singleton (sourceInitial true)).union
      (Set.finite_singleton (sourceInitial false))).subset
    simpa only [setup, PMF.support_pure] using support_mix_subset (1 / 4) (by norm_num)
      (by norm_num) (PMF.pure (sourceInitial true)) (PMF.pure (sourceInitial false))

instance finiteLeaks : leaks.FiniteSupport where
  support_finite := by intro who pending; simp [leaks]

private theorem stageChoice_finite (position : Nat) (view : app.EnvironmentView) :
    (stageChoice position view).support.Finite := by
  unfold stageChoice
  split <;> try simp only [PMF.support_pure, Set.finite_singleton]
  apply ((Set.finite_singleton _).union (Set.finite_singleton _)).subset
  simpa only [PMF.support_pure] using support_mix_subset (3 / 4)
    (by norm_num) (by norm_num)
    (PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view)) (PMF.pure .wait)

instance finiteNature : app.FiniteNature (initialLaw setup) scheduler where
  initial_finite := by
    rw [initialLaw, PMF.support_map]
    exact setup.initialLaw_support_finite.image _
  scheduler_finite past view := stageChoice_finite _ _

private def actorSchedule : List (Option Player) :=
  [none, some alice, none, none, some alice, none, none, none,
    some alice, none, some bob, none, none, none, none, none]

private def stageTicks : Nat → Nat
  | 3 | 6 | 12 | 13 | 14 => 1
  | _ => 0

private theorem latest_facts (event : nativeGraph.EventId) (owner : Player)
    (view : app.EnvironmentView) :
    ((runtime setup).reactiveLatest leaks event owner view).actor? app = none ∧
      (runtime setup).reactiveTicks leaks
        ((runtime setup).reactiveLatest leaks event owner view) = 0 := by
  rcases (runtime setup).reactiveLatest_wait_or_owned leaks event owner view with
    idle | ⟨id, _, included⟩
  · rw [idle]; exact ⟨rfl, rfl⟩
  · rw [included]; exact ⟨rfl, rfl⟩

private theorem scheduler_facts (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command) (selected : command ∈ (scheduler past view).support) :
    command.actor? app = (actorSchedule[past.length]?).join ∧
      (runtime setup).reactiveTicks leaks command = stageTicks past.length := by
  change command ∈ (stageChoice past.length view).support at selected
  generalize counted : past.length = position at selected ⊢
  by_cases inside : position < 16
  · interval_cases position <;>
      simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    all_goals
      try
        subst command
        first | exact latest_facts _ _ _ | exact ⟨rfl, rfl⟩
    have choices := support_mix_subset (3 / 4) (by norm_num) (by norm_num)
      (PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view))
      (PMF.pure (.wait : app.Command)) selected
    rcases choices with first | second
    · cases (PMF.mem_support_pure_iff _ _).mp first
      exact latest_facts _ _ _
    · cases (PMF.mem_support_pure_iff _ _).mp second
      exact ⟨rfl, rfl⟩
  · have outside : 16 ≤ position := by omega
    have idle : stageChoice position view = PMF.pure .wait := by
      unfold stageChoice; split <;> first | omega | rfl
    have noTick : stageTicks position = 0 := by
      unfold stageTicks; split <;> omega
    have lookup : actorSchedule[position]? = none :=
      List.getElem?_eq_none (by change 16 ≤ position; omega)
    rw [idle, PMF.mem_support_pure_iff] at selected
    subst command
    rw [lookup, noTick]
    exact ⟨rfl, rfl⟩

private def clockAt (position : Nat) : Nat :=
  ((List.range position).map stageTicks).sum

private def PhaseClock (execution : app.Execution) : Prop :=
  ∃ inputs, execution.application.Invariant inputs ∧
    execution.application.clock = clockAt execution.environmentRecall.length

private theorem alice_actor_unique (event : nativeGraph.EventId)
    (owned : nativeGraph.actor? event = some alice) : event = aliceEvent := by
  change Fin 3 at event
  fin_cases event
  · change none = some alice at owned
    cases owned
  · rfl
  · change some bob = some alice at owned
    norm_num [alice, bob] at owned

private theorem alice_closed_include (execution : app.Execution) (id : MessageId Player)
    (owned : id.1 = alice) (closed : aliceEvent ∈ execution.application.config.cut.completed) :
    (execution.includePending app id).application = execution.application := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => rfl
  | some message =>
      have identified : message.id = id := by
        change execution.network.pending.find? (fun packet => decide (packet.id = id)) =
          some message at found
        have matched := List.find?_some found
        exact of_decide_eq_true matched
      have authored : message.sender = alice := (congrArg Prod.fst identified).trans owned
      have rejected : app.handle execution.application message = none := by
        cases accepted : app.handle execution.application message with
        | none => rfl
        | some next =>
            have rawAccepted := reactiveHandle_call accepted
            obtain ⟨event, addressed, actor⟩ :=
              handle_event_actor (runtime setup) execution.application next
                ⟨message.id, message.payload.call⟩ rawAccepted
            change nativeGraph.actor? event = some message.sender at actor
            rw [authored] at actor
            have same := alice_actor_unique event actor
            subst event
            rw [handle_eq_none_of_completed (runtime setup) execution.application
              ⟨message.id, message.payload.call⟩ aliceEvent addressed closed] at rawAccepted
            cases rawAccepted
      simp only [rejected, Option.getD_none]

private theorem alice_closed_latest (execution next : app.Execution)
    (closed : aliceEvent ∈ execution.application.config.cut.completed)
    (reached : next ∈ (execution.environmentStep app
      ((runtime setup).reactiveLatest leaks aliceEvent alice
        (execution.observeEnvironment app))).support) :
    next.application = execution.application := by
  rcases (runtime setup).reactiveLatest_wait_or_owned leaks aliceEvent alice
      (execution.observeEnvironment app) with idle | ⟨id, owned, included⟩
  · rw [idle] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    rfl
  · rw [included] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    exact alice_closed_include execution id owned closed

private theorem latest_graphStep (execution next : app.Execution)
    (event : nativeGraph.EventId) (owner : Player)
    (reached : next ∈ (execution.environmentStep app
      ((runtime setup).reactiveLatest leaks event owner
        (execution.observeEnvironment app))).support) :
    GraphStep execution.application next.application := by
  rcases (runtime setup).reactiveLatest_wait_or_owned leaks event owner
      (execution.observeEnvironment app) with idle | ⟨id, _, included⟩
  · rw [idle] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    exact .refl _
  · rw [included] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    exact graphStep_includePending (runtime setup) leaks execution id

private theorem activated_absent (inputs : nativeGraph.Inputs)
    (state : EventGraphRuntime.State nativeGraph)
    (invariant : state.Invariant inputs) (event : nativeGraph.EventId)
    (completed : event ∈ state.config.cut.completed) : state.activatedAt event = none := by
  cases activated : state.activatedAt event with
  | none => rfl
  | some entered =>
      have ready := ((invariant.activated_iff event).mp (by rw [activated]; rfl)).1
      exact (ready.1 completed).elim

private def cutSchedule (position : Nat) (cut : nativeGraph.order.Cut) : Prop :=
  if position = 0 then cut.IsPrefix 0 else
  if position ≤ 2 then cut.IsPrefix 1 else
  if position ≤ 7 then cut.IsPrefix 1 ∨ cut.IsPrefix 2 else
  if position ≤ 11 then cut.IsPrefix 2 else
  if position ≤ 15 then cut.IsPrefix 2 ∨ cut.IsPrefix 3 else cut.IsPrefix 3

private def TimeBounds (state : EventGraphRuntime.State nativeGraph) : Prop :=
  (∀ entered, state.activatedAt aliceEvent = some entered → entered = 0) ∧
    (∀ entered, state.activatedAt bobEvent = some entered → entered ≤ 2)

private def ActivationLog (execution : app.Execution) : Prop :=
  (2 ≤ execution.environmentRecall.length →
    OwnerActivatedSince (runtime setup) leaks execution.environmentRecall aliceEvent alice 0) ∧
  (11 ≤ execution.environmentRecall.length → ∀ entered,
    execution.application.activatedAt bobEvent = some entered →
    OwnerActivatedSince (runtime setup) leaks execution.environmentRecall bobEvent bob entered)

private theorem record_activation (execution next : app.Execution) (event : nativeGraph.EventId)
    (owner : Player) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (ready : execution.application.config.cut.Ready event)
    (reached : next ∈ (execution.environmentStep app (.activate owner)).support) :
    OwnerActivatedSince (runtime setup) leaks next.environmentRecall event owner entered := by
  rw [environmentStep_recall_append execution next _ reached]
  refine ⟨⟨execution.observeEnvironment app, .activate owner⟩, by simp, rfl, activated, ?_⟩
  exact (State.publicView_eventReady _ event).mpr ready

private def CutPhase (execution : app.Execution) : Prop :=
  PhaseClock execution ∧ cutSchedule execution.environmentRecall.length
    execution.application.config.cut ∧ TimeBounds execution.application ∧ ActivationLog execution

private theorem timeBounds_closed (inputs : nativeGraph.Inputs)
    (state : EventGraphRuntime.State nativeGraph) (invariant : state.Invariant inputs)
    (rank : Nat) (ordered : state.config.cut.IsPrefix rank) (two : 2 ≤ rank)
    (clocked : state.clock ≤ 2) : TimeBounds state := by
  constructor
  · intro entered activated
    have absent := activated_absent inputs state invariant aliceEvent
      ((ordered.2 aliceEvent).mpr (by change 1 < rank; omega))
    rw [absent] at activated
    cases activated
  · intro entered activated
    exact (invariant.activated_le bobEvent entered activated).trans clocked

private theorem alice_latest_phase (execution next : app.Execution)
    (valid : PhaseClock execution) (bounds : TimeBounds execution.application)
    (ordered : execution.application.config.cut.IsPrefix 1 ∨
      execution.application.config.cut.IsPrefix 2)
    (clocked : execution.application.clock ≤ 2)
    (reached : next ∈ (execution.environmentStep app
      ((runtime setup).reactiveLatest leaks aliceEvent alice
        (execution.observeEnvironment app))).support) :
    (next.application.config.cut.IsPrefix 1 ∨ next.application.config.cut.IsPrefix 2) ∧
      TimeBounds next.application := by
  obtain ⟨inputs, invariant, _⟩ := valid
  have progress := (runtime setup).reactive_environment_progress leaks inputs execution next _
    invariant reached
  have nextClock : next.application.clock = execution.application.clock := by
    simpa only [(latest_facts _ _ _).2, Nat.add_zero] using progress.clock
  rcases ordered with current | done
  · rcases (latest_graphStep execution next aliceEvent alice reached).prefix setup aliceEvent
      current with ⟨same, _, activated⟩ | ⟨done, _, _⟩
    · exact ⟨Or.inl (same ▸ current), by rw [TimeBounds, activated]; exact bounds⟩
    · exact ⟨Or.inr done, timeBounds_closed inputs next.application progress.invariant 2 done
        (by omega) (nextClock ▸ clocked)⟩
  · have unchanged := alice_closed_latest execution next
      ((done.2 aliceEvent).mpr (by decide)) reached
    rw [unchanged]
    exact ⟨Or.inr done, bounds⟩

private theorem expire_phase (execution next : app.Execution) (event : nativeGraph.EventId)
    (owner : Player) (owned : nativeGraph.actor? event = some owner)
    (valid : PhaseClock execution)
    (ordered : execution.application.config.cut.IsPrefix event.val ∨
      execution.application.config.cut.IsPrefix (event.val + 1))
    (due : ∀ entered, execution.application.activatedAt event = some entered →
      (runtime setup).deadline event ≤ execution.application.clock - entered)
    (reached : next ∈ (execution.environmentStep app (.application (.expire event))).support) :
    next.application.config.cut.IsPrefix (event.val + 1) := by
  obtain ⟨inputs, invariant, _⟩ := valid
  obtain ⟨member, _⟩ := applicationStep_facts execution next (.expire event) reached
  rcases ordered with current | done
  · have ready := (ready_iff_rank setup _ event.val current event).mpr rfl
    obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
      (by rw [owned]; rfl)
    obtain ⟨cutEq, _, _⟩ := expire_completes (runtime setup) execution.application next.application
      event owner owned ready entered activated (due entered activated) member
    rw [cutEq]
    exact current.complete_at event ready rfl
  · have unready : ¬execution.application.config.cut.Ready event := fun ready =>
      ready.1 ((done.2 event).mpr (Nat.lt_succ_self _))
    rw [environmentStep_expire_of_not_ready (runtime setup) _ event unready,
      PMF.mem_support_pure_iff] at member
    rw [member]
    exact done

private theorem passive_state (execution next : app.Execution) (command : app.Command)
    (passive : command = .wait ∨ (∃ who, command = .activate who) ∨
      command = .application .advanceClock)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.application.config = execution.application.config ∧
      next.application.activatedAt = execution.application.activatedAt := by
  rcases passive with idle | ⟨who, activated⟩ | ticked
  · rw [idle] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    exact ⟨rfl, rfl⟩
  · rw [activated] at reached
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
    obtain ⟨sampled, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact ⟨rfl, rfl⟩
  · rw [ticked] at reached
    obtain ⟨member, _⟩ := applicationStep_facts execution next .advanceClock reached
    simp only [environmentStep, PMF.mem_support_pure_iff] at member
    rw [member]
    exact ⟨rfl, rfl⟩

private theorem timeBounds_finished (inputs : nativeGraph.Inputs)
    (state : EventGraphRuntime.State nativeGraph) (invariant : state.Invariant inputs)
    (ordered : state.config.cut.IsPrefix 3) : TimeBounds state := by
  constructor <;> intro entered activated
  · rw [activated_absent inputs state invariant aliceEvent
      ((ordered.2 aliceEvent).mpr (by decide))] at activated
    cases activated
  · rw [activated_absent inputs state invariant bobEvent
      ((ordered.2 bobEvent).mpr (by decide))] at activated
    cases activated

private theorem cutPhase_invariant : app.ServiceInvariant scheduler CutPhase where
  respond execution who action valid := by
    obtain ⟨clocked, ordered, bounds, activatedLog⟩ := valid
    obtain ⟨same, visible⟩ :=
      (runtime setup).reactive_respond_application leaks execution who action
    have activated := congrArg PublicView.activatedAt visible
    dsimp only [EventGraphRuntime.State.publicView] at activated
    have progress := (runtime setup).reactive_respond_progress leaks clocked.choose
      execution who action clocked.choose_spec.1
    refine ⟨⟨clocked.choose, progress.invariant, ?_⟩, ?_, ?_, ?_⟩
    · rw [progress.clock, app.respond_environmentRecall, Nat.add_zero]
      exact clocked.choose_spec.2
    · rw [app.respond_environmentRecall, same]; exact ordered
    · rw [TimeBounds, activated]; exact bounds
    · rw [ActivationLog, app.respond_environmentRecall, activated]; exact activatedLog
  environment execution next command valid selected reached := by
    obtain ⟨clocked, ordered, bounds, activatedLog⟩ := valid
    have originalClocked := clocked
    obtain ⟨inputs, invariant, oldClock⟩ := clocked
    have progress := (runtime setup).reactive_environment_progress leaks inputs execution next
      command invariant reached
    have appended := environmentStep_recall_append execution next command reached
    have nextValid : PhaseClock next := ⟨inputs, progress.invariant, by
      rw [progress.clock, oldClock, (scheduler_facts _ _ command selected).2, appended,
        List.length_append, List.length_singleton]
      simp [clockAt, List.range_succ]⟩
    have length : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
      rw [appended, List.length_append, List.length_singleton]
    have carryA (old : 2 ≤ execution.environmentRecall.length) :
        OwnerActivatedSince (runtime setup) leaks next.environmentRecall aliceEvent alice 0 := by
      rw [appended]; exact ownerActivatedSince_append (activatedLog.1 old) _
    have carried (same : next.application.activatedAt = execution.application.activatedAt)
        (notA : execution.environmentRecall.length ≠ 1)
        (notB : execution.environmentRecall.length ≠ 10) : ActivationLog next := by
      constructor
      · intro late; exact carryA (by omega)
      · intro late entered activated
        rw [same] at activated
        rw [appended]; exact ownerActivatedSince_append (activatedLog.2 (by omega) _ activated) _
    have beforeBob (old : 2 ≤ execution.environmentRecall.length)
        (early : next.environmentRecall.length < 11) : ActivationLog next :=
      ⟨fun _ => carryA old, fun late => False.elim (by omega)⟩
    refine ⟨nextValid, ?_⟩
    rw [length]
    change command ∈ (stageChoice execution.environmentRecall.length
      (execution.observeEnvironment app)).support at selected
    generalize located : execution.environmentRecall.length = position
      at selected ordered oldClock ⊢
    have newClock := nextValid.choose_spec.2
    rw [length, located] at newClock
    by_cases inside : position < 16
    · interval_cases position <;>
        simp only [stageChoice, PMF.mem_support_pure_iff] at selected
      all_goals norm_num [cutSchedule] at ordered ⊢
      case «3» | «4» | «6» | «8» | «12» | «13» | «14» =>
        subst command
        obtain ⟨same, activated⟩ := passive_state execution next _ (by
          first | exact Or.inl rfl | exact Or.inr (Or.inl ⟨_, rfl⟩) |
            exact Or.inr (Or.inr rfl)) reached
        refine ⟨same ▸ ordered, ?_, carried activated (by omega) (by omega)⟩
        rw [TimeBounds, activated]; exact bounds
      case «1» | «10» =>
        subst command
        obtain ⟨same, unchanged⟩ := passive_state execution next _
          (Or.inr (Or.inl ⟨_, rfl⟩)) reached
        refine ⟨same ▸ ordered, ?_, ?_⟩
        · rw [TimeBounds, unchanged]; exact bounds
        · constructor
          · intro late
            first
            | exact carryA (by omega)
            | have ready := (ready_iff_rank setup _ 1 ordered aliceEvent).mpr rfl
              obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor
                aliceEvent ready rfl
              rw [bounds.1 entered activated] at activated
              exact record_activation execution next aliceEvent alice 0 activated ready reached
          · intro late entered activated
            first
            | exact False.elim (by omega)
            | rw [unchanged] at activated
              exact record_activation execution next bobEvent bob entered activated
                ((ready_iff_rank setup _ 2 ordered bobEvent).mpr rfl) reached
      case «0» =>
        subst command
        have ready := (ready_iff_rank setup _ 0 ordered sampleEvent).mpr rfl
        obtain ⟨member, _⟩ :=
          applicationStep_facts execution next (.executeSample sampleEvent) reached
        obtain ⟨cutEq, _, _⟩ := executeSample_completes (runtime setup) execution.application
          next.application sampleEvent (by rfl) ready member
        refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
        · rw [cutEq]; exact ordered.complete_at sampleEvent ready rfl
        · intro entered activated
          have upper := progress.invariant.activated_le aliceEvent entered activated
          change next.application.clock = 0 at newClock
          omega
        · intro entered activated
          have upper := progress.invariant.activated_le bobEvent entered activated
          change next.application.clock = 0 at newClock
          omega
        all_goals intro late; rw [length, located] at late; omega
      case «2» =>
        subst command
        obtain ⟨cut, timers⟩ := alice_latest_phase execution next originalClocked bounds
          (Or.inl ordered) (by change execution.application.clock = 0 at oldClock; omega) reached
        exact ⟨cut, timers, beforeBob (by omega) (by omega)⟩
      case «5» =>
        have choices := support_mix_subset (3 / 4) (by norm_num) (by norm_num)
          (PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice
            (execution.observeEnvironment app))) (PMF.pure (.wait : app.Command)) selected
        rcases choices with included | idle
        · cases (PMF.mem_support_pure_iff _ _).mp included
          obtain ⟨cut, timers⟩ := alice_latest_phase execution next originalClocked bounds ordered
            (by change execution.application.clock = 1 at oldClock; omega) reached
          exact ⟨cut, timers, beforeBob (by omega) (by omega)⟩
        · cases (PMF.mem_support_pure_iff _ _).mp idle
          obtain ⟨same, activated⟩ := passive_state execution next _ (Or.inl rfl) reached
          refine ⟨same ▸ ordered, ?_, beforeBob (by omega) (by omega)⟩
          rw [TimeBounds, activated]; exact bounds
      case «7» =>
        subst command
        have done := expire_phase execution next aliceEvent alice rfl originalClocked
          ordered (by
            intro entered activated
            have zero := bounds.1 entered activated
            change execution.application.clock = 2 at oldClock
            change 2 ≤ execution.application.clock - entered
            omega) reached
        exact ⟨done, timeBounds_closed inputs next.application progress.invariant 2 done
          (by omega) (by change next.application.clock = 2 at newClock; omega),
          beforeBob (by omega) (by omega)⟩
      case «9» =>
        subst command
        have same := alice_closed_latest execution next
          ((ordered.2 aliceEvent).mpr (by decide)) reached
        refine ⟨same ▸ ordered, same ▸ bounds, beforeBob (by omega) (by omega)⟩
      case «11» =>
        subst command
        rcases (latest_graphStep execution next bobEvent bob reached).prefix setup bobEvent
            ordered with ⟨same, _, activatedEq⟩ | ⟨done, _, _⟩
        · have current : next.application.config.cut.IsPrefix 2 := same ▸ ordered
          exact ⟨Or.inl current, timeBounds_closed inputs next.application progress.invariant 2
            current (by omega) (by change next.application.clock = 2 at newClock; omega),
            carried activatedEq (by omega) (by omega)⟩
        · refine ⟨Or.inr done, timeBounds_finished inputs next.application progress.invariant done,
            fun _ => carryA (by omega), ?_⟩
          intro _ entered activated
          rw [activated_absent inputs next.application progress.invariant bobEvent
            ((done.2 bobEvent).mpr (by decide))] at activated
          cases activated
      case «15» =>
        subst command
        have done := expire_phase execution next bobEvent bob rfl originalClocked
          ordered (by
            intro entered activated
            have upper := bounds.2 entered activated
            change execution.application.clock = 5 at oldClock
            change 3 ≤ execution.application.clock - entered
            omega) reached
        refine ⟨done, timeBounds_finished inputs next.application progress.invariant done,
          fun _ => carryA (by omega), ?_⟩
        intro _ entered activated
        rw [activated_absent inputs next.application progress.invariant bobEvent
          ((done.2 bobEvent).mpr (by decide))] at activated
        cases activated
    · have outside : 16 ≤ position := by omega
      have idle : stageChoice position (execution.observeEnvironment app) = PMF.pure .wait := by
        unfold stageChoice; split <;> first | omega | rfl
      rw [idle, PMF.mem_support_pure_iff] at selected
      subst command
      obtain ⟨same, activated⟩ := passive_state execution next _ (Or.inl rfl) reached
      have old : execution.application.config.cut.IsPrefix 3 := by
        simpa [cutSchedule, show position ≠ 0 by omega, show ¬position ≤ 2 by omega,
          show ¬position ≤ 7 by omega, show ¬position ≤ 11 by omega,
          show ¬position ≤ 15 by omega] using ordered
      have nextCut : next.application.config.cut.IsPrefix 3 := same ▸ old
      refine ⟨?_, ?_, carried activated (by omega) (by omega)⟩
      · simpa [cutSchedule, show position + 1 ≠ 0 by omega,
          show ¬position + 1 ≤ 2 by omega, show ¬position + 1 ≤ 7 by omega,
          show ¬position + 1 ≤ 11 by omega, show ¬position + 1 ≤ 15 by omega] using nextCut
      · rw [TimeBounds, activated]; exact bounds

private theorem cut_initial (state : app.State) (supported : state ∈ (initialLaw setup).support) :
    CutPhase (ReactiveApplication.Execution.initial app state) := by
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  refine ⟨⟨setup.eventInputs initial, State.initial_invariant _, rfl⟩,
    EventOrder.Cut.empty_isPrefix _, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro entered activated
    change none = some entered at activated
    cases activated
  · intro entered activated
    change none = some entered at activated
    cases activated
  all_goals intro late; change _ ≤ 0 at late; omega

private theorem cut_history (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control)) :
    CutPhase control.execution :=
  cutPhase_invariant.history (initialLaw setup) horizon cut_initial trace

private def serveCursor (who : Player) : Nat := if who = alice then 2 else 11
private def serveClock (who : Player) : Nat := if who = alice then 0 else 2
private def serveEvent (who : Player) : nativeGraph.EventId :=
  if who = alice then aliceEvent else bobEvent

private theorem response_origin (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who) :
    (serveClock who ≤ control.execution.application.clock ∧
      (who = bob → control.execution.application.clock = serveClock who)) ∧
      (control.execution.application.clock = serveClock who →
        control.execution.environmentRecall.length = serveCursor who) ∧
      (control.execution.environmentRecall.length ≤ serveCursor who →
        (control.execution.recall who).length = 0) := by
  obtain ⟨position, located, found, counts, _⟩ := app.scheduled_decision_counts
    (initialLaw setup) horizon scheduler actorSchedule
    (fun past view command selected => (scheduler_facts past view command selected).1)
    who control trace active
  have inside : position < 16 := List.getElem?_eq_some_iff.mp found |>.1
  have clocked := (cut_history control trace).1.choose_spec.2
  rw [located] at clocked
  have own := counts who
  interval_cases position <;> norm_num [actorSchedule] at found
  all_goals
    subst who
    first
    | change (control.execution.recall alice).length + 1 = 1 at own
    | change (control.execution.recall alice).length + 1 = 2 at own
    | change (control.execution.recall alice).length + 1 = 3 at own
    | change (control.execution.recall bob).length + 1 = 1 at own
    first | change control.execution.application.clock = 0 at clocked |
      change control.execution.application.clock = 1 at clocked |
      change control.execution.application.clock = 2 at clocked
    dsimp [alice, bob] at own
    dsimp [serveClock, serveCursor, alice, bob]
    constructor
    · constructor
      · omega
      · intro same; first | exact clocked | norm_num [alice, bob] at same
    · constructor <;> intro condition <;> omega

private theorem serve_entry (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (next : app.Execution) (who : Player) (entry : app.PlayerEntry)
    (message : Message Player (WitnessedPacket nativeGraph))
    (small : (control.execution.recall who).length ≤ 1)
    (member : entry ∈ control.execution.recall who) (emitted : entry.emitted = some message)
    (authored : message.sender = who) (addressed : message.payload.call.event? nativeGraph =
      some (serveEvent who))
    (reached : next ∈ (control.execution.environmentStep app
      ((runtime setup).reactiveLatest leaks (serveEvent who) who
        (control.execution.observeEnvironment app))).support) :
    ∃ accepted, (message.id, accepted) ∈ next.receipts := by
  obtain ⟨head, singleton⟩ := List.length_eq_one_iff.mp
    (show (control.execution.recall who).length = 1 from
      Nat.le_antisymm small (List.length_pos_of_mem member))
  have same : entry = head := by simpa [singleton] using member
  subst head
  obtain ⟨_, origins, recalled, retained, sound⟩ := roster_trace_facts setup leaks _ _ trace
  by_cases published : message.id ∈ control.execution.network.ledger.map Message.id
  · obtain ⟨accepted, caught⟩ := receipt_of_published control.execution sound _ published
    exact ⟨accepted, (app.environmentStep_receipts_prefix _ _ _ reached).subset caught⟩
  · obtain ⟨pending, latest⟩ := reactiveLatest_sole (runtime setup) leaks control.execution
      origins recalled retained (serveEvent who) who [] [] entry message
      (by simpa using singleton) emitted authored addressed (by simp) published
    rw [latest] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
    cases (PMF.mem_support_pure_iff _ _).mp reached
    exact includePending_receipt_of_pending (runtime setup) leaks _ _ pending

private def PacketService (execution : app.Execution) : Prop := ∀ who,
  (execution.environmentRecall.length ≤ serveCursor who → (execution.recall who).length ≤ 1) ∧
  (∀ entry ∈ execution.recall who,
    serveClock who ≤ entry.beforeView.application.publicView.clock ∧
      (who = bob → entry.beforeView.application.publicView.clock = serveClock who)) ∧
  (∀ entry ∈ execution.recall who, ∀ message, entry.emitted = some message →
    message.sender = who → message.payload.call.event? nativeGraph = some (serveEvent who) →
    entry.beforeView.application.publicView.clock = serveClock who →
    serveCursor who < execution.environmentRecall.length →
    ∃ accepted, (message.id, accepted) ∈ execution.receipts)

private def Resources : app.ProtocolState → Prop
  | none => True
  | some control => control.remaining + control.execution.environmentRecall.length = horizon ∧
      PacketService control.execution

private theorem resources_history :
    ∀ {state} (_trace : (app.protocol (initialLaw setup) horizon scheduler).Trace state),
      Resources state
  | _, .start => trivial
  | _, @ExecutionProtocol.Trace.extend _ _ source target prior joint legal reached => by
      have inherited := resources_history prior
      change target ∈ (app.transition (initialLaw setup) horizon scheduler source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact ⟨rfl, by simp [PacketService, ReactiveApplication.Execution.initial]⟩
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              have origin := response_origin ⟨remaining, some who, execution⟩ prior who rfl
              cases (PMF.mem_support_pure_iff _ _).mp reached
              refine ⟨by simpa only [app.respond_environmentRecall] using inherited.1, ?_⟩
              intro observer
              refine ⟨?_, ?_, ?_⟩
              · intro early
                rw [app.respond_environmentRecall] at early
                by_cases same : observer = who
                · subst observer
                  rw [app.respond_recall_length]
                  have zero := origin.2.2 early
                  change (execution.recall who).length = 0 at zero
                  rw [zero]; simp
                · rw [app.respond_recall_other _ _ _ same]
                  exact (inherited.2 observer).1 early
              · intro entry member
                rcases app.respond_entry_origin execution who observer _ entry member with
                  old | ⟨rfl, before⟩
                · exact (inherited.2 observer).2.1 entry old
                · rw [before]; exact origin.1
              · intro entry member message emitted authored addressed first late
                rw [app.respond_environmentRecall] at late
                rw [app.respond_receipts]
                rcases app.respond_entry_origin execution who observer _ entry member with
                  old | ⟨rfl, before⟩
                · exact (inherited.2 observer).2.2 entry old message emitted authored
                    addressed first late
                · rw [before] at first
                  have position := origin.2.1 first
                  omega
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have appended := environmentStep_recall_append execution next command supported
                  have length : next.environmentRecall.length =
                      execution.environmentRecall.length + 1 := by
                    rw [appended, List.length_append, List.length_singleton]
                  have recalled := app.environmentStep_recall execution next command supported
                  have receipts := app.environmentStep_receipts_prefix execution next command
                    supported
                  dsimp only [Resources, PacketService] at inherited ⊢
                  refine ⟨?_, ?_⟩
                  · rw [length]; have counted := inherited.1; omega
                  · intro observer
                    refine ⟨?_, ?_, ?_⟩
                    · intro early; rw [recalled]; exact (inherited.2 observer).1 (by omega)
                    · rw [recalled]; exact (inherited.2 observer).2.1
                    · intro entry member message emitted authored addressed first late
                      rw [recalled] at member
                      by_cases old : serveCursor observer < execution.environmentRecall.length
                      · obtain ⟨accepted, caught⟩ := (inherited.2 observer).2.2 entry member
                          message emitted authored addressed first old
                        exact ⟨accepted, receipts.subset caught⟩
                      · have position : execution.environmentRecall.length =
                            serveCursor observer := by omega
                        have latest : command = (runtime setup).reactiveLatest leaks
                            (serveEvent observer) observer (execution.observeEnvironment app) := by
                          fin_cases observer <;>
                            simpa [scheduler, position, serveCursor, serveEvent, stageChoice,
                              alice, bob] using selected
                        rw [latest] at supported
                        exact serve_entry ⟨remaining + 1, none, execution⟩ prior next observer entry
                          message ((inherited.2 observer).1 (by omega)) member emitted authored
                          addressed supported

theorem completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler := by
  intro control trace terminal
  have phase := cut_history control trace
  have counted := (resources_history trace).1
  change control.remaining + control.execution.environmentRecall.length = horizon at counted
  change control.remaining = 0 ∧ control.actor = none at terminal
  rw [terminal.1, Nat.zero_add] at counted
  have finished := phase.2.1
  rw [counted] at finished
  have ordered : control.execution.application.config.cut.IsPrefix 3 :=
    by simpa [cutSchedule, horizon] using finished
  exact ordered.terminal

theorem opportunity :
    Opportunity (runtime setup) leaks (initialLaw setup) horizon scheduler delay := by
  intro control trace event owner entered owned _ activated late
  have valid := cut_history control trace
  have clocked := valid.1.choose_spec.2
  change Fin 3 at event
  fin_cases event
  · change none = some owner at owned; cases owned
  · change some alice = some owner at owned
    cases Option.some.inj owned
    have zeroEntered := valid.2.2.1.1 entered activated
    subst entered
    apply valid.2.2.2.1
    by_contra earlier
    have zero : clockAt control.execution.environmentRecall.length = 0 := by
      generalize position : control.execution.environmentRecall.length = n at earlier ⊢
      have small : n < 2 := by omega
      interval_cases n <;> rfl
    change 0 + 0 < control.execution.application.clock at late
    rw [clocked, zero] at late
    omega
  · change some bob = some owner at owned
    cases Option.some.inj owned
    apply valid.2.2.2.2 _ entered activated
    by_contra earlier
    have upper : clockAt control.execution.environmentRecall.length ≤ 2 := by
      generalize position : control.execution.environmentRecall.length = n at earlier ⊢
      have small : n < 11 := by omega
      interval_cases n <;> decide
    change entered + 2 < control.execution.application.clock at late
    rw [clocked] at late
    omega

theorem inclusion :
    ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler bound := by
  intro control trace event owner owned earlier later entry message splitRecall emitted
    authored addressed _ready _sole unfinished late
  have phase := cut_history control trace
  have data := (resources_history trace).2 owner
  have member : entry ∈ control.execution.recall owner := by rw [splitRecall]; simp
  have eventEq : serveEvent owner = event := by
    change Fin 3 at event
    fin_cases event
    · change none = some owner at owned; cases owned
    · change some alice = some owner at owned
      cases Option.some.inj owned; rfl
    · change some bob = some owner at owned
      cases Option.some.inj owned; rfl
  rw [← eventEq] at addressed unfinished late
  have entryClock := data.2.1 entry member
  have clocked := phase.1.choose_spec.2
  have pastServe : serveCursor owner < control.execution.environmentRecall.length := by
    by_contra small
    have upper : clockAt control.execution.environmentRecall.length ≤ serveClock owner := by
      fin_cases owner <;> dsimp [serveCursor, serveClock, alice, bob] at small ⊢
      all_goals
        generalize position : control.execution.environmentRecall.length = n at small ⊢
        interval_cases n <;> decide
    rw [clocked] at late
    have lower := entryClock.1
    omega
  have firstClock : entry.beforeView.application.publicView.clock = serveClock owner := by
    fin_cases owner
    · change entry.beforeView.application.publicView.clock = 0
      have early : control.execution.environmentRecall.length < 8 := by
        have ordered := phase.2.1
        unfold cutSchedule at ordered
        split_ifs at ordered <;> first
          | omega
          | exact (unfinished ((ordered.2 aliceEvent).mpr (by decide))).elim
          | rcases ordered with ordered | ordered <;>
              exact (unfinished ((ordered.2 aliceEvent).mpr (by decide))).elim
      have upper : control.execution.application.clock ≤ 2 := by
        rw [clocked]
        generalize position : control.execution.environmentRecall.length = n at early ⊢
        interval_cases n <;> decide
      change entry.beforeView.application.publicView.clock + 1 <
        control.execution.application.clock at late
      omega
    · exact entryClock.2 rfl
  exact data.2.2 entry member message emitted authored addressed firstClock pastServe

theorem contract :
    AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay bound :=
  ⟨opportunity, inclusion, completes⟩

private def silentPlayers : Player → app.Policy := fun _ _ _ => PMF.pure ⟨none⟩

private def silentInitial (high : Bool) : app.Execution :=
  ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs (sourceInitial high)))

private def sampledState (high : Bool) : EventGraphRuntime.State nativeGraph :=
  (silentInitial high).application.complete sampleEvent (by cases high <;> decide) PUnit.unit true

private def silentCompleted (high : Bool) : EventGraphRuntime.State nativeGraph :=
  ({ sampledState high with clock := 2 } : EventGraphRuntime.State nativeGraph).complete
    aliceEvent (by cases high <;> decide) false .failure

private theorem silent_sample (high : Bool) :
    EventGraphRuntime.environmentStep (runtime setup) (silentInitial high).application
      (.executeSample sampleEvent) = PMF.pure (sampledState high) := by
  rw [environmentStep_executeSample_eq (runtime setup) _ sampleEvent (by cases high <;> decide)
    .bool _ rfl rfl rfl]
  rw [Config.step_eq_map_of_eval _ sampleEvent _ _ (PMF.pure true) (by
    change some (RationalLaw.pure true).denote = some (PMF.pure true)
    congr 1
    unfold RationalLaw.denote
    have value : (RationalLaw.pure true).entryValue = fun _ => true := by
      funext index
      fin_cases index
      rfl
    rw [value]
    exact PMF.map_const _ _)]
  simp only [PMF.pure_map]
  rfl

private theorem silent_expire (high : Bool) :
    EventGraphRuntime.environmentStep (runtime setup) { sampledState high with clock := 2 }
      (.expire aliceEvent) = PMF.pure (silentCompleted high) := by
  apply environmentStep_expire_resolve_eq (runtime setup) _ aliceEvent
    (by cases high <;> decide) 0 (by cases high <;> decide) (by decide +revert)
    alice .bool _ [] rfl rfl rfl

private def recorded (execution : app.Execution) (command : app.Command)
    (state : app.State) : app.Execution :=
  { execution with application := state, environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] }

private theorem recorded_application (execution : app.Execution)
    (command : EnvironmentCommand nativeGraph) (state : app.State)
    (moved : EventGraphRuntime.environmentStep (runtime setup) execution.application command =
      PMF.pure state) :
    execution.environmentStep app (.application command) =
      PMF.pure (recorded execution (.application command) state) := by
  simp only [ReactiveApplication.Execution.environmentStep]
  change ((EventGraphRuntime.environmentStep (runtime setup) execution.application command).map
    (fun state => { execution with application := state })).map _ = _
  rw [moved, PMF.pure_map, PMF.pure_map]
  rfl

private theorem recorded_activation (execution : app.Execution) (who : Player) :
    execution.environmentStep app (.activate who) =
      PMF.pure (recorded execution (.activate who) execution.application) := by
  simp only [ReactiveApplication.Execution.environmentStep]
  change ((PMF.pure (∅ : Finset (MessageId Player))).map
    (fun selected => { execution with network := execution.network.learn who selected })).map _ = _
  rw [PMF.pure_map, PMF.pure_map, MessageNetwork.learn_empty]
  rfl

private theorem recorded_wait (execution : app.Execution) :
    execution.environmentStep app .wait =
      PMF.pure (recorded execution .wait execution.application) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem silent_round (execution next : app.Execution) (position : Nat)
    (command : app.Command)
    (cursor : execution.environmentRecall.length = position)
    (chosen : stageChoice position (execution.observeEnvironment app) = PMF.pure command)
    (moved : execution.environmentStep app command = PMF.pure next) :
    app.round scheduler silentPlayers execution =
      app.resume silentPlayers (command.actor? app) next := by
  rw [ReactiveApplication.round, scheduler, cursor, chosen, PMF.pure_bind,
    ReactiveApplication.dispatch, moved, PMF.pure_bind]

private theorem silent_prefix (high : Bool) : ∃ execution : app.Execution,
    app.runRounds scheduler silentPlayers 10 (silentInitial high) = PMF.pure execution ∧
    execution.environmentRecall.length = 10 ∧ execution.network = .empty ∧
    execution.receipts = [] ∧ execution.recall bob = [] ∧
    execution.application = silentCompleted high := by
  let e0 := silentInitial high
  let e1 := recorded e0 (.application (.executeSample sampleEvent)) (sampledState high)
  let e2 := (recorded e1 (.activate alice) e1.application).respond app alice ⟨none⟩
  let e3 := recorded e2 .wait e2.application
  let e4 := recorded e3 (.application .advanceClock) { e3.application with clock := 1 }
  let e5 := (recorded e4 (.activate alice) e4.application).respond app alice ⟨none⟩
  let e6 := recorded e5 .wait e5.application
  let e7 := recorded e6 (.application .advanceClock) { e6.application with clock := 2 }
  let e8 := recorded e7 (.application (.expire aliceEvent)) (silentCompleted high)
  let e9 := (recorded e8 (.activate alice) e8.application).respond app alice ⟨none⟩
  let e10 := recorded e9 .wait e9.application
  have s0 : app.round scheduler silentPlayers e0 = PMF.pure e1 := by
    rw [silent_round e0 e1 0 (.application (.executeSample sampleEvent)) rfl rfl
      (recorded_application e0 _ _ (silent_sample high))]
    rfl
  have s1 : app.round scheduler silentPlayers e1 = PMF.pure e2 := by
    rw [silent_round e1 _ 1 (.activate alice) rfl rfl (recorded_activation e1 alice)]
    simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke, silentPlayers, PMF.pure_map]
    rfl
  have s2 : app.round scheduler silentPlayers e2 = PMF.pure e3 := by
    rw [silent_round e2 e3 2 .wait rfl rfl (recorded_wait e2)]
    rfl
  have s3 : app.round scheduler silentPlayers e3 = PMF.pure e4 := by
    rw [silent_round e3 e4 3 (.application .advanceClock) rfl rfl
      (recorded_application e3 _ _ rfl)]
    rfl
  have s4 : app.round scheduler silentPlayers e4 = PMF.pure e5 := by
    rw [silent_round e4 _ 4 (.activate alice) rfl rfl (recorded_activation e4 alice)]
    simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke, silentPlayers, PMF.pure_map]
    rfl
  have s5 : app.round scheduler silentPlayers e5 = PMF.pure e6 := by
    have chosen : stageChoice 5 (e5.observeEnvironment app) = PMF.pure .wait := by
      change mix (3 / 4) (by norm_num) (by norm_num)
        (PMF.pure (.wait : app.Command)) (PMF.pure .wait) = PMF.pure .wait
      exact mix_self _ _ _ _
    rw [silent_round e5 e6 5 .wait rfl chosen (recorded_wait e5)]
    rfl
  have s6 : app.round scheduler silentPlayers e6 = PMF.pure e7 := by
    rw [silent_round e6 e7 6 (.application .advanceClock) rfl rfl
      (recorded_application e6 _ _ rfl)]
    rfl
  have s7 : app.round scheduler silentPlayers e7 = PMF.pure e8 := by
    rw [silent_round e7 e8 7 (.application (.expire aliceEvent)) rfl rfl
      (recorded_application e7 _ _ (silent_expire high))]
    rfl
  have s8 : app.round scheduler silentPlayers e8 = PMF.pure e9 := by
    rw [silent_round e8 _ 8 (.activate alice) rfl rfl (recorded_activation e8 alice)]
    simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke, silentPlayers, PMF.pure_map]
    rfl
  have s9 : app.round scheduler silentPlayers e9 = PMF.pure e10 := by
    rw [silent_round e9 e10 9 .wait rfl rfl (recorded_wait e9)]
    rfl
  refine ⟨e10, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change app.runRounds scheduler silentPlayers 10 e0 = PMF.pure e10
  simp only [ReactiveApplication.runRounds, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9,
    PMF.pure_bind]

private theorem silent_completed_bob_view (high : Bool) :
    app.observePlayer (silentCompleted high) bob =
      app.observePlayer (silentCompleted false) bob := by
  have observation : nativeGraph.playerObserve bob (silentCompleted high).config =
      nativeGraph.playerObserve bob (silentCompleted false).config := by
    apply nativeGraph.playerObserve_congr bob (silentCompleted high).config
      (silentCompleted false).config rfl
    intro field visible
    cases field with
    | inl input =>
        fin_cases input
        · change alice = bob at visible
          exact ((by decide : alice ≠ bob) visible).elim
        · rfl
    | inr event => fin_cases event <;> rfl
  have publicEq : (silentCompleted high).publicView = (silentCompleted false).publicView := by
    unfold EventGraphRuntime.State.publicView
    congr 1
    apply nativeGraph.publicObserve_congr (silentCompleted high).config
      (silentCompleted false).config rfl
    intro field visible
    cases field with
    | inl input => fin_cases input <;> change False at visible <;> contradiction
    | inr event => fin_cases event <;> rfl
  have candidates : (fun slot => (silentCompleted high).candidates.lookup (bob, slot)) =
      fun slot => (silentCompleted false).candidates.lookup (bob, slot) := by
    funext slot
    change (EventGraphRuntime.State.initial (graph := nativeGraph)
      (setup.eventInputs (sourceInitial high))).candidates.lookup (bob, slot) =
      (EventGraphRuntime.State.initial (graph := nativeGraph)
        (setup.eventInputs (sourceInitial false))).candidates.lookup (bob, slot)
    rw [EventGraphRuntime.State.initial_candidate, EventGraphRuntime.State.initial_candidate]
    cases slot with
    | prepared _ => rfl
    | initial input => fin_cases input <;> rfl
  change (ReactivePlayerView.mk bob _ _ _) = ReactivePlayerView.mk bob _ _ _
  rw [publicEq, observation, candidates]

/-- Literal silence reaches one full first-Bob input at both initial types.
This identifies the canonical path, not every history in that information fiber. -/
theorem silent_bob_input_law : ∃ input : List app.PlayerEntry × app.PlayerView,
    input.1 = [] ∧
    input.2.application.publicView.observation.store (.inr aliceEvent) = some .failure ∧
    ∀ high : Bool,
      (((app.runRounds scheduler (fun _ _ _ => PMF.pure (⟨none⟩ : app.Action)) 10
        (ReactiveApplication.Execution.initial app
          (EventGraphRuntime.State.initial (setup.eventInputs (sourceInitial high))))).bind
        (fun before => (scheduler before.environmentRecall (before.observeEnvironment app)).bind
          (before.environmentStep app))).map
        (fun after => (after.recall bob, after.observe app bob))) = PMF.pure input := by
  obtain ⟨baseline, _, _, baseNetwork, baseReceipts, baseRecall, baseState⟩ := silent_prefix false
  refine ⟨(baseline.recall bob, baseline.observe app bob), baseRecall, ?_, ?_⟩
  · change (app.observePlayer baseline.application bob).publicView.observation.store
      (.inr aliceEvent) = some .failure
    rw [baseState]
    rfl
  · intro high
    obtain ⟨execution, prefixLaw, cursor, network, receipts, recalled, state⟩ := silent_prefix high
    change (((app.runRounds scheduler silentPlayers 10 (silentInitial high)).bind _).map _) = _
    rw [prefixLaw, PMF.pure_bind]
    have chosen : scheduler execution.environmentRecall (execution.observeEnvironment app) =
        PMF.pure (.activate bob) := by simp only [scheduler, cursor, stageChoice]
    rw [chosen, PMF.pure_bind, recorded_activation, PMF.pure_map]
    apply congrArg PMF.pure
    change (execution.recall bob, execution.observe app bob) =
      (baseline.recall bob, baseline.observe app bob)
    apply Prod.ext
    · rw [recalled, baseRecall]
    · change (ReactiveApplication.PlayerView.mk _ _ _) =
        ReactiveApplication.PlayerView.mk _ _ _
      rw [network, baseNetwork, receipts, baseReceipts, state, baseState,
        silent_completed_bob_view]

open GameTheory.Enforcement

private theorem prescribed_opening_content (before : PublicView nativeGraph)
    (record : SettledRecord nativeGraph) (event : nativeGraph.EventId)
    (message : Message Player (WitnessedPacket nativeGraph))
    (named : message.payload.call.event? nativeGraph = some event)
    (conforming : (runtime setup).freshServiceEnvelope before message)
    (owned : nativeGraph.actor? event = some message.sender) :
    record.SettledContent message := by
  fin_cases event
  · change none = some message.sender at owned
    cases owned
  · let binding : FieldRef nativeGraph.layout (.binding alice .bool) := ⟨.inl ⟨0, by decide⟩, rfl⟩
    obtain ⟨candidate, raw, _, _, _, typed, packet, _⟩ :=
      freshServiceEnvelope_resolution_shape (runtime setup) before alice aliceEvent .bool
        binding [] rfl rfl rfl message named conforming
    cases raw with
    | mk kind value =>
        change kind = .bool at typed
        subst kind
        unfold SettledRecord.SettledContent
        rw [packet]
        refine ⟨by simp [certifiedOpening], ?_⟩
        exact (record.view.openingGuardsAccepted_iff alice aliceEvent .bool binding []
          rfl rfl rfl candidate ⟨.bool, value⟩ (some ⟨candidate, ⟨.bool, value⟩⟩)).mpr
          ⟨value, rfl, rfl⟩
  · let binding : FieldRef nativeGraph.layout (.binding bob .bool) := ⟨.inl ⟨1, by decide⟩, rfl⟩
    obtain ⟨candidate, raw, _, _, _, typed, packet, _⟩ :=
      freshServiceEnvelope_resolution_shape (runtime setup) before bob bobEvent .bool
        binding [] rfl rfl rfl message named conforming
    cases raw with
    | mk kind value =>
        change kind = .bool at typed
        subst kind
        unfold SettledRecord.SettledContent
        rw [packet]
        refine ⟨by simp [certifiedOpening], ?_⟩
        exact (record.view.openingGuardsAccepted_iff bob bobEvent .bool binding []
          rfl rfl rfl candidate ⟨.bool, value⟩ (some ⟨candidate, ⟨.bool, value⟩⟩)).mpr
          ⟨value, rfl, rfl⟩

/-- Every transmitted envelope on initialized all-prescribed play is accepted and permitted. -/
theorem prescribed_packets_clean (original : BehavioralProfile program) (execution : app.Execution)
    (reached : execution ∈ (app.roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound 0 (firstTurnTiming setup 0) original)
      horizon).support) :
    ∀ input ∈ execution.network.inputs,
      (input.envelope.id, true) ∈ execution.receipts ∧
        ((runtime setup).settledRecord leaks execution).permits input.envelope = true := by
  let players := sourceServiceTurnPolicy setup leaks bound 0 (firstTurnTiming setup 0) original
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    horizon le_rfl execution reached
  simp only [Nat.sub_self] at trace
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have finished := completes ⟨0, none, execution⟩ trace ⟨rfl, rfl⟩
  intro input member
  obtain ⟨entry, inside, material, fresh, emitted, _, _, _⟩ :=
    facts.provenance.inputs input member
  obtain ⟨calls, once, _⟩ := serialFacts_roundsFrom contract players input.envelope.sender
    (firstTurnTiming setup 0) original rfl horizon le_rfl execution reached
  obtain ⟨event, message, sent, authored, addressed, submitted, fits⟩ :=
    calls entry inside material fresh
  have identified : message = input.envelope := Option.some.inj (sent.symm.trans emitted)
  subst message
  have conforming := sourceServiceTurnPolicy_freshServiceEnvelope scheduler players
    input.envelope.sender (firstTurnTiming setup 0) original rfl horizon execution reached
    entry inside material fresh input.envelope emitted
  obtain ⟨actual, named, ready, owned⟩ :=
    (runtime setup).freshServiceEnvelope_owned _ input.envelope conforming
  have eventEq : actual = event := Option.some.inj (named.symm.trans addressed)
  subst actual
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp inside
  have call : FreshCall setup leaks input.envelope.sender event bound entry input.envelope :=
    ⟨⟨material, fresh⟩, emitted, rfl, addressed, ready, fits,
      freshServiceEnvelope.acceptable (runtime setup) conforming⟩
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event input.envelope.id := by
    intro other member ⟨replayed, output, author, addressedOther, different⟩
    have recalled : other ∈ execution.recall input.envelope.sender := by
      rw [split]
      rcases List.mem_append.mp member with left | right
      · exact List.mem_append_left _ left
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
    have issued : replayed ∈ app.outputs (execution.recall input.envelope.sender) :=
      List.mem_filterMap.mpr ⟨other, recalled, output⟩
    rw [← facts.inputs input.envelope.sender] at issued
    obtain ⟨record, present, projected⟩ := List.mem_filterMap.mp issued
    split at projected
    · cases Option.some.inj projected
      obtain ⟨issuer, issuerMember, issuerMaterial, issuerFresh, issuerEmitted,
        state, known, packet⟩ := facts.provenance.inputs record present
      rw [author] at issuerMember
      have issuerNames : (runtime setup).submittedEvent? leaks issuer.action =
          record.envelope.payload.call.event? nativeGraph := by
        unfold EventGraphRuntime.submittedEvent?
        rw [issuerFresh, ← packet]
        rfl
      exact different (once issuer issuerMember entry inside event _ _
        (issuerNames.trans addressedOther) submitted
        issuerEmitted emitted)
    · cases projected
  have accepted := (prescribed_packet_settles setup leaks inclusion trace event
    input.envelope.sender owned earlier later entry input.envelope split call sole).2
    (by rw [finished]; exact Finset.mem_univ event)
  refine ⟨accepted, SettledRecord.permits_of_accepted _ _ event addressed accepted ?_⟩
  exact prescribed_opening_content entry.beforeView.application.publicView _ event
    input.envelope addressed conforming owned

/-- Authentic terminal sampling leaves the entire prescribed payoff vector unchanged. -/
theorem prescribed_settlement (original : BehavioralProfile program) (execution : app.Execution)
    (reached : execution ∈ (app.roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound 0 (firstTurnTiming setup 0) original)
      horizon).support)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (base : app.ProtocolState → Player → ℝ) (deposit : Player → ℝ) :
    TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit (some ⟨0, none, execution⟩) =
        PMF.pure (base (some ⟨0, none, execution⟩)) := by
  apply TerminalAudit.settlement_clean
  intro who
  have clean := prescribed_packets_clean original execution reached
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler _
    horizon le_rfl execution reached
  simp only [Nat.sub_self] at trace
  have noOmission := execution.application.publicView.missedBindingBy_of_publications
    (by
      intro event owner payload
      fin_cases event <;> intro incompatible <;> cases incompatible) who
  unfold sourceServiceAudit
  rw [(runtime setup).serviceAudit_charge, noOmission]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record member _
    have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler trace
    change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.input =
      execution.network.inputs at inputs
    have present : record.input ∈ execution.network.inputs := by
      rw [← inputs]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    exact (clean record.input present).2

private def firstAlice : app.Execution :=
  let sampled := recorded (silentInitial true) (.application (.executeSample sampleEvent))
    (sampledState true)
  recorded sampled (.activate alice) sampled.application

private theorem first_alice_law (players : Player → app.Policy) :
    (app.runRounds scheduler players 1 (silentInitial true)).bind
      (fun before => (scheduler before.environmentRecall (before.observeEnvironment app)).bind
        (before.environmentStep app)) = PMF.pure firstAlice := by
  let sampled := recorded (silentInitial true) (.application (.executeSample sampleEvent))
    (sampledState true)
  have first : app.round scheduler players (silentInitial true) = PMF.pure sampled := by
    rw [ReactiveApplication.round]
    change (PMF.pure (.application (.executeSample sampleEvent) : app.Command)).bind _ = _
    rw [PMF.pure_bind, ReactiveApplication.dispatch,
      recorded_application _ _ _ (silent_sample true), PMF.pure_bind]
    rfl
  simp only [ReactiveApplication.runRounds, first, PMF.pure_bind]
  change (PMF.pure (.activate alice : app.Command)).bind _ = _
  rw [PMF.pure_bind, recorded_activation]
  rfl

private theorem first_true_prompt (players : Player → app.Policy) :
    let response := (runtime setup).canonicalServiceDecision leaks alice []
      (firstAlice.observe app alice) aliceEvent true
    ∃ next, app.round scheduler players (firstAlice.respond app alice response) =
        PMF.pure next ∧
      next.application.config.store (.inr aliceEvent) = some (.success true) := by
  let binding : FieldRef nativeGraph.layout (.binding alice .bool) := ⟨.inl ⟨0, by decide⟩, rfl⟩
  let candidate : Handle nativeGraph := (alice, .initial ⟨0, by decide⟩)
  let opening := disclosureSubmission (.opening aliceEvent candidate ⟨.bool, true⟩)
  have fixed : firstAlice.application.candidates.lookup candidate = .openable ⟨.bool, true⟩ := by
    change (State.initial (setup.eventInputs (sourceInitial true))).candidates.lookup candidate = _
    exact State.initial_candidate_binding_success (graph := nativeGraph) _ _ alice .bool
      rfl true rfl
  have associated : firstAlice.application.accepted binding.field = some candidate := rfl
  have stored : binding.get? firstAlice.application.config.store = some (.success true) := rfl
  have resolved : EventCode.resolveOutput? binding [] true
      firstAlice.application.config.store = some (.success true) := rfl
  have shape : (runtime setup).canonicalServiceDecision leaks alice []
      (firstAlice.observe app alice) aliceEvent true = ⟨some (.submit opening)⟩ := by
    rw [canonicalServiceDecision_eq_of_not_bind (runtime setup) leaks alice [] _ aliceEvent true
      (by intro owner payload outputEq codeEq; cases outputEq)]
    have result := (runtime setup).serviceDecision_successful_opening leaks firstAlice
      (by intro who; rfl) alice aliceEvent .bool binding [] rfl rfl rfl candidate true
      associated rfl fixed resolved
    change (runtime setup).serviceDecision leaks alice []
      (firstAlice.observe app alice) aliceEvent true = _ at result
    rw [result]
    change (⟨some (.submit (WitnessedSubmission.normalizeReactive alice
      (app.observePlayer firstAlice.application alice) []
      (disclosureSubmission (.opening aliceEvent candidate ⟨.bool, true⟩))))⟩ : app.Action) = _
    have localFixed : (app.observePlayer firstAlice.application alice).candidates candidate.2 =
        .openable ⟨.bool, true⟩ := fixed
    rw [disclosureSubmission_normalize_opening alice _ aliceEvent candidate ⟨.bool, true⟩
      rfl localFixed]
  rw [shape]
  let submitted := firstAlice.respond app alice ⟨some (.submit opening)⟩
  let completed := firstAlice.application.complete aliceEvent (by decide) true (.success true)
  have packet : app.packet submitted.application alice (firstAlice.network.known alice) opening =
      ⟨.opening aliceEvent candidate ⟨.bool, true⟩,
        some ⟨candidate, ⟨.bool, true⟩⟩, some ⟨aliceEvent⟩⟩ := by
    change opening.emit firstAlice.application alice [] = _
    have verified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr fixed
    have token : firstAlice.application.publicView.tokenFor
        (.opening aliceEvent candidate ⟨.bool, true⟩) = some ⟨aliceEvent⟩ := by
      exact firstAlice.application.publicView_tokenFor_of_ready _ aliceEvent rfl (by decide)
    simp only [opening, disclosureSubmission, WitnessedSubmission.emit, verified, token]
    rfl
  have handled : app.handle submitted.application
      ⟨(alice, 0), ⟨.opening aliceEvent candidate ⟨.bool, true⟩,
        some ⟨candidate, ⟨.bool, true⟩⟩, some ⟨aliceEvent⟩⟩⟩ = some completed := by
    rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _ (by rfl)]
    exact (runtime setup).handle_opening_eq firstAlice.application _ aliceEvent candidate alice
      .bool binding [] rfl rfl rfl (by decide) (by change 0 - 0 < 2; decide)
      rfl rfl associated true fixed stored
      (.success true) resolved
  have chosen : scheduler submitted.environmentRecall (submitted.observeEnvironment app) =
      PMF.pure (.include (alice, 0)) := by
    change stageChoice 2 _ = _
    simp only [stageChoice]
    change PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice _) = _
    congr 1
  have included : (submitted.includePending app (alice, 0)).application = completed := by
    change Option.getD (app.handle submitted.application ⟨(alice, 0),
      app.packet submitted.application alice (firstAlice.network.known alice) opening⟩)
      submitted.application = _
    rw [packet, handled]
    rfl
  refine ⟨{ submitted.includePending app (alice, 0) with environmentRecall :=
      submitted.environmentRecall ++ [⟨submitted.observeEnvironment app, .include (alice, 0)⟩] },
    ?_, ?_⟩
  · rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  · change (submitted.includePending app (alice, 0)).application.config.store _ = _
    rw [included]
    rfl

/-- A canonical first TRUE opening makes Alice's output successful under every later RAW policy. -/
theorem first_true_bob_output_law (players : Player → app.Policy) :
    let first := (app.runRounds scheduler players 1
      (ReactiveApplication.Execution.initial app
        (State.initial (setup.eventInputs (sourceInitial true))))).bind
      (fun before => (scheduler before.environmentRecall (before.observeEnvironment app)).bind
        (before.environmentStep app))
    let submitted := first.map (fun before => before.respond app alice
      ((runtime setup).canonicalServiceDecision leaks alice [] (before.observe app alice)
        aliceEvent true))
    ((submitted.bind (app.runRounds scheduler players 8)).bind
      (fun before => (scheduler before.environmentRecall (before.observeEnvironment app)).bind
        (before.environmentStep app))).map
      (fun after => (after.observe app bob).application.publicView.observation.store
        (.inr aliceEvent)) = PMF.pure (some (.success true)) := by
  dsimp only
  have first := first_alice_law players
  simp only [silentInitial] at first
  rw [first, PMF.pure_map, PMF.pure_bind]
  obtain ⟨next, prompt, output⟩ := first_true_prompt players
  rw [ReactiveApplication.runRounds, prompt, PMF.pure_bind]
  have invariant := ReactiveApplication.Invariant.policyInvariant app
    ((runtime setup).reactiveStoreInvariant leaks (.inr aliceEvent) (.success true)) players
  have constant : ∀ before ∈ (app.runRounds scheduler players 7 next).support,
      ∀ command ∈ (scheduler before.environmentRecall (before.observeEnvironment app)).support,
      ∀ after ∈ (before.environmentStep app command).support,
      (after.observe app bob).application.publicView.observation.store (.inr aliceEvent) =
        some (.success true) := by
    intro before reached command _ after moved
    have retained := invariant.runRounds scheduler 7 next before output reached
    have retained := invariant.environment before after command retained moved
    exact retained
  calc
    _ = ((app.runRounds scheduler players 7 next).bind
      (fun before => (scheduler before.environmentRecall (before.observeEnvironment app)).bind
        (before.environmentStep app))).map (fun _ => some (.success true)) := by
      apply map_congr_on_support
      intro after reached
      obtain ⟨before, prior, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, chosen, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      exact constant before prior command chosen after moved
    _ = _ := PMF.map_const _ _

end Vegas.Examples.CommittedResolutionService

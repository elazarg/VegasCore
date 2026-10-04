/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkClockPhase
import Interaction.ReactiveSubmissionAudit

/-! # Completed prefixes and activation times in the public resolution fork

These resources quantify over every initialized raw protocol trace. The
public schedule forces both samples and final expiries, and each strategic
event remains in its own inclusion window. Receipt and opportunity guarantees
are separate from these completed-prefix and activation-time bounds.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

def lowerRank (stage : Nat) : Nat :=
  if stage = 0 then 0 else if stage ≤ 1 then 1 else if stage ≤ 9 then 2
  else if stage ≤ 16 then 3 else 4

def upperRank (stage : Nat) : Nat :=
  if stage = 0 then 0 else if stage ≤ 1 then 1 else if stage ≤ 3 then 2
  else if stage ≤ 11 then 3 else 4

def ActivationBounds (event : nativeGraph.EventId) (entered : Nat) : Prop :=
  if event = aliceResolution then entered = 0
  else if event = bobResolution then entered ≤ 3 else False

structure CompletionBounds (control : app.Control) : Prop where
  ordered : ∃ rank, lowerRank control.execution.environmentRecall.length ≤ rank ∧
    rank ≤ upperRank control.execution.environmentRecall.length ∧
    control.execution.application.config.cut.IsPrefix rank
  entered : ∀ event entered, control.execution.application.activatedAt event = some entered →
    ActivationBounds event entered

def completionBoundsInvariant : app.ProtocolState → Prop
  | none => True
  | some control => CompletionBounds control

private theorem CompletionBounds.window (control : app.Control)
    (phase : CompletionBounds control) (event : nativeGraph.EventId)
    (lower : lowerRank control.execution.environmentRecall.length = event.val)
    (upper : upperRank control.execution.environmentRecall.length ≤ event.val + 1) :
    control.execution.application.config.cut.IsPrefix event.val ∨
      control.execution.application.config.cut.IsPrefix (event.val + 1) := by
  obtain ⟨rank, low, high, ordered⟩ := phase.ordered
  rw [lower] at low
  have maximum := high.trans upper
  have current : rank = event.val ∨ rank = event.val + 1 := by omega
  rcases current with rfl | rfl
  · exact Or.inl ordered
  · exact Or.inr ordered

private theorem withholding_prefix (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (next : app.Execution)
    (ordered : control.execution.application.config.cut.IsPrefix 2 ∨
      control.execution.application.config.cut.IsPrefix 3)
    (moved : next ∈ (control.execution.environmentStep app
      (latestAliceWithhold (control.execution.observeEnvironment app))).support) :
    next.application.config.cut.IsPrefix 2 ∨ next.application.config.cut.IsPrefix 3 := by
  rcases ordered with before | after
  · have step : GraphStep control.execution.application next.application := by
      rcases environment_graph_or_tick control.execution next _ moved with ⟨tick, _⟩ | step
      · unfold latestAliceWithhold at tick
        split at tick <;> cases tick
      · exact step
    rcases step.prefix setup aliceResolution before with same | advanced
    · rw [same.1]
      exact Or.inl before
    · exact Or.inr advanced.1
  · unfold latestAliceWithhold at moved
    split at moved
    · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at moved
      cases moved
      exact Or.inr after
    · rename_i selected found
      have matching := List.find?_some found
      simp only [decide_eq_true_eq] at matching
      have present := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
      have audited := (app.submissionAudit_history ReactivePlayerView.publicView
        (fun _ _ => rfl) (initialLaw setup) horizon scheduler trace).1
      have looked := ReactiveApplication.Execution.SubmissionAudit.lookup_of_mem app
        ReactivePlayerView.publicView control.execution audited selected present
      have rejected := (runtime setup).handle_eq_none_of_completed
        control.execution.application ⟨selected.id, selected.payload.call⟩ aliceResolution
        (by rw [matching.2.1]; rfl) ((after.2 aliceResolution).mpr (by decide))
      have reactiveRejected : app.handle control.execution.application selected = none := by
        simp only [reactiveApplication_handle, rejected, ite_self]
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at moved
      cases moved
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        looked, reactiveRejected, Option.getD_none] using Or.inr after

private theorem completionBounds_initial (state : app.State)
    (supported : state ∈ (initialLaw setup).support) :
    CompletionBounds ⟨horizon, none, ReactiveApplication.Execution.initial app state⟩ := by
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  refine ⟨⟨0, le_rfl, le_rfl, EventOrder.Cut.empty_isPrefix _⟩, ?_⟩
  intro event entered activated
  have invariant := State.initial_invariant (graph := nativeGraph) (setup.eventInputs initial)
  change (State.initial (graph := nativeGraph) (setup.eventInputs initial)).activatedAt event =
    some entered at activated
  have strategic := invariant.activated_iff event |>.mp (by rw [activated]; rfl)
  have ready := (ready_iff_rank setup _ 0 (EventOrder.Cut.empty_isPrefix _) event).mp strategic.1
  have eventEq : event = sample0 := Fin.ext ready
  rw [eventEq] at strategic
  change _ ∧ false = true at strategic
  have impossible := strategic.2
  cases impossible

private theorem completionBounds_respond (control : app.Control)
    (phase : CompletionBounds control) (who : Player) (response : app.Action) :
    CompletionBounds { control with
      actor := none
      execution := control.execution.respond app who response } := by
  obtain ⟨configEq, publicEq⟩ :=
    (runtime setup).reactive_respond_application leaks control.execution who response
  have activatedEq := congrArg PublicView.activatedAt publicEq
  dsimp only [State.publicView] at activatedEq
  refine ⟨?_, ?_⟩
  · rw [app.respond_environmentRecall, configEq]
    exact phase.ordered
  · intro event entered activated
    rw [activatedEq] at activated
    exact phase.entered event entered activated

private theorem completionBounds_environment_ordered (control : app.Control)
    (phase : CompletionBounds control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (beforeEnd : control.execution.environmentRecall.length < horizon) :
    ∃ rank, lowerRank next.environmentRecall.length ≤ rank ∧
      rank ≤ upperRank next.environmentRecall.length ∧
      next.application.config.cut.IsPrefix rank := by
  have appended := environmentStep_recall_append control.execution next command moved
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler trace).1
  have unique := app.uniqueIds_history scheduler (initialLaw setup) horizon control trace
  have clock : ClockPhase control := clockPhase_history trace
  by_cases four : control.execution.environmentRecall.length = 4
  · have same := environmentStep_config_activated_stutter setup leaks
      control.execution next command (by
      rcases scheduler_support_four _ _ _ four selected with first | second
      · exact Or.inl ⟨alice, first⟩
      · exact Or.inr (Or.inr second)) moved
    obtain ⟨rank, low, high, ordered⟩ := phase.ordered
    rw [same.1]
    exact ⟨rank, by simpa [length, four, lowerRank] using low,
      by simpa [length, four, upperRank] using high, ordered⟩
  by_cases six : control.execution.environmentRecall.length = 6
  · have window := CompletionBounds.window control phase aliceResolution
      (by simp [six, lowerRank]) (by simp [six, upperRank])
    have nextWindow : next.application.config.cut.IsPrefix 2 ∨
        next.application.config.cut.IsPrefix 3 := by
      rcases scheduler_support_six _ _ _ six selected with latest | withholding
      · rw [latest] at moved
        exact (reactiveLatest_prefix setup leaks control.execution next aliceResolution alice
          unique window moved).1
      · rw [withholding] at moved
        exact withholding_prefix control trace next window moved
    rcases nextWindow with current | completed
    · exact ⟨2, by simp [length, six, lowerRank], by simp [length, six, upperRank], current⟩
    · exact ⟨3, by simp [length, six, lowerRank], by simp [length, six, upperRank], completed⟩
  have chosen := scheduler_support_other _ _ command four six selected
  rw [chosen] at moved
  generalize stageEq : control.execution.environmentRecall.length = stage
    at beforeEnd four six moved ⊢
  change stage < 17 at beforeEnd
  interval_cases stage
  all_goals try contradiction
  case «0» =>
    obtain ⟨rank, low, high, ordered⟩ := phase.ordered
    rw [stageEq] at high
    have zero : rank = 0 := by simpa [upperRank] using high
    subst rank
    have ready := (ready_iff_rank setup _ 0 ordered sample0).mpr rfl
    have physical := (applicationStep_facts control.execution next _ moved).1
    have cutEq := (executeSample_completes (runtime setup) _ _ sample0 rfl ready physical).1
    refine ⟨1, by simp [length, stageEq, lowerRank], by simp [length, stageEq, upperRank], ?_⟩
    rw [cutEq]
    exact ordered.complete_at sample0 ready rfl
  case «1» =>
    obtain ⟨rank, low, high, ordered⟩ := phase.ordered
    rw [stageEq] at low high
    have one : rank = 1 := by simpa [lowerRank, upperRank] using Nat.le_antisymm high low
    subst rank
    have ready := (ready_iff_rank setup _ 1 ordered sample1).mpr rfl
    have physical := (applicationStep_facts control.execution next _ moved).1
    have cutEq := (executeSample_completes (runtime setup) _ _ sample1 rfl ready physical).1
    refine ⟨2, by simp [length, stageEq, lowerRank], by simp [length, stageEq, upperRank], ?_⟩
    rw [cutEq]
    exact ordered.complete_at sample1 ready rfl
  case «3» =>
    have outcome := reactiveLatest_prefix setup leaks control.execution next aliceResolution alice
      unique (CompletionBounds.window control phase aliceResolution
        (by simp [stageEq, lowerRank]) (by simp [stageEq, upperRank])) moved
    rcases outcome.1 with current | completed
    · exact ⟨_, by simp [length, stageEq, lowerRank],
        by simp [length, stageEq, upperRank], current⟩
    · exact ⟨_, by simp [length, stageEq, lowerRank],
        by simp [length, stageEq, upperRank], completed⟩
  case «9» =>
    have finished := expire_prefix_next setup leaks control.execution next
      aliceResolution alice rfl invariant
      (CompletionBounds.window control phase aliceResolution
        (by simp [stageEq, lowerRank]) (by simp [stageEq, upperRank])) 0
      (by intro entered activated
          have exactClock := phase.entered aliceResolution entered activated
          simpa [ActivationBounds] using exactClock.le)
      (by rw [clock.clock]; change 0 + 3 ≤ _; simp [stageClock, stageEq]) moved
    exact ⟨_, by simp [length, stageEq, lowerRank],
      by simp [length, stageEq, upperRank], finished⟩
  case «11» =>
    have outcome := reactiveLatest_prefix setup leaks control.execution next
      bobResolution bob unique
      (CompletionBounds.window control phase bobResolution
        (by simp [stageEq, lowerRank]) (by simp [stageEq, upperRank])) moved
    rcases outcome.1 with current | completed
    · exact ⟨_, by simp [length, stageEq, lowerRank],
        by simp [length, stageEq, upperRank], current⟩
    · exact ⟨_, by simp [length, stageEq, lowerRank],
        by simp [length, stageEq, upperRank], completed⟩
  case «16» =>
    have finished := expire_prefix_next setup leaks control.execution next
      bobResolution bob rfl invariant
      (CompletionBounds.window control phase bobResolution
        (by simp [stageEq, lowerRank]) (by simp [stageEq, upperRank])) 3
      (by intro entered activated; simpa [ActivationBounds] using
          phase.entered bobResolution entered activated)
      (by rw [clock.clock]; change 3 + 4 ≤ _; simp [stageClock, stageEq]) moved
    exact ⟨_, by simp [length, stageEq, lowerRank],
      by simp [length, stageEq, upperRank], finished⟩
  all_goals
    have same := environmentStep_config_activated_stutter setup leaks control.execution next _ (by
      simp only [stageCommand]
      first | (split <;> simp) | simp) moved
    obtain ⟨rank, low, high, ordered⟩ := phase.ordered
    rw [same.1]
    exact ⟨rank, by simpa [length, stageEq, lowerRank] using low,
      by simpa [length, stageEq, upperRank] using high, ordered⟩

private theorem completionBounds_environment_entered (control : app.Control)
    (phase : CompletionBounds control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (next : app.Execution) (command : app.Command)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (query : nativeGraph.EventId) (entered : Nat)
    (activated : next.application.activatedAt query = some entered) :
    ActivationBounds query entered := by
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler trace).1
  rcases environment_graph_or_tick control.execution next command moved with
    ⟨_, _, same, _⟩ | graphStep
  · rw [same] at activated
    exact phase.entered query entered activated
  rcases graphStep with ⟨_, _, same⟩ | ⟨event, ready, action, supported, _, refreshed⟩
  · rw [same] at activated
    exact phase.entered query entered activated
  obtain ⟨rank, low, high, ordered⟩ := phase.ordered
  have eventRank := (ready_iff_rank setup _ rank ordered event).mp ready
  have nextOrdered : next.application.config.cut.IsPrefix (rank + 1) := by
    rw [control.execution.application.config.step_cut event ready action
      next.application.config supported]
    exact ordered.complete_at event ready eventRank
  have freshInvariant := invariant.refreshStep event ready action next.application.config supported
  have queryFacts := (freshInvariant.activated_iff query).mp (by
    change (State.refreshActivated next.application.config control.execution.application.clock
      control.execution.application.activatedAt query).isSome = true
    rw [← refreshed, activated]
    rfl)
  have successor := (ready_iff_rank setup _ (rank + 1) nextOrdered query).mp queryFacts.1
  have now : entered = control.execution.application.clock := by
    rw [refreshed] at activated
    exact refreshActivated_successor setup invariant event
      (by simpa only [eventRank] using ordered) next.application.config query
      (by omega) entered activated
  have clock : ClockPhase control := clockPhase_history trace
  rw [now, clock.clock]
  change Fin 4 at query
  fin_cases query
  · have owned := queryFacts.2
    change false = true at owned
    cases owned
  · have owned := queryFacts.2
    change false = true at owned
    cases owned
  · change 2 = rank + 1 at successor
    have one : rank = 1 := by omega
    rw [one] at low high
    have stage : control.execution.environmentRecall.length = 1 := by
      simp only [lowerRank, upperRank] at low high
      split_ifs at low high <;> omega
    change stageClock control.execution.environmentRecall = 0
    simp [stageClock, stage]
  · change 3 = rank + 1 at successor
    have two : rank = 2 := by omega
    rw [two] at low high
    have early : control.execution.environmentRecall.length ≤ 9 := by
      unfold lowerRank at low
      split_ifs at low <;> omega
    change stageClock control.execution.environmentRecall ≤ 3
    dsimp only [stageClock]
    split_ifs <;> omega

private theorem completionBounds_transition (before after : app.ProtocolState)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace before)
    (valid : completionBoundsInvariant before) (joint : Player → Option app.Action)
    (reached : after ∈
      (app.transition (initialLaw setup) horizon scheduler before joint).support) :
    completionBoundsInvariant after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact completionBounds_initial state supported
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact completionBounds_respond _ valid who _
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, realized⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ realized
              have beforeEnd : execution.environmentRecall.length < horizon := by
                have budget := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
                change execution.environmentRecall.length + (remaining + 1) = horizon at budget
                omega
              exact ⟨completionBounds_environment_ordered _ valid trace next command selected
                moved beforeEnd,
                completionBounds_environment_entered _ valid trace next command moved⟩

theorem completionBounds_history : ∀ {state}
    (_trace : (app.protocol (initialLaw setup) horizon scheduler).Trace state),
    completionBoundsInvariant state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      completionBounds_transition _ _ prior (completionBounds_history prior) joint reached

theorem bob_raw_ready (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (active : control.actor = some bob) :
    control.execution.application.config.cut.Ready bobResolution := by
  have stage := (bob_raw_decision_resources control trace active).1
  obtain ⟨rank, low, high, ordered⟩ := (completionBounds_history trace).ordered
  have current : rank = 3 := Nat.le_antisymm
    (by simpa [upperRank, stage] using high) (by simpa [lowerRank, stage] using low)
  subst rank
  exact (ready_iff_rank setup _ 3 ordered bobResolution).mpr rfl

theorem completesPlay :
    CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler := by
  intro control trace terminal
  have budget := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
  change control.execution.environmentRecall.length + control.remaining = horizon at budget
  have stage : control.execution.environmentRecall.length = horizon := by
    rw [terminal.1] at budget
    omega
  obtain ⟨rank, low, high, ordered⟩ := (completionBounds_history trace).ordered
  have full : rank = 4 := Nat.le_antisymm
    (by simpa [upperRank, stage, horizon] using high)
    (by simpa [lowerRank, stage, horizon] using low)
  rw [full] at ordered
  exact ordered.terminal

end Vegas.PrivateResolutionFork

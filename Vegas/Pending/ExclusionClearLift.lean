/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionProjection
import Vegas.Pending.ExclusionInvariant
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveResponseAccounting

/-! # Clear lifts of native execution data

Native observations and recalls lift with empty permanent exclusion flags.
On actual recovery histories whose final excluded set is empty, monotonicity
makes all recalled flags empty too, so lifting reverses native projection.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def liftAction (response : (runtime.reactiveApplication leaks).Action) :
    (runtime.recoveryApplication leaks).Action := ⟨response.transmission⟩

def liftPlayerView (view : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.recoveryApplication leaks).PlayerView :=
  ⟨view.messages, (view.application, ∅), view.receipts⟩

def liftPlayerEntry (entry : (runtime.reactiveApplication leaks).PlayerEntry) :
    (runtime.recoveryApplication leaks).PlayerEntry :=
  ⟨liftPlayerView runtime leaks entry.beforeView,
    liftAction runtime leaks entry.action, entry.emitted⟩

def liftEnvironmentView (view : (runtime.reactiveApplication leaks).EnvironmentView) :
    (runtime.recoveryApplication leaks).EnvironmentView :=
  ⟨view.network, (view.application, ∅), view.receipts⟩

def liftCommand : (runtime.reactiveApplication leaks).Command →
    (runtime.recoveryApplication leaks).Command
  | .activate who => .activate who
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def liftEnvironmentEntry (entry : (runtime.reactiveApplication leaks).EnvironmentEntry) :
    (runtime.recoveryApplication leaks).EnvironmentEntry :=
  ⟨liftEnvironmentView runtime leaks entry.beforeView, liftCommand runtime leaks entry.command⟩

def liftExecution (current : (runtime.reactiveApplication leaks).Execution) :
    (runtime.recoveryApplication leaks).Execution :=
  ⟨⟨current.application, ∅⟩, current.network, current.receipts,
    fun who => (current.recall who).map (liftPlayerEntry runtime leaks),
    current.environmentRecall.map (liftEnvironmentEntry runtime leaks)⟩

def liftControl (current : (runtime.reactiveApplication leaks).Control) :
    (runtime.recoveryApplication leaks).Control :=
  ⟨current.remaining, current.actor, liftExecution runtime leaks current.execution⟩

@[simp] theorem action_liftAction (response : (runtime.reactiveApplication leaks).Action) :
    action runtime leaks (liftAction runtime leaks response) = response := by
  cases response
  rfl

@[simp] theorem liftAction_action (response : (runtime.recoveryApplication leaks).Action) :
    liftAction runtime leaks (action runtime leaks response) = response := by
  cases response
  rfl

@[simp] theorem playerView_liftPlayerView (view : (runtime.reactiveApplication leaks).PlayerView) :
    playerView runtime leaks (liftPlayerView runtime leaks view) = view := by
  cases view
  rfl

@[simp] theorem liftPlayerView_playerView
    (view : (runtime.recoveryApplication leaks).PlayerView) (empty : view.application.2 = ∅) :
    liftPlayerView runtime leaks (playerView runtime leaks view) = view := by
  cases view with
  | mk messages application receipts =>
    rcases application with ⟨native, excluded⟩
    change excluded = ∅ at empty
    subst excluded
    rfl

@[simp] theorem playerEntry_liftPlayerEntry
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) :
    playerEntry runtime leaks (liftPlayerEntry runtime leaks entry) = entry := by
  cases entry
  simp only [liftPlayerEntry, playerEntry, playerView_liftPlayerView, action_liftAction]

@[simp] theorem liftPlayerEntry_playerEntry
    (entry : (runtime.recoveryApplication leaks).PlayerEntry)
    (empty : entry.beforeView.application.2 = ∅) :
    liftPlayerEntry runtime leaks (playerEntry runtime leaks entry) = entry := by
  cases entry with
  | mk before response emitted =>
    simp only [liftPlayerEntry, playerEntry, liftPlayerView_playerView runtime leaks before empty,
      liftAction_action]

@[simp] theorem environmentView_liftEnvironmentView
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
    environmentView runtime leaks (liftEnvironmentView runtime leaks view) = view := by
  cases view
  rfl

@[simp] theorem liftEnvironmentView_environmentView
    (view : (runtime.recoveryApplication leaks).EnvironmentView) (empty : view.application.2 = ∅) :
    liftEnvironmentView runtime leaks (environmentView runtime leaks view) = view := by
  cases view with
  | mk network application receipts =>
    rcases application with ⟨native, excluded⟩
    change excluded = ∅ at empty
    subst excluded
    rfl

@[simp] theorem command_liftCommand (entry : (runtime.reactiveApplication leaks).Command) :
    command runtime leaks (liftCommand runtime leaks entry) = entry := by
  cases entry <;> rfl

@[simp] theorem liftCommand_command (entry : (runtime.recoveryApplication leaks).Command) :
    liftCommand runtime leaks (command runtime leaks entry) = entry := by
  cases entry <;> rfl

@[simp] theorem environmentEntry_liftEnvironmentEntry
    (entry : (runtime.reactiveApplication leaks).EnvironmentEntry) :
    environmentEntry runtime leaks (liftEnvironmentEntry runtime leaks entry) = entry := by
  cases entry
  simp only [liftEnvironmentEntry, environmentEntry, environmentView_liftEnvironmentView,
    command_liftCommand]

@[simp] theorem liftEnvironmentEntry_environmentEntry
    (entry : (runtime.recoveryApplication leaks).EnvironmentEntry)
    (empty : entry.beforeView.application.2 = ∅) :
    liftEnvironmentEntry runtime leaks (environmentEntry runtime leaks entry) = entry := by
  cases entry with
  | mk before operation =>
    simp only [liftEnvironmentEntry, environmentEntry,
      liftEnvironmentView_environmentView runtime leaks before empty, liftCommand_command]

@[simp] theorem execution_liftExecution (current : (runtime.reactiveApplication leaks).Execution) :
    execution runtime leaks (liftExecution runtime leaks current) = current := by
  cases current
  simp only [liftExecution, execution, List.map_map, Function.comp_def, playerEntry_liftPlayerEntry,
    environmentEntry_liftEnvironmentEntry, List.map_id_fun', id_eq]

/-- Projection is reversible when both the current and all recalled exclusion
flags are empty. Actual clear recovery histories satisfy these conditions. -/
theorem liftExecution_execution_of_clear (current : (runtime.recoveryApplication leaks).Execution)
    (empty : current.application.excluded = ∅)
    (ownClear : ∀ who entry, entry ∈ current.recall who → entry.beforeView.application.2 = ∅)
    (environmentClear : ∀ entry ∈ current.environmentRecall,
      entry.beforeView.application.2 = ∅) :
    liftExecution runtime leaks (execution runtime leaks current) = current := by
  have applicationEq : (⟨current.application.native, ∅⟩ : RecoveryState graph) =
      current.application := by
    cases same : current.application with
    | mk native excluded =>
      have flags : excluded = ∅ := by simpa only [same] using empty
      subst excluded
      rfl
  have ownMap (who : Player) :
      (current.recall who).map (fun entry =>
        liftPlayerEntry runtime leaks (playerEntry runtime leaks entry)) = current.recall who := by
    calc
      _ = (current.recall who).map id := List.map_congr_left fun entry member =>
        liftPlayerEntry_playerEntry runtime leaks entry (ownClear who entry member)
      _ = _ := List.map_id _
  have environmentMap :
      current.environmentRecall.map (fun entry =>
        liftEnvironmentEntry runtime leaks (environmentEntry runtime leaks entry)) =
        current.environmentRecall := by
    calc
      _ = current.environmentRecall.map id := List.map_congr_left fun entry member =>
        liftEnvironmentEntry_environmentEntry runtime leaks entry (environmentClear entry member)
      _ = _ := List.map_id _
  change (⟨⟨current.application.native, ∅⟩, current.network, current.receipts,
    fun who => ((current.recall who).map (playerEntry runtime leaks)).map
      (liftPlayerEntry runtime leaks),
    (current.environmentRecall.map (environmentEntry runtime leaks)).map
      (liftEnvironmentEntry runtime leaks)⟩ :
      (runtime.recoveryApplication leaks).Execution) = current
  simp only [List.map_map, Function.comp_def, applicationEq, ownMap, environmentMap]

/-- On an actual clear recovery history, every recorded exclusion flag is
clear too, so native projection and clear lifting recover the full execution. -/
theorem liftExecution_execution_of_history_clear
    (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (current : (runtime.recoveryApplication leaks).Control)
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some current)) (empty : current.execution.application.excluded = ∅) :
    liftExecution runtime leaks (execution runtime leaks current.execution) =
      current.execution := by
  let app := runtime.recoveryApplication leaks
  have monotone : app.StepRelation (fun before after => before.excluded ⊆ after.excluded) :=
    recoveryApplication_exclusion_monotone runtime leaks
  have lowerInvariant (lower : Finset Player) :
      app.Invariant (fun state => lower ⊆ state.excluded) := {
    submit := fun state who submission holds => holds.trans (monotone.submit state who submission)
    handle := fun state message next holds accepted =>
      holds.trans (monotone.handle state message next accepted)
    environment := fun state command next holds realized =>
      holds.trans (monotone.environment state command next realized) }
  have ownBound := app.recallBound_history (fun observation => observation.2)
    (fun state => state.excluded) (fun _ _ => rfl) lowerInvariant
    initial horizon scheduler current trace
  let environmentBound : app.Execution → Prop := fun current =>
    ∀ entry ∈ current.environmentRecall,
      entry.beforeView.application.2 ⊆ current.application.excluded
  have environmentInvariant : app.ServiceInvariant scheduler environmentBound := {
    respond := by
      intro current who response holds entry member
      rw [app.respond_environmentRecall] at member
      exact (holds entry member).trans (monotone.respond current who response)
    environment := by
      intro current next command holds _selected moved entry member
      rw [app.environmentStep_environmentRecall current next command moved] at member
      rcases List.mem_append.mp member with earlier | latest
      · exact (holds entry earlier).trans (monotone.environmentStep current next command moved)
      · have same := List.mem_singleton.mp latest
        subst entry
        exact monotone.environmentStep current next command moved }
  have environmentBounded := environmentInvariant.history initial horizon
    (fun _ _ entry member => False.elim (List.not_mem_nil member)) trace
  apply liftExecution_execution_of_clear runtime leaks current.execution empty
  · intro who entry member
    have bound : entry.beforeView.application.2 ⊆ current.execution.application.excluded :=
      ownBound who entry member
    rw [empty] at bound
    exact Finset.subset_empty.mp bound
  · intro entry member
    have bound : entry.beforeView.application.2 ⊆ current.execution.application.excluded :=
      environmentBounded entry member
    rw [empty] at bound
    exact Finset.subset_empty.mp bound

end Vegas.EventGraphRuntime.RecoveryProjection

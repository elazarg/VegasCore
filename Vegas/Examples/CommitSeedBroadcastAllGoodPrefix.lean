/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparedPrefix
import Vegas.Examples.CommitSeedBroadcastCallbackSurgery
import Interaction.ReactiveControlOccupation
import Mathlib.Data.List.NodupEquivFin

/-! # Actual all-good native prefixes retaining every original preparation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def allGoodSeed (order : Equiv.Perm Player) : Seeds := (order, fun _ => true)

theorem response_publicView (execution : app.Execution) (owner : Player)
    (action : app.Action) :
    (execution.respond app owner action).application.publicView =
      execution.application.publicView := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material => exact PhaseCount.submit_publicView execution.application owner material

theorem activation_metadata (players : Player → app.Policy) (owner : Player)
    (execution next : app.Execution)
    (reached : next ∈ (app.dispatch players (.activate owner) execution).support) :
    next.application.publicView = execution.application.publicView ∧
      next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  have word := app.dispatch_environmentRecall players (.activate owner) execution next reached
  have length := congrArg List.length word
  simp only [List.length_append, List.length_singleton] at length
  refine ⟨?_, length⟩
  rw [ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind] at reached
  change next ∈ ((players owner _ _).map _).support at reached
  obtain ⟨action, _chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  exact response_publicView _ owner action

theorem allGood_prefix_choice (order : Equiv.Perm Player) (index : Fin 3)
    (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5 + index.val) :
    family (allGoodSeed order) execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate (order index)) := by
  have original : execution.application.attempt = originalAttempt :=
    (congrArg PhasePublicView.attempt publicView).trans quietStart_attempt
  have readyOwner (owner : Player) : ready owner (bindingEvent owner)
      (execution.observeEnvironment app) = true := by
    simp only [ready, decide_eq_true_eq]
    change PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, bindingEvent owner⟩
    rw [original, publicView]
    exact quietStart_public_requests owner
  rw [family, choose_original _ _ _ original, position]
  fin_cases index <;>
    simp only [allGoodSeed, originalCommand, pollCommand, ite_true, activateReady, readyOwner] <;>
    rfl

private theorem allGood_prefix_round (order : Equiv.Perm Player) (index : Fin 3)
    (players : Player → app.Policy) (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5 + index.val) :
    app.round (family (allGoodSeed order)) players execution =
      app.dispatch players (.activate (order index)) execution := by
  unfold ReactiveApplication.round
  rw [allGood_prefix_choice order index execution publicView position, PMF.pure_bind]

/-- Before the shared inclusion block the actual original command stream is
the chosen permutation's callback prefix. Early packets need not be absent. -/
theorem allGood_prefix_commands (order : Equiv.Perm Player) (players : Player → app.Policy)
    (count : Nat) (bounded : count ≤ 3) (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5) :
    app.runRounds (family (allGoodSeed order)) players count execution =
      commandComposition players (((List.ofFn order).take count).map
        ReactiveApplication.Command.activate) execution := by
  interval_cases count
  · rfl
  · change (app.round (family (allGoodSeed order)) players execution).bind PMF.pure =
      (app.dispatch players (.activate (order 0)) execution).bind PMF.pure
    rw [allGood_prefix_round order 0 players execution publicView (by simpa using position)]
  · change (app.round (family (allGoodSeed order)) players execution).bind (fun first =>
        (app.round (family (allGoodSeed order)) players first).bind PMF.pure) =
      (app.dispatch players (.activate (order 0)) execution).bind fun first =>
        (app.dispatch players (.activate (order 1)) first).bind PMF.pure
    rw [allGood_prefix_round order 0 players execution publicView (by simpa using position)]
    apply bind_congr_on_support
    intro first reached
    obtain ⟨firstPublic, firstPosition⟩ := activation_metadata players _ execution first reached
    rw [allGood_prefix_round order 1 players first (firstPublic.trans publicView)
      (by omega)]
  · change (app.round (family (allGoodSeed order)) players execution).bind (fun first =>
        (app.round (family (allGoodSeed order)) players first).bind fun second =>
          (app.round (family (allGoodSeed order)) players second).bind PMF.pure) =
      (app.dispatch players (.activate (order 0)) execution).bind fun first =>
        (app.dispatch players (.activate (order 1)) first).bind fun second =>
          (app.dispatch players (.activate (order 2)) second).bind PMF.pure
    rw [allGood_prefix_round order 0 players execution publicView (by simpa using position)]
    apply bind_congr_on_support
    intro first reached
    obtain ⟨firstPublic, firstPosition⟩ := activation_metadata players _ execution first reached
    rw [allGood_prefix_round order 1 players first (firstPublic.trans publicView) (by omega)]
    apply bind_congr_on_support
    intro second moved
    obtain ⟨secondPublic, secondPosition⟩ := activation_metadata players _ first second moved
    rw [allGood_prefix_round order 2 players second
      (secondPublic.trans (firstPublic.trans publicView)) (by omega)]

theorem allGood_prefix_physical (order : Equiv.Perm Player) (players : Player → app.Policy)
    (count : Nat) (bounded : count ≤ 3) (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5) :
    (app.runRounds (family (allGoodSeed order)) players count execution).map physicalExecution =
      physicalCallbacks players ((List.ofFn order).take count) execution := by
  rw [allGood_prefix_commands order players count bounded execution publicView position,
    commandComposition_physical]
  rfl

private theorem commandCallbacks_publicView (players : Player → app.Policy)
    (owners : List Player) (execution next : app.Execution)
    (reached : next ∈ (commandComposition players
      (owners.map ReactiveApplication.Command.activate) execution).support) :
    next.application.publicView = execution.application.publicView := by
  induction owners generalizing execution with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons owner owners ih =>
      change next ∈ ((app.dispatch players (.activate owner) execution).bind
        (commandComposition players (owners.map ReactiveApplication.Command.activate))).support
        at reached
      obtain ⟨middle, moved, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (ih middle future).trans (activation_metadata players owner execution middle moved).1

theorem allGood_prefix_metadata (order : Equiv.Perm Player) (players : Player → app.Policy)
    (count : Nat) (bounded : count ≤ 3) (execution next : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5)
    (reached : next ∈
      (app.runRounds (family (allGoodSeed order)) players count execution).support) :
    next.application.publicView = quietStart.application.publicView ∧
      next.environmentRecall.length = 5 + count := by
  refine ⟨?_, ?_⟩
  · rw [allGood_prefix_commands order players count bounded execution publicView position]
      at reached
    exact (commandCallbacks_publicView players _ execution next reached).trans publicView
  · rw [app.runRounds_environmentRecall_length _ _ _ execution next reached, position]

/-- A retained callback-kernel prefix is realized by the literal initialized
all-good scheduler, retaining its true command history rather than installing a new prior. -/
theorem allGood_prefix_realizes (oldSeed : Seeds) (order : Equiv.Perm Player)
    (players : Player → app.Policy) (frame next : app.Execution) (count : Nat) (bounded : count ≤ 3)
    (started : frame ∈ (app.runRounds (family oldSeed) players 5 initialExecution).support)
    (publicView : frame.application.publicView = quietStart.application.publicView)
    (position : frame.environmentRecall.length = 5)
    (reached : next ∈ (physicalCallbacks players ((List.ofFn order).take count) frame).support) :
    ∃ actual ∈ (app.runRounds (family (allGoodSeed order)) players (5 + count)
      initialExecution).support,
      physicalExecution actual = next ∧
      actual.application.publicView = quietStart.application.publicView ∧
      actual.environmentRecall.length = 5 + count := by
  have initialSame := first_five_seed_independent oldSeed (allGoodSeed order) players
  rw [initialSame] at started
  rw [← allGood_prefix_physical order players count bounded frame publicView position] at reached
  obtain ⟨actual, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  obtain ⟨actualPublic, actualPosition⟩ := allGood_prefix_metadata order players count bounded
    frame actual publicView position supported
  refine ⟨actual, ?_, same, actualPublic, actualPosition⟩
  rw [app.runRounds_add, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨frame, started, supported⟩

/-- The final command is the genuine original focal activation, so the
retained full input also has its actual occupation-law and legal raw actor witness. -/
theorem allGood_focal_decision (oldSeed : Seeds) (order : Equiv.Perm Player)
    (players : Player → app.Policy) (frame next : app.Execution) (count : Nat) (bounded : count < 3)
    (started : frame ∈ (app.runRounds (family oldSeed) players 5 initialExecution).support)
    (publicView : frame.application.publicView = quietStart.application.publicView)
    (position : frame.environmentRecall.length = 5)
    (reached : next ∈ (physicalCallbacks players ((List.ofFn order).take count) frame).support) :
    ∃ actual, physicalExecution actual = next ∧
      actual ∈ (app.runRounds (family (allGoodSeed order)) players (5 + count)
        initialExecution).support ∧
      some ⟨horizon - (5 + count) - 1, some (order ⟨count, bounded⟩),
        completeActivation actual (order ⟨count, bounded⟩)⟩ ∈
        (app.commandControlLaw (family (allGoodSeed order)) players initial
          (horizon - (5 + count) - 1) (5 + count)).support ∧
      Nonempty ((app.protocol initial horizon (family (allGoodSeed order))).Trace
        (some ⟨horizon - (5 + count) - 1, some (order ⟨count, bounded⟩),
          completeActivation actual (order ⟨count, bounded⟩)⟩)) := by
  obtain ⟨actual, supported, same, actualPublic, actualPosition⟩ :=
    allGood_prefix_realizes oldSeed order players frame next count (by omega) started
      publicView position reached
  have selected := allGood_prefix_choice order ⟨count, bounded⟩ actual actualPublic actualPosition
  have observed : completeActivation actual (order ⟨count, bounded⟩) ∈
      (actual.environmentStep app (.activate (order ⟨count, bounded⟩))).support := by
    rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff ..).mpr rfl
  have rounds : actual ∈ (app.roundsFrom initial (family (allGoodSeed order)) players
      (5 + count)).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using supported
  obtain ⟨prior⟩ := app.raw_trace_roundsFrom initial horizon (family (allGoodSeed order)) players
    (5 + count) (by change 5 + count ≤ 128; omega) actual rounds
  have total : horizon - (5 + count) = horizon - (5 + count) - 1 + 1 := by
    change 128 - (5 + count) = 128 - (5 + count) - 1 + 1
    omega
  rw [total] at prior
  have legal := app.raw_trace_environment initial horizon (family (allGoodSeed order))
    (horizon - (5 + count) - 1) actual (completeActivation actual (order ⟨count, bounded⟩))
    (.activate (order ⟨count, bounded⟩)) prior
    (by rw [selected]; exact (PMF.mem_support_pure_iff ..).mpr rfl) observed
  refine ⟨actual, same, supported, ?_, legal⟩
  unfold ReactiveApplication.commandControlLaw
  rw [initial, PMF.pure_bind, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨actual, supported, ?_⟩
  rw [selected, PMF.pure_bind]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, observed, rfl⟩

end Vegas.Examples.CommitSeedBroadcast

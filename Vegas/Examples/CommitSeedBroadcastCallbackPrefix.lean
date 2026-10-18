/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAllGoodPrefix

/-! # Actual original callback prefixes before the focal first-late response -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem callback_command_metadata (players : Player → app.Policy)
    (command : app.Command) (allowed : command = .wait ∨ ∃ owner, command = .activate owner)
    (execution next : app.Execution)
    (reached : next ∈ (app.dispatch players command execution).support) :
    next.application.publicView = execution.application.publicView ∧
      next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  have word := app.dispatch_environmentRecall players command execution next reached
  have length := congrArg List.length word
  simp only [List.length_append, List.length_singleton] at length
  refine ⟨?_, length⟩
  rcases allowed with rfl | ⟨owner, rfl⟩
  · have same : next = { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .wait⟩] } := by
      simpa only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, PMF.mem_support_pure_iff] using reached
    rw [same]
  · exact (activation_metadata players owner execution next reached).1

private theorem firstLateCommand_allowed (seed : Seeds) (index : Fin 9) :
    ((firstLateCommands seed)[index.val]?).getD .wait = .wait ∨
      ∃ owner, ((firstLateCommands seed)[index.val]?).getD .wait = .activate owner := by
  have inside : index.val < (firstLateCommands seed).length := by
    simpa only [firstLateCommands, List.length_cons, List.length_nil] using index.isLt
  apply firstLateCommands_permitted seed
  rw [List.getElem?_eq_getElem inside, Option.getD_some]
  exact List.getElem_mem inside

theorem good_prefix_choice (seed : Seeds) (index : Fin 3)
    (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5 + index.val) :
    family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (((firstLateCommands seed)[index.val]?).getD .wait) := by
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
    simp only [originalCommand, pollCommand, firstLateCommands, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, activateReady, readyOwner, ite_true]

private theorem good_prefix_run_metadata (seed : Seeds) (players : Player → app.Policy)
    (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5) (count : Nat) (within : count ≤ 3)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players count execution).support) :
    next.application.publicView = execution.application.publicView ∧
      next.environmentRecall.length = 5 + count := by
  induction count generalizing next with
  | zero =>
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst next
      exact ⟨rfl, position⟩
  | succ count ih =>
      rw [app.runRounds_add (family seed) players count 1, PMF.support_bind] at reached
      obtain ⟨before, prefixReached, last⟩ := Set.mem_iUnion₂.mp reached
      have previous := ih (by omega) before prefixReached
      have selected := good_prefix_choice seed ⟨count, by omega⟩ before
        (previous.1.trans publicView) previous.2
      have round : next ∈ (app.round (family seed) players before).support := by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using last
      rw [ReactiveApplication.round, selected, PMF.pure_bind] at round
      have metadata := callback_command_metadata players _
        (firstLateCommand_allowed seed ⟨count, by omega⟩) before next round
      exact ⟨metadata.1.trans previous.1, by omega⟩

theorem good_prefix_commands (seed : Seeds) (players : Player → app.Policy)
    (count : Nat) (bounded : count ≤ 3) (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5) :
    app.runRounds (family seed) players count execution =
      commandComposition players ((firstLateCommands seed).take count) execution := by
  have fullLength : (firstLateCommands seed).length = 9 := rfl
  have length : ((firstLateCommands seed).take count).length = count :=
    List.length_take_of_le (by omega)
  have actual := runRounds_commandComposition seed players ((firstLateCommands seed).take count)
    execution (by
      intro used inside next reached
      have smaller : used < count := by omega
      have metadata := good_prefix_run_metadata seed players execution publicView position used
        (by omega) next reached
      have selected := good_prefix_choice seed ⟨used, by omega⟩ next
        (metadata.1.trans publicView) metadata.2
      simpa only [List.getElem?_take, smaller, ite_true] using selected)
  rwa [length] at actual

theorem good_prefix_physical_kernel (seed : Seeds) (players : Player → app.Policy)
    (count : Nat) (bounded : count ≤ 3) (execution : app.Execution)
    (publicView : execution.application.publicView = quietStart.application.publicView)
    (position : execution.environmentRecall.length = 5) :
    (app.runRounds (family seed) players count execution).map physicalExecution =
      physicalCallbacks players (((firstLateCommands seed).take count).filterMap
        (fun command => command.actor? app)) execution := by
  rw [good_prefix_commands seed players count bounded execution publicView position]
  apply commandComposition_callbacks
  intro command member
  exact firstLateCommands_permitted seed command (List.mem_of_mem_take member)

theorem callbackComposition_publicView (players : Player → app.Policy)
    (commands : List app.Command)
    (allowed : ∀ command ∈ commands, command = .wait ∨ ∃ owner, command = .activate owner)
    (execution final : app.Execution)
    (reached : final ∈ (commandComposition players commands execution).support) :
    final.application.publicView = execution.application.publicView := by
  induction commands generalizing execution with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons command commands ih =>
      change final ∈ ((app.dispatch players command execution).bind
        (commandComposition players commands)).support at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have initial := callback_command_metadata players command
        (allowed command (List.mem_cons_self ..)) execution middle moved
      exact (ih (fun next member => allowed next (List.mem_cons_of_mem command member))
        middle later).trans initial.1

/-- A partial no-helper block uses the same literal command prefix as the
complete replay theorem. The initial native preparations remain unchanged. -/
theorem nohelper_prefix_physical_kernel (seed : Seeds) (players : Player → app.Policy)
    (count : Nat) (bounded : count ≤ 9) (execution : app.Execution)
    (valid : NoHelperBlock execution) (position : execution.environmentRecall.length = 5) :
    (app.runRounds (family seed) players count execution).map physicalExecution =
      physicalCallbacks players (((firstLateCommands seed).take count).filterMap
        (fun command => command.actor? app)) execution := by
  have fullLength : (firstLateCommands seed).length = 9 := rfl
  have length : ((firstLateCommands seed).take count).length = count :=
    List.length_take_of_le (by omega)
  have actual := runRounds_commandComposition seed players ((firstLateCommands seed).take count)
    execution (by
      intro used inside next reached
      have smaller : used < count := by omega
      have nextValid := noHelperBlock_run seed players execution valid position used
        (by omega) next reached
      have nextPosition : next.environmentRecall.length = 5 + used := by
        rw [app.runRounds_environmentRecall_length _ _ _ execution next reached, position]
      have selected := noHelperBlock_command seed used (by omega) next nextValid nextPosition
      simpa only [List.getElem?_take, smaller, ite_true] using selected)
  rw [length] at actual
  rw [actual]
  apply commandComposition_callbacks
  intro command member
  exact firstLateCommands_permitted seed command (List.mem_of_mem_take member)

end Vegas.Examples.CommitSeedBroadcast

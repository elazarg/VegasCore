/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCallbackPrefix
import Vegas.Examples.CommitSeedBroadcastFirstLateEmptyLedger
import Interaction.ReactiveRoundTrace

/-! # Genuine raw first-late histories retain their original callback frame -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- A genuine off-path raw input is reached by the existing uniform response
family. Its initialized raw preparation frame and literal final activation are retained. -/
theorem original_first_late_run_prefix (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2) :
    ∃ used : Nat, ∃ frame before : app.Execution,
      used < 9 ∧
      frame ∈ (app.runRounds (family seed) rawMenu.uniformResponses 5 initialExecution).support ∧
      before ∈ (app.runRounds (family seed) rawMenu.uniformResponses used frame).support ∧
      frame.application.publicView = quietStart.application.publicView ∧
      frame.environmentRecall.length = 5 ∧
      before.environmentRecall.length = 5 + used ∧
      execution = completeActivation before owner ∧
      family seed before.environmentRecall (before.observeEnvironment app) =
        PMF.pure (.activate owner) ∧
      (used ≤ 2 ∧ seed.2 owner = true ∨ 6 ≤ used ∧ seed.2 owner = false) := by
  have placement := original_first_late_input_placement seed
    ⟨remaining, some owner, execution⟩ (rawMenu.toRawTrace initial horizon (family seed) trace)
    owner rfl original clock
  have supported := rawMenu.roundSupported_uniform initial horizon (family seed) trace
  obtain ⟨_budget, count, before, command, position, prior, selected, actor, moved⟩ := supported
  have commandEq : command = .activate owner := by
    cases command <;> simp_all only [ReactiveApplication.Command.actor?,
      Option.some.injEq, reduceCtorEq]
  subst command
  have observed : execution = completeActivation before owner := by
    rw [completeActivation_law, PMF.mem_support_pure_iff] at moved
    exact moved
  have chosen : family seed before.environmentRecall (before.observeEnvironment app) =
      PMF.pure (.activate owner) := by
    change _ ∈ (PMF.pure (choose seed before.environmentRecall
      (before.observeEnvironment app))).support at selected
    rw [PMF.mem_support_pure_iff] at selected
    exact congrArg PMF.pure selected.symm
  have countLower : 5 ≤ count := by
    rcases placement with good | bad <;> omega
  have countUpper : count < 14 := by
    rcases placement with good | bad <;> omega
  have priorRun : before ∈ (app.runRounds (family seed) rawMenu.uniformResponses
      count initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using prior
  rw [show count = 5 + (count - 5) by omega, app.runRounds_add, PMF.support_bind] at priorRun
  obtain ⟨frame, started, later⟩ := Set.mem_iUnion₂.mp priorRun
  have initialSupported := started
  rw [first_five_rounds] at initialSupported
  obtain ⟨first, _first, afterFirst⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ initialSupported)
  obtain ⟨second, _second, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  obtain ⟨third, _third, sameFrame⟩ := (PMF.mem_support_map_iff _ _ _).mp afterSecond
  have framePublic : frame.application.publicView = quietStart.application.publicView := by
    rw [← sameFrame]
    exact initialClockTwo_publicView first second third
  have framePosition : frame.environmentRecall.length = 5 := by
    rw [← sameFrame]
    exact initialClockTwo_length first second third
  have beforePosition : before.environmentRecall.length = 5 + (count - 5) := by
    rw [app.runRounds_environmentRecall_length _ _ _ frame before later, framePosition]
  refine ⟨count - 5, frame, before, by omega, started, later, framePublic,
    framePosition, beforePosition, observed, chosen, ?_⟩
  rcases placement with good | bad
  · exact Or.inl ⟨by omega, good.2.2⟩
  · exact Or.inr ⟨by omega, bad.2.2⟩

private theorem frame_snapshot_of_later (seed : Seeds) (players : Player → app.Policy)
    (used : Nat) (frame before execution : app.Execution) (owner : Player)
    (position : frame.environmentRecall.length = 5)
    (reached : before ∈ (app.runRounds (family seed) players used frame).support)
    (observed : execution = completeActivation before owner)
    (empty : EmptyEarlySnapshot execution) : EmptyEarlySnapshot frame := by
  obtain ⟨later, word, _length⟩ := app.runRounds_environmentRecall_append
    (family seed) players used frame before reached
  have snapshot : execution.environmentRecall[3]? = frame.environmentRecall[3]? := by
    rw [observed]
    change (before.environmentRecall ++
      [(⟨before.observeEnvironment app, .activate owner⟩ : app.EnvironmentEntry)])[3]? = _
    rw [word, List.append_assoc, List.getElem?_append_left (by rw [position]; decide)]
  intro entry member
  exact empty entry (by simpa only [snapshot] using member)

private theorem callback_prefix_shape (seed : Seeds) (used : Nat) (inside : used < 9)
    (owner : Player)
    (selected : ((firstLateCommands seed)[used]?).getD .wait = .activate owner) :
    (((firstLateCommands seed).take used).filterMap (fun command => command.actor? app)).Nodup ∧
      owner ∉ ((firstLateCommands seed).take used).filterMap
        (fun command => command.actor? app) := by
  have bounded : used < (firstLateCommands seed).length := by
    simpa only [firstLateCommands, List.length_cons, List.length_nil] using inside
  have located : (firstLateCommands seed)[used] = .activate owner := by
    simpa only [List.getElem?_eq_getElem bounded, Option.getD_some] using selected
  have whole : ((firstLateCommands seed).filterMap (fun command => command.actor? app)).Nodup := by
    rw [firstLateCommands_callbacks]
    exact nativePartitionedOrder_nodup seed
  have split : ((((firstLateCommands seed).take used).filterMap
      (fun command => command.actor? app)) ++
      ((firstLateCommands seed).drop used).filterMap
        (fun command => command.actor? app)).Nodup := by
    rw [← List.filterMap_append, List.take_append_drop]
    exact whole
  have later : owner ∈ ((firstLateCommands seed).drop used).filterMap
      (fun command => command.actor? app) := by
    rw [List.drop_eq_getElem_cons bounded, located]
    simp only [List.filterMap_cons, ReactiveApplication.Command.actor?, List.mem_cons,
      true_or]
  exact ⟨split.of_append_left, fun earlier =>
    (List.nodup_append.mp split).2.2 owner earlier owner later rfl⟩

/-- Every actual empty-receipt first-late input has the exact original raw
frame and a supported prefix of distinct callbacks which has not yet called its owner. -/
theorem original_first_late_callback_prefix (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = []) :
    ∃ frame final : app.Execution, ∃ owners : List Player,
      frame ∈ (app.runRounds (family seed) rawMenu.uniformResponses 5 initialExecution).support ∧
      owners.Nodup ∧ owner ∉ owners ∧
      final ∈ (physicalCallbacks rawMenu.uniformResponses owners frame).support ∧
      (∀ who, final.recall who = execution.recall who) ∧
      ((completeActivation final owner).recall owner,
        (completeActivation final owner).observe app owner) =
      (execution.recall owner, execution.observe app owner) := by
  obtain ⟨used, frame, before, inside, started, later, framePublic, framePosition,
    beforePosition, observed, selected, placement⟩ :=
    original_first_late_run_prefix seed remaining execution owner trace original clock
  have physical : physicalExecution before ∈
      ((app.runRounds (family seed) rawMenu.uniformResponses used frame).map
        physicalExecution).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨before, later, rfl⟩
  have kernel : (app.runRounds (family seed) rawMenu.uniformResponses used frame).map
      physicalExecution = physicalCallbacks rawMenu.uniformResponses
        (((firstLateCommands seed).take used).filterMap (fun command => command.actor? app))
          frame := by
    rcases placement with good | bad
    · exact good_prefix_physical_kernel seed rawMenu.uniformResponses used (by omega)
        frame framePublic framePosition
    · have currentEmpty := bad_firstLate_empty_receipts_snapshot seed
        ⟨remaining, some owner, execution⟩
        (rawMenu.toRawTrace initial horizon (family seed) trace) owner rfl original clock
        bad.2 empty
      have initialEmpty := frame_snapshot_of_later seed rawMenu.uniformResponses used frame before
        execution owner framePosition later observed currentEmpty
      exact nohelper_prefix_physical_kernel seed rawMenu.uniformResponses used (by omega) frame
        ⟨framePublic, initialEmpty, by omega⟩ framePosition
  have prescribed : family seed before.environmentRecall (before.observeEnvironment app) =
      PMF.pure (((firstLateCommands seed)[used]?).getD .wait) := by
    rcases placement with good | bad
    · have goodRun := later
      rw [good_prefix_commands seed rawMenu.uniformResponses used (by omega) frame framePublic
        framePosition] at goodRun
      have beforePublic := (callbackComposition_publicView rawMenu.uniformResponses
        ((firstLateCommands seed).take used) (fun command member =>
          firstLateCommands_permitted seed command (List.mem_of_mem_take member))
        frame before goodRun).trans framePublic
      exact good_prefix_choice seed ⟨used, by omega⟩ before beforePublic beforePosition
    · have currentEmpty := bad_firstLate_empty_receipts_snapshot seed
        ⟨remaining, some owner, execution⟩
        (rawMenu.toRawTrace initial horizon (family seed) trace) owner rfl original clock
        bad.2 empty
      have initialEmpty := frame_snapshot_of_later seed rawMenu.uniformResponses used frame before
        execution owner framePosition later observed currentEmpty
      have valid : NoHelperBlock frame := ⟨framePublic, initialEmpty, by omega⟩
      exact noHelperBlock_command seed used inside before
        (noHelperBlock_run seed rawMenu.uniformResponses frame valid framePosition used
          (by omega) before later) beforePosition
  have actor : ((firstLateCommands seed)[used]?).getD .wait = .activate owner := by
    have member : (.activate owner : app.Command) ∈
        (PMF.pure (((firstLateCommands seed)[used]?).getD .wait)).support := by
      rw [← prescribed, selected]
      exact (PMF.mem_support_pure_iff ..).mpr rfl
    exact ((PMF.mem_support_pure_iff ..).mp member).symm
  obtain ⟨distinct, absent⟩ := callback_prefix_shape seed used inside owner actor
  refine ⟨frame, physicalExecution before,
    ((firstLateCommands seed).take used).filterMap (fun command => command.actor? app),
    started, distinct, absent, kernel ▸ physical, ?_, ?_⟩
  · intro who
    rw [observed]
    rfl
  · rw [observed]
    rfl

end Vegas.Examples.CommitSeedBroadcast

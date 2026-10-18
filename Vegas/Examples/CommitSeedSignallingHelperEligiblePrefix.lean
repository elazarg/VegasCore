/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperPendingAcceptance
import Vegas.Examples.CommitSeedSignallingOriginalLateAdmission
import Interaction.ReactiveRoundTrace

/-! # The passive gap following an eligible original helper response -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- After the eligible clock-two response, the actual Bob helper include and
the other Alice poll leave her original request pending at her late include.
The current response may have any counted private preparation or evidence. -/
theorem helper_clock_two_eligible_prefix (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = false)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (identified : marker.id = (bob, 0)) (permitted : PhaseCount.permits [] marker = true)
    (action : app.Action)
    (offered : action ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players 2
      (execution.respond app alice action)).support) :
    next.application.SeedRequest alice (originalCoordinate alice) ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob next ∧
      next.environmentRecall.length = lateIncludePosition alice (seedBits seed alice) ∧
      next.recall alice = (execution.respond app alice action).recall alice ∧
      Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
        (some ⟨remaining - 2, none, next⟩)) := by
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have sourceOriginal : execution.application.attempt = originalAttempt := request.1.symm
  have count := original_first_late_input_index seed ⟨remaining, some alice, execution⟩ rawFixed
    alice rfl sourceOriginal clock
  change execution.environmentRecall.length = 4 + if seedBits seed alice then 3 else 1 at count
  have position : execution.environmentRecall.length = 5 := by
    rw [bit] at count
    simpa only [Bool.false_eq_true, ite_false] using count
  obtain ⟨repliedTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution alice action fixed offered
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed)
    repliedTrace).1
  have replyLength : (execution.respond app alice action).environmentRecall.length = 5 := by
    rw [ReactiveApplication.respond_environmentRecall]
    exact position
  have enough : 2 ≤ remaining := by
    rw [replyLength] at accounted
    change 5 + remaining = 64 at accounted
    omega
  rw [ReactiveApplication.runRounds, PMF.support_bind] at reached
  obtain ⟨before, moved, later⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨bobAccepted, aliceRequest, beforeLength⟩ := helper_pending_binding_accepted_next seed
    remaining execution mixed rawFixed bit request clock quiet marker input sender identified
      permitted action offered players before moved
  have replyBudget : remaining = (remaining - 1) + 1 := by omega
  have roundTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 1) + 1, none, execution.respond app alice action⟩) := by
    rw [← replyBudget]
    exact repliedTrace
  obtain ⟨beforeTrace⟩ := countedMenu.trace_round initial horizon (family seed) players covered
    (remaining - 1) (execution.respond app alice action) before roundTrace moved
  have original : before.application.attempt = originalAttempt := aliceRequest.1.symm
  have command : family seed before.environmentRecall (before.observeEnvironment app) =
      PMF.pure (ReactiveApplication.Command.wait : app.Command) := by
    rw [family_apply, choose_original seed _ _ original, beforeLength]
    change PMF.pure (pollCommand alice (seed.2 (originalAddress alice)) true _) = _
    change seed.2 (originalAddress alice) = false at bit
    simp only [pollCommand, bit, Bool.false_eq_true, ite_false]
  let waited : app.Execution := { before with environmentRecall := before.environmentRecall ++
    [⟨before.observeEnvironment app, .wait⟩] }
  have nextRound : app.round (family seed) players before = PMF.pure waited := by
    rw [ReactiveApplication.round, command, PMF.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  change next ∈ ((app.round (family seed) players before).bind
    (app.runRounds (family seed) players 0)).support at later
  rw [nextRound, PMF.pure_bind, ReactiveApplication.runRounds] at later
  have nextEq := (PMF.mem_support_pure_iff _ _).mp later
  subst next
  have remembered : before.recall alice =
      (execution.respond app alice action).recall alice := by
    obtain ⟨command, chosen, dispatched⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
    obtain ⟨observed, environmentMoved, resumed⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
    have responseOriginal : (execution.respond app alice action).application.attempt =
        originalAttempt := (respond_request runtime leaks execution alice action alice
          (originalCoordinate alice) request).1.symm
    have selected : command = earlyCommand bob
        (execution.respond app alice action).environmentRecall
          ((execution.respond app alice action).observeEnvironment app) := by
      rw [family_apply, choose_original seed _ _ responseOriginal, replyLength] at chosen
      exact (PMF.mem_support_pure_iff _ _).mp chosen
    have passive : command.actor? app = none := by
      rw [selected]
      unfold earlyCommand
      split
      · rfl
      · split
        · rfl
        · unfold pendingCommand
          split <;> rfl
    simp only [ReactiveApplication.resume, passive, PMF.mem_support_pure_iff] at resumed
    subst before
    exact congrFun (app.environmentStep_recall _ _ _ environmentMoved) alice
  have allTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 2) + 2, none, execution.respond app alice action⟩) := by
    rw [show (remaining - 2) + 2 = remaining by omega]
    exact repliedTrace
  have fullReached : waited ∈ (app.runRounds (family seed) players 2
      (execution.respond app alice action)).support := by
    rw [ReactiveApplication.runRounds, PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨before, moved, ?_⟩
    simp only [ReactiveApplication.runRounds, nextRound, PMF.pure_bind,
      PMF.mem_support_pure_iff]
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (remaining - 2) 2 (execution.respond app alice action) waited allTrace fullReached
  refine ⟨aliceRequest, bobAccepted, ?_, remembered, ⟨finalTrace⟩⟩
  change (before.environmentRecall ++ [_]).length = lateIncludePosition alice _
  rw [List.length_append, List.length_singleton, beforeLength, bit]
  rfl

/-- At the eligible clock-three callback the next command is already the
late inclusion. Responding changes neither the original request nor Bob's
existing accepting receipt; arbitrary counted preparation is retained. -/
theorem helper_clock_three_eligible_prefix (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (position : execution.environmentRecall.length = 10)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (action : app.Action)
    (offered : action ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice)) :
    let replied := execution.respond app alice action
    replied.application.SeedRequest alice (originalCoordinate alice) ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob replied ∧
      replied.environmentRecall.length = lateIncludePosition alice (seedBits seed alice) ∧
      Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
        (some ⟨remaining, none, replied⟩)) := by
  dsimp only
  refine ⟨respond_request runtime leaks execution alice action alice (originalCoordinate alice)
    request, ?_, ?_, ?_⟩
  · obtain ⟨packet, input, authored, addressed, named, receipted⟩ := bobAccepted
    refine ⟨packet, ?_, authored, addressed, named, ?_⟩
    · rcases action with ⟨transmission⟩
      cases transmission with
      | none => exact input
      | some material => exact List.mem_append_left _ input
    · rwa [app.respond_receipts]
  · rw [ReactiveApplication.respond_environmentRecall, position, bit]
    rfl
  · exact countedMenu.trace_respond initial horizon (family seed) remaining execution alice action
      fixed offered

end Vegas.Examples.CommitSeedSignalling

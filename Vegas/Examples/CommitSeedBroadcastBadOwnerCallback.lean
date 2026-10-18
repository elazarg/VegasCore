/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperCallbackGap

/-! # An unsent bad owner reaches its actual first-late callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- From an original idle prefix after all initial responses, the owner's
next original callback is derived from the real fixed command stream. -/
theorem bad_owner_firstLate_callback (seed : Seeds) (remaining : Nat)
    (anchor : app.Execution) (owner : Player) (bad : seed.2 owner = false)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, anchor⟩))
    (request : anchor.application.SeedRequest owner (originalCoordinate owner))
    (unsent : ∀ message ∈ app.outputs (anchor.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (started : 5 ≤ anchor.environmentRecall.length)
    (ahead : anchor.environmentRecall.length ≤ 11 + (seed.1.symm owner).val)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players
      ((11 + (seed.1.symm owner).val - anchor.environmentRecall.length) + 1) anchor).support) :
    ∃ before observed action,
      before ∈ (app.runRounds (family seed) players
        (11 + (seed.1.symm owner).val - anchor.environmentRecall.length) anchor).support ∧
      observed = completeActivation before owner ∧
      family seed before.environmentRecall (before.observeEnvironment app) =
        PMF.pure (.activate owner) ∧
      Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
        (some ⟨remaining - (11 + (seed.1.symm owner).val - anchor.environmentRecall.length) - 1,
          some owner, observed⟩)) ∧
      observed.application.SeedRequest owner (originalCoordinate owner) ∧
      observed.application.current.native.clock = 2 ∧ observed.recall owner = anchor.recall owner ∧
      action ∈ (players owner (observed.recall owner) (observed.observe app owner)).support ∧
      next = observed.respond app owner action := by
  classical
  let count := 11 + (seed.1.symm owner).val - anchor.environmentRecall.length
  have budget := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).1
  change anchor.environmentRecall.length + remaining = horizon at budget
  have rankBound := (seed.1.symm owner).isLt
  have target : anchor.environmentRecall.length + count = 11 + (seed.1.symm owner).val := by
    dsimp only [count]
    omega
  have enough : count + 1 ≤ remaining := by dsimp only [horizon] at budget; omega
  rw [app.runRounds_add] at reached
  obtain ⟨before, prior, finalRound⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have beforeTraceStart : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - count) + count, none, anchor⟩) := by
    have difference : remaining - count + count = remaining := by omega
    rw [difference]
    exact trace
  have avoids : ∀ position, anchor.environmentRecall.length ≤ position →
      position < anchor.environmentRecall.length + count → position ∉ originalTurns seed owner := by
    intro position lower upper member
    simp only [originalTurns, bad, Bool.false_eq_true, ite_false, List.mem_cons,
      List.not_mem_nil, or_false] at member
    have ownerBound := owner.isLt
    omega
  obtain ⟨beforeRequest, beforeWord, beforeLength⟩ := original_unsent_interval_run seed owner
    (remaining - count) count anchor before beforeTraceStart request unsent avoids (by omega)
      players covered prior
  have beforePosition : before.environmentRecall.length = 11 + (seed.1.symm owner).val := by omega
  obtain ⟨beforeTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (remaining - count) count anchor before beforeTraceStart prior
  have valid := raw_native_valid (family seed) _
    (countedMenu.toRawTrace initial horizon (family seed) beforeTrace)
  have readyOwner : ready owner (bindingEvent owner) (before.observeEnvironment app) = true := by
    apply decide_eq_true
    change PhaseRuntimeState.requests before.application.publicView owner
      ⟨before.application.attempt, bindingEvent owner⟩
    rw [beforeRequest.1.symm]
    exact (before.application.requests_publicView valid owner (originalCoordinate owner)).mpr
      beforeRequest
  have selected : family seed before.environmentRecall (before.observeEnvironment app) =
      PMF.pure (.activate owner) := by
    rw [family, choose_original _ _ _ beforeRequest.1.symm]
    apply congrArg PMF.pure
    apply (original_command_activation seed owner _ _ _ readyOwner).mpr
    rw [beforePosition]
    simp [originalTurns, bad]
  have first : next ∈ (app.round (family seed) players before).support := by
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using finalRound
  rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
    completeActivation_law, PMF.pure_bind] at first
  change next ∈ ((players owner _ _).map _).support at first
  obtain ⟨action, chosen, same⟩ := (PMF.mem_support_map_iff _ _ _).mp first
  let observed := completeActivation before owner
  have priorRemaining : remaining - count = (remaining - count - 1) + 1 := by omega
  rw [priorRemaining] at beforeTrace
  obtain ⟨observedTrace⟩ := countedMenu.trace_environment initial horizon (family seed)
    (remaining - count - 1) before observed (.activate owner) beforeTrace
      (by rw [selected]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      (by rw [completeActivation_law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have observedClock : observed.application.current.native.clock = 2 := by
    rw [original_clock_index seed _
      (countedMenu.toRawTrace initial horizon (family seed) observedTrace) beforeRequest.1.symm]
    change originalClock observed.environmentRecall.length = 2
    have length : observed.environmentRecall.length = before.environmentRecall.length + 1 := by
      simp only [observed, completeActivation, ReactiveApplication.Execution.sampledActivation,
        List.length_append, List.length_singleton]
    rw [length, beforePosition]
    generalize rankEq : seed.1.symm owner = rank
    fin_cases rank <;> rfl
  exact ⟨before, observed, action, prior, rfl, selected, ⟨observedTrace⟩, beforeRequest,
    observedClock, beforeWord, chosen, same.symm⟩

end Vegas.Examples.CommitSeedBroadcast

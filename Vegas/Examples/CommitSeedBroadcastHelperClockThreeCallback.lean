/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperCallbackPosition

/-! # Waiting at the helper input reaches the actual final original callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Six real scheduler rounds after WAIT preserve the unsent word; the seventh
round activates its owner at clock three and samples the same continuing policy. -/
theorem helper_wait_reaches_clock_three (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (bad : seed.2 owner = false)
    (emptyOutputs : app.outputs (execution.recall owner) = [])
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players 7
      (execution.respond app owner ⟨none⟩)).support) :
    7 ≤ remaining ∧ ∃ before observed action,
      before ∈ (app.runRounds (family seed) players 6
        (execution.respond app owner ⟨none⟩)).support ∧
      observed = completeActivation before owner ∧
      family seed before.environmentRecall (before.observeEnvironment app) =
        PMF.pure (.activate owner) ∧
      Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
        (some ⟨remaining - 7, some owner, observed⟩)) ∧
      observed.application.SeedRequest owner (originalCoordinate owner) ∧
      observed.application.current.native.clock = 3 ∧
      observed.recall owner = (execution.respond app owner ⟨none⟩).recall owner ∧
      action ∈ (players owner (observed.recall owner) (observed.observe app owner)).support ∧
      next = observed.respond app owner action := by
  classical
  have position := bad_firstLate_position seed remaining execution owner trace request clock bad
  have budget := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).1
  change execution.environmentRecall.length + remaining = horizon at budget
  have rankBound := (seed.1.symm owner).isLt
  have enough : 7 ≤ remaining := by dsimp only [horizon] at budget; omega
  let post := execution.respond app owner ⟨none⟩
  obtain ⟨postTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining execution
    owner ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
  have postRequest := respond_request runtime leaks execution owner (⟨none⟩ : app.Action) owner
    (originalCoordinate owner) request
  have postPosition : post.environmentRecall.length = 12 + (seed.1.symm owner).val := position
  have postOutputs : app.outputs (post.recall owner) = [] := by
    simp only [post, ReactiveApplication.Execution.respond, ite_true, ReactiveApplication.outputs,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      List.append_nil]
    exact emptyOutputs
  have unsent : ∀ message ∈ app.outputs (post.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner) := by
    rw [postOutputs]
    exact fun _ member => (List.not_mem_nil member).elim
  have split : (7 : Nat) = 6 + 1 := rfl
  rw [split, app.runRounds_add] at reached
  obtain ⟨before, prior, finalRound⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have beforeTraceStart : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 6) + 6, none, post⟩) := by
    have difference : remaining - 6 + 6 = remaining := by omega
    rw [difference]
    exact postTrace
  obtain ⟨beforeRequest, beforeWord, beforeLength⟩ := original_helper_gap_run seed owner bad
    (remaining - 6) 6 post before beforeTraceStart postRequest unsent (by rw [postPosition]; omega)
      (by rw [postPosition]; omega) players covered prior
  have beforePosition : before.environmentRecall.length = 18 + (seed.1.symm owner).val := by
    omega
  obtain ⟨beforeTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (remaining - 6) 6 post before beforeTraceStart prior
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
    simp [originalTurns]
  have first : next ∈ (app.round (family seed) players before).support := by
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using finalRound
  rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
    completeActivation_law, PMF.pure_bind] at first
  change next ∈ ((players owner _ _).map _).support at first
  obtain ⟨action, chosen, same⟩ := (PMF.mem_support_map_iff _ _ _).mp first
  let observed := completeActivation before owner
  have priorRemaining : remaining - 6 = (remaining - 7) + 1 := by omega
  rw [priorRemaining] at beforeTrace
  obtain ⟨observedTrace⟩ := countedMenu.trace_environment initial horizon (family seed)
    (remaining - 7) before observed (.activate owner) beforeTrace
      (by rw [selected]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      (by rw [completeActivation_law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have observedClock : observed.application.current.native.clock = 3 := by
    rw [original_clock_index seed _
      (countedMenu.toRawTrace initial horizon (family seed) observedTrace) beforeRequest.1.symm]
    change originalClock observed.environmentRecall.length = 3
    have length : observed.environmentRecall.length = before.environmentRecall.length + 1 := by
      simp only [observed, completeActivation, ReactiveApplication.Execution.sampledActivation,
        List.length_append, List.length_singleton]
    rw [length, beforePosition]
    generalize rankEq : seed.1.symm owner = rank
    fin_cases rank <;> rfl
  exact ⟨enough, before, observed, action, prior, rfl, selected, ⟨observedTrace⟩, beforeRequest,
    observedClock, beforeWord, chosen, same.symm⟩

end Vegas.Examples.CommitSeedBroadcast

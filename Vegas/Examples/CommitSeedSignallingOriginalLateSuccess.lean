/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalEmissionCut
import Vegas.Examples.CommitSeedSignallingCorrectSeedProbability

/-! # Eligible original emissions succeed before their resolved endpoint -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem late_command_passive (owner : Player) (seed : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    (lateCommand owner seed clock past view).actor? app = none := by
  classical
  unfold lateCommand
  split
  · cases (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      past view).emissions.find? (fun emitted => emitted.1 = clock) with
    | none => rfl
    | some emitted =>
        change (pendingCommand emitted.2.id view).actor? app = none
        unfold pendingCommand
        split <;> rfl
  · rfl

private theorem original_selected_late_passive (seeds : Seeds) (owner : Player)
    (execution : app.Execution) (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length =
      lateIncludePosition owner (seeds.2 (originalAddress owner))) :
    (choose seeds execution.environmentRecall (execution.observeEnvironment app)).actor? app =
      none := by
  rw [choose_original seeds _ _ original, position, original_late_command]
  exact late_command_passive _ _ _ _ _
/-- Every eligible original counted emission has a true receipt by any resolved
endpoint of its actual initialized history. The inclusion prefix, pending packet,
native admission and retained final receipt are all derived. -/
theorem original_eligible_emission_resolved_accepted (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (resolved : (originalCoordinate owner).Resolved execution.application)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock owner (seeds.2 (originalAddress owner)), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner execution := by
  classical
  by_contra unaccepted
  let position := lateIncludePosition owner (seeds.2 (originalAddress owner))
  let players := countedMenu.uniformResponses
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have finished : 21 ≤ execution.environmentRecall.length := by
    by_contra early
    have request := original_request_of_unaccepted_before_expiry seeds _ raw owner unaccepted
      (by change execution.environmentRecall.length < 21; omega)
    exact resolved.not_request _ _ owner request
  have positionSmall : position < 21 := by
    unfold position lateIncludePosition
    split <;> split <;> decide
  have bounded : position < execution.environmentRecall.length := by omega
  have supported := countedMenu.roundSupported_uniform initial horizon (family seeds) trace
  have initialized := supported.2
  rw [ReactiveApplication.roundsFrom, PMF.support_bind] at initialized
  obtain ⟨state, stateSupport, initialized⟩ := Set.mem_iUnion₂.mp initialized
  rw [initial_eq_pure, PMF.mem_support_pure_iff] at stateSupport
  subst state
  have accounted : execution.environmentRecall.length + remaining = horizon := supported.1
  have fullLength : execution.environmentRecall.length =
      position + (execution.environmentRecall.length - position) := by omega
  rw [fullLength, app.runRounds_add] at initialized
  obtain ⟨before, prior, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ initialized)
  have futureFull := future
  have count : before.environmentRecall.length = position := by
    have length := app.runRounds_environmentRecall_length (family seeds) players position
      initialExecution before prior
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  have sourceSupported : before ∈
      (app.roundsFrom initial (family seeds) players position).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialState, by rw [initial_eq_pure]; simp, prior⟩
  obtain ⟨beforeTrace⟩ := countedMenu.trace_roundsFrom initial horizon (family seeds) players
    (fun who past view action member =>
      (countedMenu.uniformResponses_support who past view action).mp member)
    position (by omega) before sourceSupported
  have beforeUnaccepted : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner before := by
    intro accepted
    exact unaccepted (original_binding_accepted_runRounds (family seeds) players _ before execution
      futureFull owner accepted)
  have sourceRequest := original_request_of_unaccepted_before_expiry seeds _
    (countedMenu.toRawTrace initial horizon (family seeds) beforeTrace) owner beforeUnaccepted
      (by rw [count]; exact positionSmall)
  have sourceOriginal : before.application.attempt = originalAttempt := sourceRequest.1.symm
  have rest : execution.environmentRecall.length - position =
      (execution.environmentRecall.length - position - 1) + 1 := by omega
  rw [rest] at future
  change execution ∈ ((app.round (family seeds) players before).bind
    (app.runRounds (family seeds) players
      (execution.environmentRecall.length - position - 1))).support at future
  obtain ⟨middle, firstRound, following⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ future)
  obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ firstRound)
  obtain ⟨observed, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨later, environment, _length⟩ := app.runRounds_environmentRecall_append (family seeds)
    players (execution.environmentRecall.length - position - 1) middle execution following
  have wholeEnvironment : execution.environmentRecall = before.environmentRecall ++
      (⟨before.observeEnvironment app, command⟩ : app.EnvironmentEntry) :: later := by
    rw [environment, app.dispatch_environmentRecall players command before middle dispatched]
    simp only [List.append_assoc, List.singleton_append]
  have takeEq : execution.environmentRecall.take position = before.environmentRecall := by
    rw [wholeEnvironment, ← count, List.take_left]
  have picked : execution.environmentRecall[position]? =
      some (⟨before.observeEnvironment app, command⟩ : app.EnvironmentEntry) := by
    rw [wholeEnvironment, ← count, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have entryEq := Option.some.inj ((List.getElem?_eq_getElem bounded).symm.trans picked)
  have prefixEmission := original_eligible_emission_before_include countedMenu seeds remaining
    execution trace owner bounded message emitted
  rw [takeEq, entryEq] at prefixEmission
  change (lateClock owner (seeds.2 (originalAddress owner)), message) ∈
    (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      before.environmentRecall (before.observeEnvironment app)).emissions at prefixEmission
  change command ∈ (family seeds before.environmentRecall
    (before.observeEnvironment app)).support at chosen
  rw [family_apply, PMF.mem_support_pure_iff] at chosen
  subst command
  have accepted := original_late_emission_accepted seeds (horizon - position) before observed
    beforeTrace owner count message prefixEmission moved
  have passive := original_selected_late_passive seeds owner before sourceOriginal count
  change middle ∈ (app.resume players
    ((choose seeds before.environmentRecall (before.observeEnvironment app)).actor? app)
      observed).support at resumed
  rw [passive] at resumed
  have middleEq : middle = observed := (PMF.mem_support_pure_iff _ _).mp resumed
  subst middle
  exact unaccepted (original_binding_accepted_runRounds (family seeds) players _ observed execution
    following owner accepted)

end Vegas.Examples.CommitSeedSignalling

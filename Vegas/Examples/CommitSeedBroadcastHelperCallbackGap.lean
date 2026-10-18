/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingExhaustion
import Vegas.Examples.CommitSeedBroadcastFirstLateProvenance
import Vegas.Examples.CommitSeedBroadcastInitialQuiet
import Vegas.Pending.PhaseReadyResolution
import Interaction.ReactiveRoundTrace

/-! # The actual unsent interval before the final original callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem original_helper_gap_step (seed : Seeds) (owner : Player)
    (bad : seed.2 owner = false) (remaining : Nat) (execution next : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (lower : 11 + (seed.1.symm owner).val < execution.environmentRecall.length)
    (upper : execution.environmentRecall.length < 18 + (seed.1.symm owner).val)
    (players : Player → app.Policy)
    (reached : next ∈ (app.round (family seed) players execution).support) :
    next.application.SeedRequest owner (originalCoordinate owner) ∧
      next.recall owner = execution.recall owner := by
  classical
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨observed, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have valid := raw_native_valid (family seed) _ raw
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have commandEq : command = originalCommand seed execution.environmentRecall.length
      execution.environmentRecall (execution.observeEnvironment app) := by
    rw [family, choose_original _ _ _ original, PMF.mem_support_pure_iff] at selected
    exact selected
  have readyOwner : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true := by
    apply decide_eq_true
    change PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, bindingEvent owner⟩
    rw [original]
    exact (execution.application.requests_publicView valid owner (originalCoordinate owner)).mpr
      request
  have noOwn : command ≠ .activate owner := by
    intro activated
    have turn := (original_command_activation seed owner execution.environmentRecall.length
      execution.environmentRecall (execution.observeEnvironment app) readyOwner).mp
        (commandEq.symm.trans activated)
    simp only [originalTurns, bad, Bool.false_eq_true, ite_false, List.mem_cons,
      List.not_mem_nil, or_false] at turn
    have bounded := owner.isLt
    omega
  have noExpiry : command ≠ .application (.expire (bindingEvent owner)) := by
    intro expiry
    have position := original_command_expiry seed owner execution.environmentRecall.length
      execution.environmentRecall (execution.observeEnvironment app) (commandEq.symm.trans expiry)
    have rank := (seed.1.symm owner).isLt
    omega
  have observedRequest : observed.application.SeedRequest owner (originalCoordinate owner) := by
    rcases unsent_request_retained_or_expiry seed (remaining + 1) execution observed raw
      (originalCoordinate owner) owner request unsent command moved with retained | expiry
    · exact retained
    · exact (noExpiry expiry).elim
  have observedWord : observed.recall owner = execution.recall owner := by
    rw [app.environmentStep_recall execution observed command moved]
  cases actor : command.actor? app with
  | none =>
      change next ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [actor] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact ⟨observedRequest, observedWord⟩
  | some who =>
      have different : owner ≠ who := by
        intro same
        subst who
        have commandOwn : command = .activate owner := by
          cases command with
          | activate other =>
              exact congrArg (fun who => (.activate who : app.Command)) (Option.some.inj actor)
          | wait => cases actor
          | «include» identifier => cases actor
          | application operation => cases actor
        exact noOwn commandOwn
      change next ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [actor] at resumed
      obtain ⟨action, _chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp resumed
      exact ⟨respond_request runtime leaks observed who action owner (originalCoordinate owner)
        observedRequest, (app.respond_recall_other observed who owner different action).trans
          observedWord⟩

/-- Before the owner's fixed clock-three turn, every actual round preserves
its unsent request and literal old word. Foreign policies remain arbitrary. -/
theorem original_helper_gap_run (seed : Seeds) (owner : Player) (bad : seed.2 owner = false)
    (remaining count : Nat) (execution next : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining + count, none, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (lower : 11 + (seed.1.symm owner).val < execution.environmentRecall.length)
    (upper : execution.environmentRecall.length + count ≤ 18 + (seed.1.symm owner).val)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (reached : next ∈ (app.runRounds (family seed) players count execution).support) :
    next.application.SeedRequest owner (originalCoordinate owner) ∧
      next.recall owner = execution.recall owner ∧
      next.environmentRecall.length = execution.environmentRecall.length + count := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨request, rfl, (Nat.add_zero _).symm⟩
  | succ count ih =>
      obtain ⟨middle, first, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have beforeTrace : (countedMenu.protocol initial horizon (family seed)).Trace
          (some ⟨(remaining + count) + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      obtain ⟨still, sameWord⟩ := original_helper_gap_step seed owner bad (remaining + count)
        execution middle beforeTrace request unsent lower (by omega) players first
      have length := app.runRounds_environmentRecall_length (family seed) players 1 execution
        middle (by simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using first)
      have middleUnsent : ∀ message ∈ app.outputs (middle.recall owner),
          PhaseCount.event? message.payload ≠ some (originalCoordinate owner) := by
        rw [sameWord]
        exact unsent
      obtain ⟨middleTrace⟩ := countedMenu.trace_round initial horizon (family seed) players covered
        (remaining + count) execution middle beforeTrace first
      obtain ⟨afterRequest, afterWord, afterLength⟩ := ih middle middleTrace still middleUnsent
        (by omega) (by omega) later
      exact ⟨afterRequest, afterWord.trans sameWord, by omega⟩

end Vegas.Examples.CommitSeedBroadcast

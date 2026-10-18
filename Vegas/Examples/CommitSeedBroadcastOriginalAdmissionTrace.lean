/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalReceiptProvenance
import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveRoundTrace
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual counted inclusion prefixes of original terminal receipts -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The real original receipt has an actual counted include transition and a
retained counted continuation to the identical complete physical endpoint. -/
theorem original_terminal_receipt_counted_prefix (seeds : Seeds) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨0, none, execution⟩)) (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner execution) :
    ∃ (before after : app.Control)
      (prior : (countedMenu.protocol initial horizon (family seeds)).Trace (some before))
      (message : Message Player (CommitAttemptPacket graph)) (native : PhaseRuntimeState graph),
      before.execution.application.attempt = originalAttempt ∧
      message ∈ execution.network.inputs ∧ message.sender = owner ∧
      message.payload.attempt = originalAttempt ∧
      message.payload.packet.call.event? graph = some (bindingEvent owner) ∧
      before.execution.application.handle runtime message = some native ∧
      after.execution.application = native ∧
      ∃ (joint : Player → Option app.Action)
        (legal : (countedMenu.protocol initial horizon (family seeds)).Legal (some before) joint)
        (moved : some after ∈ (app.transition initial horizon (family seeds)
          (some before) joint).support)
        (finalTrace : (countedMenu.protocol initial horizon (family seeds)).Trace
          (some ⟨0, none, execution⟩)),
        TracePrefix (prior.extend joint legal moved) finalTrace := by
  classical
  obtain ⟨prior, native, used, _rawPrior, position, original, _past, _words, _emissions,
    message, _input, sender, attempt, event, _lookup, handled, selected,
    rest, middle, reachedPrior, moved, middleState, future, length, finalInput⟩ :=
    original_binding_accepted_boundary countedMenu seeds 0 execution trace owner accepted
  have accounted := app.raw_trace_horizon initial horizon (family seeds)
    (countedMenu.toRawTrace initial horizon (family seeds) trace)
  change execution.environmentRecall.length + 0 = horizon at accounted
  have horizonEq : used + 1 + rest = horizon := by omega
  have priorFrom : prior ∈ (app.roundsFrom initial (family seeds)
      countedMenu.uniformResponses used).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialState, by rw [initial]; simp, reachedPrior⟩
  have covered : ∀ who past view action, action ∈
      (countedMenu.uniformResponses who past view).support →
        action ∈ countedMenu.actions who past view := fun who past view action member =>
    (countedMenu.uniformResponses_support who past view action).mp member
  obtain ⟨beforeTrace⟩ := countedMenu.trace_roundsFrom initial horizon (family seeds)
    countedMenu.uniformResponses covered used (by omega) prior priorFrom
  have countEq : horizon - used = rest + 1 := by omega
  rw [countEq] at beforeTrace
  let before : app.Control := ⟨rest + 1, none, prior⟩
  let after : app.Control := ⟨rest, none, middle⟩
  let joint : Player → Option app.Action := fun _ => none
  have legal : (countedMenu.protocol initial horizon (family seeds)).Legal (some before) joint := by
    constructor
    · simp [before, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
    · intro who
      simp [joint, before, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor]
  have chosen : (.include message.id : app.Command) ∈
      (family seeds prior.environmentRecall (prior.observeEnvironment app)).support := by
    change (.include message.id : app.Command) ∈
      (PMF.pure (choose seeds prior.environmentRecall (prior.observeEnvironment app))).support
    rw [choose_original seeds prior.environmentRecall (prior.observeEnvironment app)
      original, position, selected]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have step : some after ∈ (app.transition initial horizon (family seeds) (some before)
      joint).support := by
    change some after ∈ ((family seeds prior.environmentRecall (prior.observeEnvironment app)).bind
      fun command => (prior.environmentStep app command).map fun next =>
        some (⟨rest, command.actor? app, next⟩ : app.Control)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨.include message.id, chosen,
      PMF.mem_support_map_iff _ _ _ |>.mpr ⟨middle, moved, rfl⟩⟩
  let post := beforeTrace.extend joint legal step
  let history : (countedMenu.protocol initial horizon (family seeds)).History := ⟨some after, post⟩
  let profile := fun who => countedMenu.restrictPolicy initial horizon (family seeds) who
    (countedMenu.uniformResponses who)
  have decoded : countedMenu.decodeProfile initial horizon (family seeds) profile =
      countedMenu.uniformResponses := by
    funext who
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon (family seeds) who
      (countedMenu.uniformResponses who) (covered who)
  have law := countedMenu.run_eq_finish initial horizon (family seeds) profile (2 * horizon + 1)
    history (by change 2 * rest + 0 ≤ 2 * horizon + 1; omega)
  rw [decoded] at law
  have finish : some (⟨0, none, execution⟩ : app.Control) ∈
      (app.finish initial horizon (family seeds) countedMenu.uniformResponses
        (some after)).support := by
    simp only [ReactiveApplication.finish, after, ReactiveApplication.resume, PMF.pure_bind]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨execution, future, rfl⟩
  rw [← law, PMF.support_map] at finish
  obtain ⟨ending, supported, state⟩ := finish
  have kept :=
    ((countedMenu.information initial horizon (family seeds)).runBehavioralFrom_reachesWithin
      profile (2 * horizon + 1) history ending supported).tracePrefix
  rcases ending with ⟨endingState, endingTrace⟩
  change endingState = some (⟨0, none, execution⟩ : app.Control) at state
  subst endingState
  exact ⟨before, after, beforeTrace, message, native, original, finalInput, sender, attempt, event,
    handled, middleState, joint, legal, step, endingTrace, kept⟩

end Vegas.Examples.CommitSeedBroadcast

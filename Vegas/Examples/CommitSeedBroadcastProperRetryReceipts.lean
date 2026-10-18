/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRememberedRequest
import Vegas.Examples.CommitSeedBroadcastTailSuccess
import Vegas.Examples.CommitSeedBroadcastProperResponse
import Vegas.Examples.CommitSeedBroadcastTailDecision
import Vegas.Examples.CommitSeedBroadcastCalendarClocks
import Interaction.ReactiveRecovery

/-! # Original proper-policy records rule out unserved retry expiry -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

variable (clock : Nat)

theorem scheduled_proper_recorded_tail_binding_accepted
    (seed : Seeds) (beforeRemaining : Nat) (before : app.Execution)
    (beforeTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨beforeRemaining, none, before⟩))
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (kept : TracePrefix beforeTrace trace)
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (binding : graph.outputLayout coordinate.event = .binding owner .bool)
    (request : before.application.SeedRequest owner coordinate)
    (positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (before.observeEnvironment app))
    (consistent : (scheduledProperPolicy clock owner).Consistent (final.execution.recall owner))
    (resolved : coordinate.Resolved final.execution.application) :
    PhaseService.BindingAccepted runtime leaks coordinate owner final.execution := by
  classical
  obtain ⟨entry, member, requested⟩ := positive_age_own_request seed beforeRemaining before
    beforeTrace coordinate owner request positive
  have retained := app.reaches_recall_prefix initial horizon (family seed)
    (countedMenu.reaches_raw initial horizon (family seed) kept.reachesWithin)
      ⟨beforeRemaining, none, before⟩ final rfl rfl owner
  have recorded : entry ∈ final.execution.recall owner := retained.subset member
  obtain ⟨callback, prior, _prefix, acting, viewed, chosen, _later⟩ :=
    countedMenu.recorded_response_supported initial horizon (family seed) final trace owner
      (scheduledProperPolicy clock owner) consistent entry recorded
  have valid := raw_native_valid (family seed) callback
    (countedMenu.toRawTrace initial horizon (family seed) prior)
  have currentPublic := requested
  rw [viewed] at currentPublic
  have sourceRequest :=
    (callback.execution.application.requests_publicView valid owner coordinate).mp currentPublic
  rcases callback with ⟨remaining, actor, execution⟩
  cases acting
  have sourceRetired : execution.application.attempt ≠ originalAttempt := by
    rwa [← sourceRequest.1]
  have coordinateEq : coordinate = ⟨execution.application.attempt, coordinate.event⟩ := by
    cases coordinate with
    | mk attempt event =>
        exact congrArg (fun value => (⟨value, event⟩ : CommitAttemptEvent graph)) sourceRequest.1
  have sourceRequested : execution.application.SeedRequest owner
      ⟨execution.application.attempt, coordinate.event⟩ := coordinateEq ▸ sourceRequest
  have unsubmitted := fixed_tail_callback_unsubmitted seed remaining execution owner prior
    coordinate retired sourceRequest
  have recalled := PhaseCount.countRecall_history runtime leaks
    (countedMenu.toRawTrace initial horizon (family seed) prior)
  have unsent (message : Message Player (CommitAttemptPacket graph))
      (present : message ∈ app.outputs (execution.recall owner)) :
      PhaseCount.event? message.payload ≠
        some ⟨execution.application.attempt, coordinate.event⟩ := by
    rw [← recalled.1 owner] at present
    have old := unsubmitted message (List.mem_filter.mp present).1
      (of_decide_eq_true (List.mem_filter.mp present).2)
    intro same
    exact old (same.trans (congrArg some coordinateEq.symm))
  have clocks := tail_service_clocks countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seed
      ⟨remaining, some owner, execution⟩ prior owner rfl
        ⟨execution.application.attempt, coordinate.event⟩ sourceRetired sourceRequested
  obtain ⟨serial, _bounded, literal, _freshSlot, _fresh, _result⟩ :=
    properPolicy_binding_response (lateAtRule clock) (family seed)
      ⟨remaining, some owner, execution⟩ (countedInRaw.trace initial horizon (family seed) prior)
        owner rfl coordinate.event binding sourceRequested unsent
          (Or.inl (by rw [clocks]; rfl))
  have proper : scheduledProperPolicy clock owner (execution.recall owner) (execution.observe
    app owner) =
      properPolicy (lateAtRule clock) owner (execution.recall owner) (execution.observe app
        owner) := by
    unfold scheduledProperPolicy
    exact ite_eq_right (fun both => sourceRetired both.1)
  rw [proper, literal, PMF.mem_support_pure_iff] at chosen
  let material : app.Submission :=
    ⟨⟨.commitment coordinate.event (owner, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩
  have transmitted : entry.action.transmission = some material := by rw [chosen]; rfl
  exact tail_recorded_binding_resolved_accepted seed final trace coordinate owner retired binding
    entry recorded requested material transmitted resolved

/-- At a resolved endpoint of an original initialized experiment, a retry
that reached positive age has a true receipt under the literal fixed-late
deviation. Original policy consistency is derived from the complete run. -/
theorem initialized_scheduled_proper_positive_retry_accepted
    (players : Player → app.Policy) (seed : Seeds) (count : Nat) (final : app.Control)
    (reached : final.execution ∈
      (app.runRounds (family seed) players count initialExecution).support)
    (owner : Player) (policy : players owner = scheduledProperPolicy clock owner)
    (beforeRemaining : Nat) (before : app.Execution)
    (beforeTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨beforeRemaining, none, before⟩))
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (kept : TracePrefix beforeTrace trace)
    (coordinate : CommitAttemptEvent graph)
    (retired : coordinate.attempt ≠ originalAttempt)
    (binding : graph.outputLayout coordinate.event = .binding owner .bool)
    (request : before.application.SeedRequest owner coordinate)
    (positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (before.observeEnvironment app))
    (resolved : coordinate.Resolved final.execution.application) :
    PhaseService.BindingAccepted runtime leaks coordinate owner final.execution := by
  have consistent := (app.consistentRecall_policyInvariant players).runRounds
    (family seed) count initialExecution final.execution (fun _ => .nil) reached
  have focal := consistent owner
  rw [policy] at focal
  exact scheduled_proper_recorded_tail_binding_accepted clock seed beforeRemaining before
    beforeTrace final
    trace kept coordinate owner retired binding request positive focal resolved

end Vegas.Examples.CommitSeedBroadcast

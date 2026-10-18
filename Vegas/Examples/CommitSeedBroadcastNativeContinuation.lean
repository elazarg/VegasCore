/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperSurvival
import Vegas.Examples.CommitSeedBroadcastCountedContinuation
import Vegas.Examples.CommitSeedBroadcastPublicationReceipts
import Vegas.Examples.CommitSeedBroadcastPayoffs
import Vegas.Examples.CommitSeedBroadcastPosteriorTrace

/-! # Proper continuation survival and payoff at arbitrary genuine native inputs -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable (clock : Nat)

/-- Literal own-policy consistency propagates from a subgame root; opponents'
recorded past actions are unrestricted. -/
theorem finish_own_policy_consistent (players : Player → app.Policy) (owner : Player)
    (current : app.Control) (past : (players owner).Consistent (current.execution.recall owner))
    (after : app.Execution)
    (reached : some (⟨0, none, after⟩ : app.Control) ∈
      (app.finish initial horizon scheduler players (some current)).support) :
    (players owner).Consistent (after.recall owner) := by
  have recovered : players owner = (players owner).recover (players owner) := by
    funext earlier view
    simp only [ReactiveApplication.Policy.recover, ite_self]
  have invariant := (players owner).recover_invariant (players owner) owner players recovered
  obtain ⟨final, supported, equal⟩ := PMF.support_map .. ▸ reached
  have same : final = after := congrArg (fun control : app.Control => control.execution)
    (Option.some.inj equal)
  subst final
  obtain ⟨resumed, response, continued⟩ := Set.mem_iUnion₂.mp
    (PMF.support_bind .. ▸ supported)
  exact invariant.runRounds scheduler current.remaining resumed after
    (invariant.resume current.actor current.execution resumed past response) continued

/-- Native finish support has an actual counted trace at the identical control. -/
theorem counted_finish_trace
    (profile : ∀ who, countedModel.BehavioralPolicy who) (history : countedProtocol.History)
    (current : app.Control) (state : history.state = some current) (after : app.Execution)
    (reached : some (⟨0, none, after⟩ : app.Control) ∈
      (app.finish initial horizon scheduler
        (countedMenu.decodeProfile initial horizon scheduler profile) (some current)).support) :
    Nonempty (countedProtocol.Trace (some ⟨0, none, after⟩)) := by
  have finish := countedMenu.run_eq_finish initial horizon scheduler profile
    (app.rank horizon history.state) history le_rfl
  rw [state] at finish
  rw [← finish, PMF.support_map] at reached
  obtain ⟨final, _supported, equal⟩ := reached
  exact ⟨equal ▸ final.trace⟩

/-- An admitted original binding protects a proper continuation even when the
subgame root is off path under the original assessed profile. -/
theorem counted_scheduled_proper_finish_survives
    (profile : ∀ who, countedModel.BehavioralPolicy who) (history : countedProtocol.History)
    (current : app.Control) (state : history.state = some current) (owner : Player)
    (selected : countedMenu.decodeProfile initial horizon scheduler profile owner =
      scheduledProperPolicy clock owner)
    (past : (scheduledProperPolicy clock owner).Consistent (current.execution.recall owner))
    (after : app.Execution)
    (reached : some (⟨0, none, after⟩ : app.Control) ∈
      (app.finish initial horizon scheduler
        (countedMenu.decodeProfile initial horizon scheduler profile) (some current)).support)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after) :
    owner ∉ after.application.current.excluded := by
  obtain ⟨trace⟩ := counted_finish_trace profile history current state after reached
  obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) ⟨0, none, after⟩ trace
  have before : (countedMenu.decodeProfile initial horizon scheduler profile owner).Consistent
      (current.execution.recall owner) := selected.symm ▸ past
  have consistent := finish_own_policy_consistent
    (countedMenu.decodeProfile initial horizon scheduler profile) owner current before after reached
  rw [selected] at consistent
  exact scheduled_proper_original_binding_survives clock seed ⟨0, none, after⟩ fixed owner
    consistent accepted

/-- Every genuine completed counted endpoint has the literal fixed-loss payoff
and zero count charge, independently of how its prefix was reached. -/
theorem counted_endpoint_payoff (after : app.Execution)
    (trace : countedProtocol.Trace (some ⟨0, none, after⟩)) (owner : Player) :
    netPayoff (app.finished after) owner =
      if owner ∈ after.application.current.excluded then -(3 / 2) else
        if ∃ other : Player, other ≠ owner ∧
          RecoveryState.publicationFailed after.application.current.native
            (revealEvent other) = true then 1 else 0 := by
  have complete := scheduler_completesPlay ⟨0, none, after⟩
    (countedMenu.toRawTrace initial horizon scheduler trace) ⟨rfl, rfl⟩
  have zero := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    scheduler evidenceService ⟨some ⟨0, none, after⟩, trace⟩ owner
  change TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, after⟩) owner = 0 at zero
  change basePayoff (some ⟨0, none, after⟩) owner -
    TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, after⟩) owner * deposit owner = _
  rw [zero, zero_mul, sub_zero]
  exact basePayoff_terminal_formula ⟨0, none, after⟩ complete owner

/-- An arbitrary genuine counted terminal trace has an initialized raw
realization under uniform recorded responses; no equilibrium reach is required. -/
theorem counted_endpoint_missing_original_publication_failed
    (after : app.Execution) (trace : countedProtocol.Trace (some ⟨0, none, after⟩))
    (owner : Player)
    (missing : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      after) :
    RecoveryState.publicationFailed after.application.current.native
      (revealEvent owner) = true := by
  have complete := scheduler_completesPlay ⟨0, none, after⟩
    (countedMenu.toRawTrace initial horizon scheduler trace) ⟨rfl, rfl⟩
  obtain ⟨accounted, actual⟩ := countedMenu.roundSupported_uniform initial horizon scheduler trace
  have reached : after ∈ (app.runRounds scheduler countedMenu.uniformResponses horizon
      initialExecution).support := by
    change after ∈ (app.roundsFrom initial scheduler countedMenu.uniformResponses
      after.environmentRecall.length).support at actual
    have length : after.environmentRecall.length = horizon := by
      change after.environmentRecall.length + 0 = horizon at accounted
      omega
    rw [length] at actual
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using actual
  exact initialized_missing_original_binding_publication_failed countedMenu.uniformResponses
    after reached complete owner missing

/-- The proper continuation attains the reward ceiling on a foreign original
miss, even from an initially off-path counted subgame root. -/
theorem counted_scheduled_proper_finish_foreign_miss
    (profile : ∀ who, countedModel.BehavioralPolicy who) (history : countedProtocol.History)
    (current : app.Control) (state : history.state = some current) (owner : Player)
    (selected : countedMenu.decodeProfile initial horizon scheduler profile owner =
      scheduledProperPolicy clock owner)
    (past : (scheduledProperPolicy clock owner).Consistent (current.execution.recall owner))
    (after : app.Execution)
    (reached : some (⟨0, none, after⟩ : app.Control) ∈
      (app.finish initial horizon scheduler
        (countedMenu.decodeProfile initial horizon scheduler profile) (some current)).support)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after)
    (foreign : ∃ other : Player, other ≠ owner ∧
      ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate other) other after) :
    netPayoff (app.finished after) owner = 1 := by
  classical
  obtain ⟨trace⟩ := counted_finish_trace profile history current state after reached
  have active := counted_scheduled_proper_finish_survives clock profile history current state owner
    selected past after reached accepted
  obtain ⟨other, different, missing⟩ := foreign
  have failed := counted_endpoint_missing_original_publication_failed after trace other missing
  rw [counted_endpoint_payoff after trace owner, ite_eq_right active,
    ite_eq_left ⟨other, different, failed⟩]

/-- Proper continuation has nonnegative payoff on every admitted-original
branch, without imposing proper hidden preparations on any opponent. -/
theorem counted_scheduled_proper_finish_nonnegative
    (profile : ∀ who, countedModel.BehavioralPolicy who) (history : countedProtocol.History)
    (current : app.Control) (state : history.state = some current) (owner : Player)
    (selected : countedMenu.decodeProfile initial horizon scheduler profile owner =
      scheduledProperPolicy clock owner)
    (past : (scheduledProperPolicy clock owner).Consistent (current.execution.recall owner))
    (after : app.Execution)
    (reached : some (⟨0, none, after⟩ : app.Control) ∈
      (app.finish initial horizon scheduler
        (countedMenu.decodeProfile initial horizon scheduler profile) (some current)).support)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after) :
    0 ≤ netPayoff (app.finished after) owner := by
  classical
  obtain ⟨trace⟩ := counted_finish_trace profile history current state after reached
  have active := counted_scheduled_proper_finish_survives clock profile history current state owner
    selected past after reached accepted
  rw [counted_endpoint_payoff after trace owner, ite_eq_right active]
  split <;> norm_num

end Vegas.Examples.CommitSeedBroadcast

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostHandle
import Vegas.Pending.PhaseSignedBindings
import Vegas.Pending.PhaseValueSwap
import Vegas.Pending.ReactiveEventStability

/-! # An unassociated preparation through actual phase restoration

Both physical accepted tables are retained. Automatic completion keeps each
table, while restore selects the saved table; no live namespace restriction
or assumption about a normalized target is needed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- A binding accepted with a handle owned by an excluded player would have
that same player as its graph actor, contradicting the actual phase gate. -/
theorem handle_commitment_none_of_handle_owner_excluded
    (runtime : EventGraphRuntime graph) (state : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph)) (event : graph.EventId)
    (candidate : Handle graph) (call : message.payload.packet.call = .commitment event candidate)
    (excluded : candidate.1 ∈ state.current.excluded) : state.handle runtime message = none := by
  cases actual : state.handle runtime message with
  | none => rfl
  | some next =>
      unfold handle at actual
      split at actual
      · rename_i allowed
        obtain ⟨native, accepted, _same⟩ := Option.map_eq_some_iff.mp actual
        obtain ⟨_ready, _timely, owner, payload, binding, _code, _node, _sender,
            owned, _vacant, _unused⟩ := handle_commitment_conditions runtime state.current.native
              native message.id event candidate (by simpa only [call] using accepted)
        have actor := actor?_of_outputLayout_binding graph binding
        have blocked : state.current.excludedCall message.payload.packet.call = true := by
          simp only [RecoveryState.excludedCall, call, Payload.event?, RecoveryState.excludedEvent,
            actor, Option.any_some, decide_eq_true_eq]
          exact owned ▸ excluded
        simp only [blocked, Bool.not_true, Bool.and_false, Bool.false_eq_true] at allowed
      · cases actual

/-- The structural accepted-table projection of the existing normalizer. -/
theorem settle_unused_preparation
    (candidate : Handle graph) (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (saved : entry.native.HandleUnused candidate) (active : current.native.HandleUnused candidate) :
    (settle phases generation entry current retired).entry.native.HandleUnused candidate ∧
      (settle phases generation entry current retired).current.native.HandleUnused candidate := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨saved, active⟩
  | cons phase rest ih =>
      have drained : (phase.drain current).native.HandleUnused candidate := by
        simpa only [State.HandleUnused, (phase.drain_tables current).1] using active
      have rebuilt : (phase.drain (restore entry (phase.drain current))).native.HandleUnused
          candidate := by
        simpa only [State.HandleUnused, (phase.drain_tables _).1, restore] using saved
      simp only [settle]
      split
      · split
        · split
          · exact ⟨saved, rebuilt⟩
          · exact ih _ _ _ _ rebuilt rebuilt
        · exact ih _ _ _ _ drained drained
      · exact ⟨saved, drained⟩

/-- A real phase handler cannot associate the selected lost handle when its
actual packet rejects; all other accepted associations and restoration are
handled by the owning table formulas. -/
theorem handle_unused_preparation
    (runtime : EventGraphRuntime graph) (state next : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
    (saved : state.entry.native.HandleUnused candidate)
    (active : state.current.native.HandleUnused candidate)
    (rejected : ∀ event, message.payload.packet.call = .commitment event candidate →
      state.handle runtime message = none)
    (handled : state.handle runtime message = some next) :
    next.entry.native.HandleUnused candidate ∧ next.current.native.HandleUnused candidate := by
  have original := handled
  unfold handle at handled
  split at handled
  · obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
    have fresh : native.HandleUnused candidate := by
      rcases handle_tables_cases runtime state.current.native native
          ⟨message.id, message.payload.packet.call⟩ accepted with
        ⟨event, selected, call, _catalogue, table, _owner⟩ | ⟨table, _catalogue⟩
      · have different : selected ≠ candidate := by
          intro same
          subst selected
          have absent := rejected event call
          rw [absent] at original
          cases original
        intro field installed
        rw [table] at installed
        by_cases same : field = .inr event
        · subst field
          rw [Function.update_self] at installed
          exact different (Option.some.inj installed)
        · rw [Function.update_of_ne same] at installed
          exact active field installed
      · simpa only [State.HandleUnused, table] using active
    exact settle_unused_preparation candidate state.phases state.generation state.entry
      (state.current.inclusionResult message.payload.packet.call native) state.retired saved fresh
  · cases handled

/-- Every original environment atom keeps the selected nonassociation,
including automatic exclusion drain and rollback. -/
theorem environment_unused_preparation
    (runtime : EventGraphRuntime graph) (state next : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph) (candidate : Handle graph)
    (saved : state.entry.native.HandleUnused candidate)
    (active : state.current.native.HandleUnused candidate)
    (moved : next ∈ (state.environment runtime command).support) :
    next.entry.native.HandleUnused candidate ∧ next.current.native.HandleUnused candidate := by
  unfold environment at moved
  split at moved
  · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ moved
    have fresh : native.HandleUnused candidate := by
      simpa only [State.HandleUnused,
        (environmentStep_tables runtime state.current.native native command supported).1]
        using active
    exact settle_unused_preparation candidate state.phases state.generation state.entry
      (state.current.environmentResult command native) state.retired saved fresh
  · cases (PMF.mem_support_pure_iff _ _).mp moved
    exact ⟨saved, active⟩

end PhaseRuntimeState

/-- One actual command preserves both nonassociations. Rejection is needed
only for the command actually selected, and only when it names this handle. -/
theorem phase_environment_unused_preparation
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (before after : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command) (candidate : Handle graph)
    (saved : before.application.entry.native.HandleUnused candidate)
    (active : before.application.current.native.HandleUnused candidate)
    (rejected : ∀ id message event, command = .include id →
      before.network.lookup id = some message →
      message.payload.packet.call = .commitment event candidate →
        before.application.handle runtime message = none)
    (moved : after ∈ (before.environmentStep (phaseApplication runtime leaks) command).support) :
    after.application.entry.native.HandleUnused candidate ∧
      after.application.current.native.HandleUnused candidate := by
  let app := phaseApplication runtime leaks
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact ⟨saved, active⟩
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _selected, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨saved, active⟩
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨next, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.environment_unused_preparation runtime before.application next
        command candidate saved active changed
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      change (before.includePending app id).application.entry.native.HandleUnused candidate ∧
        (before.includePending app id).application.current.native.HandleUnused candidate
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : before.network.lookup id with
      | none => exact ⟨saved, active⟩
      | some message =>
          change State.HandleUnused
              ((before.application.handle runtime message).getD before.application).entry.native
              candidate ∧ State.HandleUnused
                ((before.application.handle runtime message).getD before.application).current.native
                candidate
          cases handled : before.application.handle runtime message with
          | none => exact ⟨saved, active⟩
          | some next =>
              exact PhaseRuntimeState.handle_unused_preparation runtime before.application next
                message candidate saved active (fun event named =>
                  rejected id message event rfl found named) handled

/-- After the genuine omission excludes the sender, the existing application
invariant engine keeps both accepted tables free of this particular handle.
No rank-limited stamp or clear-attempt reduction is used. -/
theorem phaseApplication_excluded_unused_preparation
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (candidate : Handle graph) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      candidate.1 ∈ state.current.excluded ∧ state.entry.native.HandleUnused candidate ∧
        state.current.native.HandleUnused candidate) where
  submit state who material valid := by
    refine ⟨valid.1, valid.2.1, ?_⟩
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).HandleUnused candidate
    simpa only [State.HandleUnused, submitStep_accepted, Submission.register_accepted]
      using valid.2.2
  handle state message next valid accepted := by
    obtain ⟨saved, active⟩ := PhaseRuntimeState.handle_unused_preparation runtime state next
      message candidate valid.2.1 valid.2.2
        (fun event call => PhaseRuntimeState.handle_commitment_none_of_handle_owner_excluded
          runtime state message event candidate call valid.1) accepted
    exact ⟨(phaseApplication_exclusion_monotone runtime leaks).handle state message next accepted
      valid.1, saved, active⟩
  environment state command next valid moved := by
    obtain ⟨saved, active⟩ := PhaseRuntimeState.environment_unused_preparation runtime state next
      command candidate valid.2.1 valid.2.2 moved
    exact ⟨(phaseApplication_exclusion_monotone runtime leaks).environment state command next moved
      valid.1, saved, active⟩

end Vegas.EventGraphRuntime

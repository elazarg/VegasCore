/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ReactiveSignedCommitments

/-! # Signed binding origins survive physical phase rollback

Both the saved checkpoint and live accepted table retain actual authored
commitments. Retirement preserves the complete author recall, while restore
selects the saved semantic associations without fabricating signed inputs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every accepted event handle has a concrete signed owner output; input
handles retain their distinguished initial identity. -/
def SignedBindingTable (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (state : State graph) : Prop :=
  (∀ input candidate, state.accepted (.inl input) = some candidate →
    candidate.2 = .initial input) ∧
  ∀ event candidate, state.accepted (.inr event) = some candidate →
    ∃ message ∈ outputs candidate.1, message.sender = candidate.1 ∧
      message.payload.packet.call = .commitment event candidate

namespace SignedBindingTable

variable {outputs : Player → List (Message Player (CommitAttemptPacket graph))}

omit [DecidableEq Player] in
theorem copy {before after : State graph} (valid : SignedBindingTable outputs before)
    (accepted : after.accepted = before.accepted) : SignedBindingTable outputs after := by
  simpa only [SignedBindingTable, accepted] using valid

omit [DecidableEq Player] in
theorem mono {more : Player → List (Message Player (CommitAttemptPacket graph))}
    {state : State graph} (valid : SignedBindingTable outputs state)
    (contains : ∀ who, outputs who ⊆ more who) : SignedBindingTable more state := by
  refine ⟨valid.1, ?_⟩
  intro event candidate installed
  obtain ⟨message, present, sender, sent⟩ := valid.2 event candidate installed
  exact ⟨message, contains candidate.1 present, sender, sent⟩

theorem initial (inputs : graph.Inputs) : SignedBindingTable outputs (State.initial inputs) := by
  refine ⟨?_, ?_⟩
  · intro input candidate installed
    obtain ⟨original, owner, payload, field, layout, same⟩ :=
      State.initial_accepted_eq_some inputs (.inl input) candidate installed
    cases Sum.inl.inj field
    exact congrArg Prod.snd same
  · intro event candidate installed
    obtain ⟨input, owner, payload, impossible, rest⟩ :=
      State.initial_accepted_eq_some inputs (.inr event) candidate installed
    cases impossible

end SignedBindingTable

namespace PhaseRuntimeState

/-- Saved, live and retired accepted tables refer only to actual author recall. -/
def SignedBindings (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) : Prop :=
  SignedBindingTable (fun who => (phaseApplication runtime leaks).outputs (execution.recall who))
      execution.application.entry.native ∧
    SignedBindingTable (fun who => (phaseApplication runtime leaks).outputs (execution.recall who))
      execution.application.current.native ∧
    ∀ record ∈ execution.application.retired,
      SignedBindingTable (fun who => (phaseApplication runtime leaks).outputs
        (execution.recall who)) record.state

theorem settle_signedBindings
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (saved : SignedBindingTable outputs entry.native)
    (active : SignedBindingTable outputs current.native)
    (archives : ∀ record ∈ retired, SignedBindingTable outputs record.state) :
    SignedBindingTable outputs (settle phases generation entry current retired).entry.native ∧
      SignedBindingTable outputs
        (settle phases generation entry current retired).current.native ∧
      ∀ record ∈ (settle phases generation entry current retired).retired,
        SignedBindingTable outputs record.state := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨saved, active, archives⟩
  | cons phase rest ih =>
      have drained := active.copy (phase.drain_tables current).1
      have rebuilt := saved.copy (phase.drain_tables (restore entry (phase.drain current))).1
      have appended : ∀ record ∈ retired ++
          [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩],
          SignedBindingTable outputs record.state := by
        intro record member
        rcases List.mem_append.mp member with previous | newest
        · exact archives record previous
        · cases List.mem_singleton.mp newest
          exact drained
      simp only [settle]
      split
      · split
        · split
          · exact ⟨saved, rebuilt, appended⟩
          · exact ih _ _ _ _ rebuilt rebuilt appended
        · exact ih _ _ _ _ drained drained archives
      · exact ⟨saved, drained, archives⟩

end PhaseRuntimeState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem signedBindings_respond (execution : (app).Execution)
    (who : Player) (response : (app).Action)
    (valid : PhaseRuntimeState.SignedBindings runtime leaks execution) :
    PhaseRuntimeState.SignedBindings runtime leaks (execution.respond (app) who response) := by
  have contains : ∀ observer, (app).outputs (execution.recall observer) ⊆
      (app).outputs ((execution.respond (app) who response).recall observer) := by
    intro observer message member
    obtain ⟨entry, present, emitted⟩ := List.mem_filterMap.mp member
    exact List.mem_filterMap.mpr ⟨entry,
      (app).respond_recall_mono execution who observer response present, emitted⟩
  cases response with
  | mk transmission =>
      cases transmission with
      | none =>
          exact ⟨valid.1.mono contains, valid.2.1.mono contains,
            fun record member => (valid.2.2 record member).mono contains⟩
      | some material =>
          refine ⟨valid.1.mono contains, ?_,
            fun record member => (valid.2.2 record member).mono contains⟩
          apply (valid.2.1.mono contains).copy
          change (submitStep (material.call.register execution.application.current.native who)
            who material.call.packet).accepted = _
          rw [submitStep_accepted, Submission.register_accepted]

private theorem signedBindings_handle (execution : (app).Execution)
    (next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (valid : PhaseRuntimeState.SignedBindings runtime leaks execution)
    (issued : execution.Issued (app) message)
    (handled : execution.application.handle runtime message = some next) :
    PhaseRuntimeState.SignedBindings runtime leaks {execution with application := next} := by
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
    apply PhaseRuntimeState.settle_signedBindings
    · exact valid.1
    · rcases handle_tables_cases runtime execution.application.current.native native _ accepted with
        ⟨event, candidate, call, _, table, owner⟩ | ⟨table, _⟩
      · refine ⟨?_, ?_⟩
        · intro input handle installed
          change native.accepted (.inl input) = some handle at installed
          rw [table, Function.update_of_ne (by simp)] at installed
          exact valid.2.1.1 input handle installed
        · intro field handle installed
          change native.accepted (.inr field) = some handle at installed
          rw [table] at installed
          by_cases same : field = event
          · subst field
            rw [Function.update_self] at installed
            cases Option.some.inj installed
            obtain ⟨entry, present, material, transmission, emitted, packet⟩ := issued
            exact ⟨message, List.mem_filterMap.mpr ⟨entry,
              by simpa only [Message.sender, owner] using present, emitted⟩, owner.symm, call⟩
          · rw [Function.update_of_ne (by simpa using same)] at installed
            exact valid.2.1.2 field handle installed
      · exact valid.2.1.copy table
    · exact valid.2.2
  · cases handled

private theorem signedBindings_environment (execution next : (app).Execution)
    (command : (app).Command) (valid : PhaseRuntimeState.SignedBindings runtime leaks execution)
    (origins : execution.Provenance (app))
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    PhaseRuntimeState.SignedBindings runtime leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid
      | some message =>
          change PhaseRuntimeState.SignedBindings runtime leaks {execution with
            application := ((app).handle execution.application message).getD execution.application}
          cases accepted : (app).handle execution.application message with
          | none => exact valid
          | some state =>
              exact signedBindings_handle runtime leaks execution state message valid
                (origins.lookup id message found) accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (execution.application.environment runtime command).support at changed
      unfold PhaseRuntimeState.environment at changed
      split at changed
      · rw [PMF.support_map] at changed
        obtain ⟨native, nativeMoved, rfl⟩ := changed
        exact PhaseRuntimeState.settle_signedBindings _ _ _ _ _ _ valid.1
          (valid.2.1.copy (environmentStep_tables runtime _ _ command nativeMoved).1) valid.2.2
      · rw [PMF.mem_support_pure_iff] at changed
        subst state
        exact valid

/-- Arbitrary initialized physical histories retain concrete signed binding
origins at the saved checkpoint, current frontier and every retired snapshot. -/
theorem phaseSignedBindings_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) : PhaseRuntimeState.SignedBindings runtime leaks control.execution := by
  have invariant : (app).ServiceInvariant scheduler (fun execution =>
      PhaseRuntimeState.SignedBindings runtime leaks execution ∧ execution.Provenance (app)) := {
    respond := fun execution who action valid =>
      ⟨signedBindings_respond runtime leaks execution who action valid.1,
        (app).respond_provenance execution who action valid.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨signedBindings_environment runtime leaks execution next command valid.1 valid.2 reached,
        (app).environment_provenance execution next command valid.2 reached⟩ }
  exact (invariant.history _ horizon (by
    intro state supported
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact ⟨PhaseRuntimeState.settle_signedBindings _ _ _ _ _ _
      (SignedBindingTable.initial draw) (SignedBindingTable.initial draw)
      (fun _ impossible => (List.not_mem_nil impossible).elim),
      MessageNetwork.Satisfies.empty⟩) trace).1

end Vegas.EventGraphRuntime

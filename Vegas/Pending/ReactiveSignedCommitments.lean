/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveProvenance

/-! # Own signed data behind commitments and accepted handles

Every operation of the reactive runtime keeps a fixed candidate fixed
(`Vegas.EventGraphRuntime.fixesCandidates_step`) and keeps the accepted handle
of every initial binding input (`Vegas.EventGraphRuntime.keepsInputHandles_step`).

Along every history, under arbitrary responses and scheduler choices, the
following hold together (`Vegas.EventGraphRuntime.SignedCommitments`):

* every envelope a player recalls emitting is signed by it and carries the
  packet of the submission it recalls making;
* every commitment a player emitted for a handle of its own has fixed that
  handle's candidate, so a fresh own slot was never named by an own commitment;
* every handle accepted for a binding event was named, for that event, by a
  commitment its owner emitted; and every handle accepted for an initial binding
  input is that input's fixed handle.

The last two are what the count verdict reads of a sender's earlier packets:
a fresh commitment handle, and the signed binding behind an opened handle.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Registering opening data leaves every fixed candidate as it was. -/
theorem Submission.register_lookup_of_not_fresh (submission : Submission graph)
    (state : State graph) (who : Player) (handle : Handle graph)
    (fixed : state.candidates.lookup handle ≠ .fresh) :
    (submission.register state who).candidates.lookup handle =
      state.candidates.lookup handle := by
  unfold Submission.register
  split
  · split
    · exact state.candidates.lookup_prepare_eq_of_not_fresh handle _ _ _ fixed
    · rfl
  · rfl

/-- Registering opening data changes no accepted handle. -/
theorem Submission.register_accepted (submission : Submission graph) (state : State graph)
    (who : Player) : (submission.register state who).accepted = state.accepted := by
  unfold Submission.register
  split
  · split <;> rfl
  · rfl

/-- `after` keeps every candidate that is fixed at `before` fixed. -/
def FixesCandidates (before after : State graph) : Prop :=
  ∀ handle, before.candidates.lookup handle ≠ .fresh → after.candidates.lookup handle ≠ .fresh

/-- `after` has the accepted handle of every initial input of `before`. -/
def KeepsInputHandles (before after : State graph) : Prop :=
  ∀ input, after.accepted (.inl input) = before.accepted (.inl input)

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- An accepted call either is a commitment, freezing its handle and installing
it at its event for its sender, or changes neither table. -/
theorem handle_tables_cases (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    (∃ event candidate, message.payload = .commitment event candidate ∧
      next.candidates = state.candidates.freeze candidate ∧
      next.accepted = Function.update state.accepted (.inr event) (some candidate) ∧
      candidate.1 = message.id.1) ∨
    (next.accepted = state.accepted ∧ next.candidates = state.candidates) := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | commitment event candidate =>
      exact Or.inl ⟨event, candidate, rfl,
        handle_commitment_tables runtime state next id event candidate accepted⟩
  | opening event candidate raw =>
      exact Or.inr (handle_resolution_tables runtime state next _
        (fun _ _ same => by cases same) accepted)
  | malformed raw =>
      exact Or.inr (handle_resolution_tables runtime state next _
        (fun _ _ same => by cases same) accepted)

/-- **Fixed candidates stay fixed** under every runtime operation. -/
theorem fixesCandidates_step :
    (runtime.reactiveApplication leaks).StepRelation FixesCandidates where
  refl _ _ fixed := fixed
  submit state who material handle fixed := by
    change (submitStep (material.call.register state who) who
      material.call.packet).candidates.lookup handle ≠ .fresh
    have registered := material.call.register_lookup_of_not_fresh state who handle fixed
    rw [submitStep_lookup_of_not_fresh _ _ _ _ (registered ▸ fixed), registered]
    exact fixed
  handle state message next accepted handle fixed := by
    rcases handle_tables_cases runtime state next _ (reactiveHandle_call accepted) with
      ⟨_, candidate, _, candidates, _⟩ | ⟨_, candidates⟩
    · rw [candidates, state.candidates.lookup_freeze_eq_of_not_fresh handle candidate fixed]
      exact fixed
    · rw [candidates]
      exact fixed
  environment state command next reached handle fixed := by
    rw [(environmentStep_tables runtime state next command reached).2]
    exact fixed

/-- **Initial input handles stay accepted** under every runtime operation. -/
theorem keepsInputHandles_step :
    (runtime.reactiveApplication leaks).StepRelation KeepsInputHandles where
  refl _ _ := rfl
  submit state who material input := by
    change (submitStep (material.call.register state who) who
      material.call.packet).accepted (.inl input) = _
    rw [submitStep_accepted, Submission.register_accepted]
  handle state message next accepted input := by
    rcases handle_tables_cases runtime state next _ (reactiveHandle_call accepted) with
      ⟨event, _, _, _, acceptedEq, _⟩ | ⟨acceptedEq, _⟩
    · rw [acceptedEq, Function.update_of_ne (by simp)]
    · rw [acceptedEq]
  environment state command next reached input := by
    rw [(environmentStep_tables runtime state next command reached).1]

/-- An accepted inclusion either installs, for a binding event, the handle its
envelope commits to, or leaves every accepted handle of a binding event as it
was. -/
theorem includePending_accepted (execution : (runtime.reactiveApplication leaks).Execution)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (installed : (execution.includePending (runtime.reactiveApplication leaks)
      id).application.accepted (.inr event) = some candidate) :
    execution.application.accepted (.inr event) = some candidate ∨
      ∃ envelope, execution.network.lookup id = some envelope ∧
        envelope.payload.call = .commitment event candidate ∧ candidate.1 = envelope.sender := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending at installed
  cases found : execution.network.lookup id with
  | none =>
      simp only [found] at installed
      exact Or.inl installed
  | some envelope =>
      simp only [found] at installed
      cases accepted :
          (runtime.reactiveApplication leaks).handle execution.application envelope with
      | none =>
          simp only [accepted, Option.getD_none] at installed
          exact Or.inl installed
      | some next =>
          simp only [accepted, Option.getD_some] at installed
          rcases handle_tables_cases runtime execution.application next _
              (reactiveHandle_call accepted) with
            ⟨named, committed, call, _, acceptedEq, owner⟩ | ⟨acceptedEq, _⟩
          · rw [acceptedEq] at installed
            by_cases same : event = named
            · subst same
              rw [Function.update_self] at installed
              cases Option.some.inj installed
              exact Or.inr ⟨envelope, rfl, call, owner⟩
            · rw [Function.update_of_ne (by simpa using same)] at installed
              exact Or.inl installed
          · rw [acceptedEq] at installed
            exact Or.inl installed

/-- A response leaves every other player's recall and appends one entry to
the responder's, which records the envelope the response emits. -/
theorem respond_recall (execution : (runtime.reactiveApplication leaks).Execution)
    (who observer : Player) (action : (runtime.reactiveApplication leaks).Action) :
    (execution.respond (runtime.reactiveApplication leaks) who action).recall observer =
      if observer = who then execution.recall who ++
        [⟨execution.observe (runtime.reactiveApplication leaks) who, action,
          action.transmission.map fun material =>
            ⟨(who, execution.network.nextSerial who),
              (runtime.reactiveApplication leaks).packet
                ((runtime.reactiveApplication leaks).submit execution.application who material)
                who (execution.network.known who) material⟩⟩]
      else execution.recall observer := by
  rcases action with ⟨_ | material⟩ <;> rfl

/-- Every envelope a player recalls emitting is signed by it and carries the
packet of the submission it recalls. -/
def EmissionsRecorded (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ message, entry.emitted = some message →
    message.sender = who ∧ ∃ material, entry.action.transmission = some material ∧
      message.payload.call = material.call.packet

/-- **Own signed data behind commitments and accepted handles.** -/
structure SignedCommitments (execution : (runtime.reactiveApplication leaks).Execution) :
    Prop where
  provenance : execution.Provenance (runtime.reactiveApplication leaks)
  emissions : EmissionsRecorded runtime leaks execution
  ownFixed : ∀ who, ∀ message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall who),
    ∀ event slot, message.payload.call = .commitment event (who, slot) →
      execution.application.candidates.lookup (who, slot) ≠ .fresh
  acceptedSigned : ∀ event candidate,
    execution.application.accepted (.inr event) = some candidate →
      ∃ message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall candidate.1),
        message.payload.call = .commitment event candidate
  inputHandles : ∀ input candidate, execution.application.accepted (.inl input) = some candidate →
    candidate.2 = .initial input

theorem signedCommitments_initial (inputs : graph.Inputs) :
    SignedCommitments runtime leaks
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks)
        (State.initial inputs)) where
  provenance := MessageNetwork.Satisfies.empty
  emissions _ _ member := (List.not_mem_nil member).elim
  ownFixed _ _ member := (List.not_mem_nil member).elim
  acceptedSigned event candidate accepted := by
    obtain ⟨_, _, _, field, _, _⟩ := State.initial_accepted_eq_some inputs _ candidate accepted
    cases field
  inputHandles input candidate accepted := by
    obtain ⟨_, owner, _, field, _, rfl⟩ :=
      State.initial_accepted_eq_some inputs _ candidate accepted
    cases field
    rfl

/-- The invariant survives every response, whatever its content. -/
theorem SignedCommitments.respond {execution : (runtime.reactiveApplication leaks).Execution}
    (valid : SignedCommitments runtime leaks execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    SignedCommitments runtime leaks (execution.respond (runtime.reactiveApplication leaks) who
      action) := by
  let app := runtime.reactiveApplication leaks
  have fixes := (fixesCandidates_step runtime leaks).respond execution who action
  have inputs := (keepsInputHandles_step runtime leaks).respond execution who action
  have acceptedSame : (execution.respond app who action).application.accepted =
      execution.application.accepted := by
    rcases action with ⟨_ | material⟩
    · rfl
    · change (submitStep (material.call.register execution.application who) who
        material.call.packet).accepted = _
      rw [submitStep_accepted, Submission.register_accepted]
  have outputsMono (observer : Player) :
      app.outputs (execution.recall observer) ⊆
        app.outputs ((execution.respond app who action).recall observer) := by
    intro message member
    obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
    exact List.mem_filterMap.mpr
      ⟨entry, app.respond_recall_mono execution who observer action entryMember, emitted⟩
  refine ⟨app.respond_provenance execution who action valid.provenance, ?_, ?_, ?_, ?_⟩
  · intro observer entry member message emitted
    rw [respond_recall] at member
    split at member
    · rename_i same
      subst same
      rcases List.mem_append.mp member with old | new
      · exact valid.emissions observer entry old message emitted
      · obtain rfl := List.mem_singleton.mp new
        rcases action with ⟨_ | material⟩
        · cases emitted
        · cases Option.some.inj emitted
          exact ⟨rfl, material, rfl, rfl⟩
    · exact valid.emissions observer entry member message emitted
  · intro observer message member event slot call
    obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
    rw [respond_recall] at entryMember
    split at entryMember
    · rename_i same
      subst same
      rcases List.mem_append.mp entryMember with old | new
      · exact fixes _ (valid.ownFixed observer message
          (List.mem_filterMap.mpr ⟨entry, old, emitted⟩) event slot call)
      · obtain rfl := List.mem_singleton.mp new
        rcases action with ⟨_ | material⟩
        · cases emitted
        · cases Option.some.inj emitted
          change (submitStep (material.call.register execution.application observer) observer
            material.call.packet).candidates.lookup (observer, slot) ≠ .fresh
          change material.call.packet = _ at call
          rw [call]
          exact submitStep_commitment_fixed _ observer event slot
    · exact fixes _ (valid.ownFixed observer message
        (List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩) event slot call)
  · intro event candidate accepted
    rw [acceptedSame] at accepted
    obtain ⟨message, member, call⟩ := valid.acceptedSigned event candidate accepted
    exact ⟨message, outputsMono candidate.1 member, call⟩
  · intro input candidate accepted
    rw [inputs input] at accepted
    exact valid.inputHandles input candidate accepted

/-- The invariant survives every environment step. -/
theorem SignedCommitments.environmentStep
    {execution next : (runtime.reactiveApplication leaks).Execution}
    (valid : SignedCommitments runtime leaks execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    SignedCommitments runtime leaks next := by
  let app := runtime.reactiveApplication leaks
  have recallSame := app.environmentStep_recall execution next command reached
  have fixes := (fixesCandidates_step runtime leaks).environmentStep execution next command
    reached
  have inputs := (keepsInputHandles_step runtime leaks).environmentStep execution next command
    reached
  refine ⟨app.environment_provenance execution next command valid.provenance reached, ?_, ?_, ?_,
    ?_⟩
  · intro who entry member
    rw [recallSame] at member
    exact valid.emissions who entry member
  · intro who message member event slot call
    rw [recallSame] at member
    exact fixes _ (valid.ownFixed who message member event slot call)
  · intro event candidate accepted
    rw [recallSame]
    have origin : execution.application.accepted (.inr event) = some candidate ∨
        ∃ envelope ∈ app.outputs (execution.recall candidate.1),
          envelope.payload.call = .commitment event candidate := by
      cases command with
      | wait =>
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact Or.inl accepted
      | activate observer =>
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
          obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact Or.inl accepted
      | «include» id =>
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          rcases includePending_accepted runtime leaks execution id event candidate accepted with
            old | ⟨envelope, found, call, owner⟩
          · exact Or.inl old
          · right
            obtain ⟨entry, member, _, _, emitted, _⟩ := valid.provenance.lookup id envelope found
            refine ⟨envelope, ?_, call⟩
            rw [owner]
            exact List.mem_filterMap.mpr ⟨entry, member, emitted⟩
      | application command =>
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
          obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
          rw [(environmentStep_tables runtime execution.application state command changed).1]
            at accepted
          exact Or.inl accepted
    rcases origin with old | signed
    · exact valid.acceptedSigned event candidate old
    · exact signed
  · intro input candidate accepted
    rw [inputs input] at accepted
    exact valid.inputHandles input candidate accepted

/-- The invariant is a service invariant under every scheduler. -/
theorem signedCommitments_invariant (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (SignedCommitments runtime leaks) where
  respond _ who action valid := valid.respond runtime leaks who action
  environment _ _ command valid _ reached := valid.environmentStep runtime leaks command reached

/-- **Signed commitments along every history.** Under an initial law of
initial runtime states, every history of the runtime, under arbitrary responses
and scheduler choices, satisfies the invariant. -/
theorem signedCommitments_history (initial : PMF (runtime.reactiveApplication leaks).State)
    (initialized : ∀ state ∈ initial.support, ∃ inputs, state = State.initial inputs)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    SignedCommitments runtime leaks control.execution :=
  (signedCommitments_invariant runtime leaks scheduler).history initial horizon
    (fun state supported => by
      obtain ⟨inputs, rfl⟩ := initialized state supported
      exact signedCommitments_initial runtime leaks inputs) trace

end Vegas.EventGraphRuntime

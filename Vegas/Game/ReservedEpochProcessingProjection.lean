/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochPhaseBindingFrame
import Vegas.Pending.PhaseBindingCountedIncludeMemory
import Vegas.Pending.PhaseResolution
import Vegas.Pending.PhaseNamespace

/-! # Actual same-namespace processing projected through the original native handler -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

/-- Retain the original drained native image of an actual binding inclusion,
including an inclusion that immediately retires or rolls back its namespace. -/
theorem binding_processing_snapshot (runtime : EventGraphRuntime graph)
    (before after : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ before.phases.head?) (commitment : phase.kind = .commitment)
    (inputs : (graph).Inputs) (valid : before.Invariant inputs)
    (owner : Player) (active : owner ∉ before.current.excluded)
    (message : Message Player (CommitAttemptPacket graph))
    (handled : before.handle runtime message = some after) :
    ∃ (event : (graph).EventId) (candidate : Handle graph) (native : State graph),
      message.payload.packet.call = .commitment event candidate ∧
      handle runtime before.current.native ⟨message.id, .commitment event candidate⟩ = some native ∧
      after = ({ before with current := ⟨native, before.current.excluded⟩ } :
        PhaseRuntimeState graph).normalize ∧
      BindingFrame program owner native
        (phase.drain ⟨native, before.current.excluded⟩).native ∧
      (message.sender ≠ owner → BindingFrame program owner before.current.native
        (phase.drain ⟨native, before.current.excluded⟩).native) := by
  have onlyCommitment : ∀ actual ∈ before.phases.head?, actual.kind = .commitment := by
    intro actual actualInstalled
    have same : actual = phase := Option.some.inj
      ((Option.mem_def.mp actualInstalled).symm.trans (Option.mem_def.mp installed))
    simpa only [same] using commitment
  obtain ⟨event, candidate, call⟩ := BindingShadow.accepted_call_in_commitment runtime
    before after onlyCommitment message handled
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · obtain ⟨native, nativeStep, normalized⟩ := Option.map_eq_some_iff.mp handled
    have nativeBinding := nativeStep
    rw [call] at nativeBinding
    have nativeValid := handle_invariant runtime before.current.native native
      ⟨message.id, .commitment event candidate⟩ valid.active nativeBinding
    have retained := commitment_drain_frame program phase commitment
      (⟨native, before.current.excluded⟩ : RecoveryState graph) inputs nativeValid owner active
    refine ⟨event, candidate, native, call, nativeBinding, ?_, retained, ?_⟩
    · rw [call] at normalized
      exact normalized.symm
    · intro different
      have beforeFrame := foreign_binding_frame program runtime before.current.native native inputs
        valid.active message.id event candidate owner message.sender different rfl nativeBinding
      exact beforeFrame.trans retained
  · cases handled

/-- Within its original commitment namespace an actual accepted envelope is
its native binding handler followed only by the existing automatic drain.
This includes an owner whose own chain has already finished. -/
theorem same_attempt_binding_projection (runtime : EventGraphRuntime graph)
    (before after : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ before.phases.head?) (commitment : phase.kind = .commitment)
    (inputs : (graph).Inputs) (valid : before.Invariant inputs) (ordered : before.Ordered)
    (owner : Player) (active : owner ∉ before.current.excluded)
    (message : Message Player (CommitAttemptPacket graph))
    (handled : before.handle runtime message = some after)
    (sameAttempt : after.attempt = before.attempt) :
    ∃ (event : (graph).EventId) (candidate : Handle graph) (native : State graph),
      message.payload.packet.call = .commitment event candidate ∧
      handle runtime before.current.native ⟨message.id, .commitment event candidate⟩ = some native ∧
      after.current.native = (phase.drain ⟨native, before.current.excluded⟩).native ∧
      after.phases = before.phases ∧ after.generation = before.generation ∧
      after.current.excluded = before.current.excluded ∧
      BindingFrame program owner native after.current.native ∧
      (message.sender ≠ owner →
        BindingFrame program owner before.current.native after.current.native) := by
  obtain ⟨event, candidate, native, call, nativeBinding, actual, retained, foreign⟩ :=
    binding_processing_snapshot program runtime before after phase installed commitment inputs
      valid owner active message handled
  let raw : PhaseRuntimeState graph :=
    { before with current := ⟨native, before.current.excluded⟩ }
  have namespaceEq : raw.attempt = raw.normalize.attempt := by
    change before.attempt = raw.normalize.attempt
    rw [← actual]
    exact sameAttempt.symm
  have shape := PhaseRuntimeState.settle_of_same_namespace raw.phases raw.generation
    raw.entry raw.current raw.retired ordered namespaceEq
  have rawInstalled : phase ∈ raw.phases.head? := installed
  have drained : raw.normalize = { raw with current := phase.drain raw.current } := by
    change PhaseRuntimeState.settle _ _ _ _ _ = _
    rw [shape]
    simp only [Option.mem_def.mp rawInstalled, Option.elim_some]
  have postFrame : BindingFrame program owner native after.current.native := by
    rw [actual, drained]
    exact retained
  refine ⟨event, candidate, native, call, nativeBinding, ?_, ?_, ?_, ?_, postFrame, ?_⟩
  · rw [actual, drained]
  · rw [actual, drained]
  · rw [actual, drained]
  · rw [actual, drained]
    exact phase.drain_excluded _
  · intro different
    rw [actual, drained]
    exact foreign different

/-- Processing the same owned envelope has the same receipt and owner-local
effect in two actual surviving commitment namespaces. The packet may reject;
no handler result is supplied as a counterpart premise. -/
theorem same_attempt_owned_processing_pair (runtime : EventGraphRuntime graph)
    (left right nextLeft nextRight : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (leftInstalled : phase ∈ left.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (leftValid : left.Invariant inputs) (rightValid : right.Invariant inputs)
    (leftOrdered : left.Ordered) (rightOrdered : right.Ordered)
    (owner : Player) (active : owner ∉ left.current.excluded)
    (frame : BindingFrame program owner left.current.native right.current.native)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (excluded : left.current.excluded = right.current.excluded)
    (message : Message Player (CommitAttemptPacket graph)) (sender : message.sender = owner)
    (leftStep : nextLeft = (left.handle runtime message).getD left)
    (rightStep : nextRight = (right.handle runtime message).getD right)
    (leftSame : nextLeft.attempt = left.attempt)
    (rightSame : nextRight.attempt = right.attempt) :
    (left.handle runtime message).isSome = (right.handle runtime message).isSome ∧
      BindingFrame program owner nextLeft.current.native nextRight.current.native ∧
      nextLeft.phases = left.phases ∧ nextRight.phases = right.phases ∧
      nextLeft.generation = left.generation ∧ nextRight.generation = right.generation ∧
      nextLeft.current.excluded = left.current.excluded ∧
      nextRight.current.excluded = right.current.excluded := by
  have rightInstalled : phase ∈ right.phases.head? := by
    simpa only [← phases] using leftInstalled
  have rightActive : owner ∉ right.current.excluded := by
    simpa only [← excluded] using active
  have onlyCommitment : ∀ actual ∈ left.phases.head?, actual.kind = .commitment := by
    intro actual installed
    have same : actual = phase := Option.some.inj
      ((Option.mem_def.mp installed).symm.trans (Option.mem_def.mp leftInstalled))
    simpa only [same] using commitment
  cases first : left.handle runtime message with
  | none =>
      cases second : right.handle runtime message with
      | none =>
          simp only [first, Option.getD_none] at leftStep
          simp only [second, Option.getD_none] at rightStep
          subst nextLeft
          subst nextRight
          exact ⟨rfl, frame, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some result =>
          have rightCommitment : ∀ actual ∈ right.phases.head?,
              actual.kind = .commitment := by simpa only [← phases] using onlyCommitment
          obtain ⟨event, candidate, call⟩ := BindingShadow.accepted_call_in_commitment runtime
            right result rightCommitment message second
          have receipts := phase_binding_receipt_congr program runtime left right owner message
            event candidate frame phases generation excluded sender call
          simp only [first, second, Option.isSome_none, Option.isSome_some] at receipts
          cases receipts
  | some result =>
      obtain ⟨event, candidate, call⟩ := BindingShadow.accepted_call_in_commitment runtime
        left result onlyCommitment message first
      obtain ⟨rawLeft, rawRight, leftNative, rightNative, _leftNormalized,
        rightHandled, rawFrame⟩ := phase_binding_handler_counterpart program runtime
          left right result owner message event candidate frame phases generation excluded
            sender call first
      simp only [first, Option.getD_some] at leftStep
      subst nextLeft
      let resultRight : PhaseRuntimeState graph :=
        ({ right with current := ⟨rawRight, right.current.excluded⟩ } :
          PhaseRuntimeState graph).normalize
      have rightActual : right.handle runtime message = some resultRight := rightHandled
      simp only [rightActual, Option.getD_some] at rightStep
      subst nextRight
      obtain ⟨leftEvent, leftCandidate, actualLeft, leftCall, actualLeftLaw, _, leftPhases,
        leftGeneration, leftExcluded, leftDrain, _⟩ := same_attempt_binding_projection program
          runtime left result phase leftInstalled commitment inputs leftValid leftOrdered owner
            active message first leftSame
      obtain ⟨rightEvent, rightCandidate, actualRight, rightCall, actualRightLaw, _, rightPhases,
        rightGeneration, rightExcluded, rightDrain, _⟩ := same_attempt_binding_projection program
          runtime right resultRight phase rightInstalled commitment inputs rightValid rightOrdered
            owner rightActive message rightActual rightSame
      have sameLeft : rawLeft = actualLeft := by
        have actual : handle runtime left.current.native
            ⟨message.id, message.payload.packet.call⟩ = some actualLeft := by
          simpa only [leftCall] using actualLeftLaw
        have supplied : handle runtime left.current.native
            ⟨message.id, message.payload.packet.call⟩ = some rawLeft := by
          simpa only [call] using leftNative
        exact Option.some.inj (supplied.symm.trans actual)
      have sameRight : rawRight = actualRight := by
        have actual : handle runtime right.current.native
            ⟨message.id, message.payload.packet.call⟩ = some actualRight := by
          simpa only [rightCall] using actualRightLaw
        have supplied : handle runtime right.current.native
            ⟨message.id, message.payload.packet.call⟩ = some rawRight := by
          simpa only [call] using rightNative
        exact Option.some.inj (supplied.symm.trans actual)
      rw [← sameLeft] at leftDrain
      rw [← sameRight] at rightDrain
      refine ⟨?_, leftDrain.symm.trans (rawFrame.trans rightDrain), leftPhases, rightPhases,
        leftGeneration, rightGeneration, leftExcluded, rightExcluded⟩
      simp only [rightActual, Option.isSome_some]

/-- An arbitrary foreign or stale packet is a stutter on a surviving owner's
complete binding frame. A foreign owner need not have an unfinished request. -/
theorem same_attempt_foreign_processing (runtime : EventGraphRuntime graph)
    (before after : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ before.phases.head?) (commitment : phase.kind = .commitment)
    (inputs : (graph).Inputs) (valid : before.Invariant inputs) (ordered : before.Ordered)
    (owner : Player) (active : owner ∉ before.current.excluded)
    (message : Message Player (CommitAttemptPacket graph))
    (other : message.sender ≠ owner ∨ message.payload.attempt ≠ before.attempt)
    (step : after = (before.handle runtime message).getD before)
    (sameAttempt : after.attempt = before.attempt) :
    BindingFrame program owner before.current.native after.current.native ∧
      after.phases = before.phases ∧ after.generation = before.generation ∧
      after.current.excluded = before.current.excluded := by
  cases handled : before.handle runtime message with
  | none =>
      simp only [handled, Option.getD_none] at step
      subst after
      exact ⟨BindingFrame.refl owner before.current.native, rfl, rfl, rfl⟩
  | some result =>
      simp only [handled, Option.getD_some] at step
      subst after
      have different : message.sender ≠ owner := by
        rcases other with different | stale
        · exact different
        · rw [before.handle_retired runtime message stale] at handled
          cases handled
      obtain ⟨_, _, _, _, _, _, phases, generation, excluded, _, retained⟩ :=
        same_attempt_binding_projection program runtime before result phase installed commitment
          inputs valid ordered owner active message handled sameAttempt
      exact ⟨retained different, phases, generation, excluded⟩

private theorem processing_fold_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (packets : List (Message Player (CommitAttemptPacket graph)))
    (before : PhaseRuntimeState graph) (ordered : before.Ordered) :
    let after := packets.foldl (fun state message => (state.handle runtime message).getD state)
      before
    after.Ordered ∧ before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase := by
  induction packets generalizing before with
  | nil => exact ⟨ordered, le_rfl, le_rfl⟩
  | cons message rest ih =>
      cases handled : before.handle runtime message with
      | none => simpa only [List.foldl_cons, handled, Option.getD_none] using ih before ordered
      | some next =>
          have nextOrdered := (phaseApplication_seedOrder runtime leaks).handle
            before message next ordered handled
          have step := (phaseApplication_namespace_progress runtime leaks).handle
            before message next handled ordered
          have later := ih next nextOrdered
          simpa only [List.foldl_cons, handled, Option.getD_some] using
            And.intro later.1 ⟨step.1.trans later.2.1, step.2.trans later.2.2⟩

private theorem processing_prefix_same_attempt (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (packets : List (Message Player (CommitAttemptPacket graph)))
    (before : PhaseRuntimeState graph) (ordered : before.Ordered)
    (same : (packets.foldl (fun state message => (state.handle runtime message).getD state)
      before).attempt = before.attempt) (count : Nat) :
    ((packets.take count).foldl
      (fun state message => (state.handle runtime message).getD state) before).attempt =
        before.attempt := by
  let middle := (packets.take count).foldl
    (fun state message => (state.handle runtime message).getD state) before
  have first := processing_fold_progress program runtime leaks (packets.take count) before ordered
  have second := processing_fold_progress program runtime leaks (packets.drop count) middle first.1
  have final : (packets.drop count).foldl
      (fun state message => (state.handle runtime message).getD state) middle =
        packets.foldl (fun state message => (state.handle runtime message).getD state) before := by
    dsimp only [middle]
    rw [← List.foldl_append, List.take_append_drop]
  dsimp only at first second
  rw [final, same] at second
  have generation : middle.attempt.generation = before.attempt.generation :=
    Nat.le_antisymm second.2.1 first.2.1
  have phase : middle.attempt.phase = before.attempt.phase :=
    Nat.le_antisymm second.2.2 first.2.2
  change (⟨middle.attempt.phase, middle.attempt.generation⟩ : CommitAttemptId) =
    ⟨before.attempt.phase, before.attempt.generation⟩
  rw [generation, phase]

/-- A whole actual phase-handler fold of foreign and retired backlog preserves
the selected surviving cone, even after that owner's chain is already done.
Only the real endpoint's namespace is assumed; monotonicity supplies every
intermediate namespace needed by the induction. -/
theorem same_attempt_foreign_batch (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (packets : List (Message Player (CommitAttemptPacket graph)))
    (before : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ before.phases.head?) (commitment : phase.kind = .commitment)
    (inputs : (graph).Inputs) (valid : before.Invariant inputs) (ordered : before.Ordered)
    (owner : Player) (active : owner ∉ before.current.excluded)
    (other : ∀ message ∈ packets,
      message.sender ≠ owner ∨ message.payload.attempt ≠ before.attempt)
    (same : (packets.foldl (fun state message => (state.handle runtime message).getD state)
      before).attempt = before.attempt) :
    let after := packets.foldl (fun state message => (state.handle runtime message).getD state)
      before
    BindingFrame program owner before.current.native after.current.native ∧
      after.phases = before.phases ∧ after.generation = before.generation ∧
      after.current.excluded = before.current.excluded := by
  induction packets generalizing before with
  | nil => exact ⟨BindingFrame.refl owner before.current.native, rfl, rfl, rfl⟩
  | cons message rest ih =>
      let next := (before.handle runtime message).getD before
      have nextSame : next.attempt = before.attempt := by
        have initialPrefix := processing_prefix_same_attempt program runtime leaks (message :: rest)
          before ordered same 1
        simpa only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
          using initialPrefix
      have retained := same_attempt_foreign_processing program runtime before next phase installed
        commitment inputs valid ordered owner active message (other message (List.mem_cons_self ..))
          rfl nextSame
      have nextValid : next.Invariant inputs := by
        cases handled : before.handle runtime message with
        | none => simpa only [next, handled, Option.getD_none] using valid
        | some state =>
            simpa only [next, handled, Option.getD_some] using
              (phaseApplication_invariant runtime leaks inputs).handle before message state valid
                handled
      have nextOrdered :=
        (processing_fold_progress program runtime leaks [message] before ordered).1
      change next.Ordered at nextOrdered
      have nextInstalled : phase ∈ next.phases.head? := by
        simpa only [retained.2.1] using installed
      have nextActive : owner ∉ next.current.excluded := by
        simpa only [retained.2.2.2] using active
      have remaining : ∀ packet ∈ rest,
          packet.sender ≠ owner ∨ packet.payload.attempt ≠ next.attempt := by
        intro packet member
        simpa only [nextSame] using other packet (List.mem_cons_of_mem _ member)
      have finalSame : (rest.foldl
          (fun state packet => (state.handle runtime packet).getD state) next).attempt =
            next.attempt := by
        simpa only [List.foldl_cons] using same.trans nextSame.symm
      have after := ih next nextInstalled nextValid nextOrdered nextActive remaining finalSame
      change BindingFrame program owner before.current.native
          (rest.foldl (fun state packet => (state.handle runtime packet).getD state)
            next).current.native ∧
        _
      exact ⟨retained.1.trans after.1, after.2.1.trans retained.2.1,
        after.2.2.1.trans retained.2.2.1, after.2.2.2.trans retained.2.2.2⟩

end Vegas.EventGraphRuntime.ReservedEpoch

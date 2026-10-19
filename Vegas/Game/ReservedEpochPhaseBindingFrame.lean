/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochDrainFrame
import Vegas.Game.ReservedEpochBindingFrontier

/-! # Actual phase-handler counterparts before each attempt's own exit -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem phase_binding_request_congr (left right : PhaseRuntimeState graph) (owner : Player)
    (frame : BindingFrame program owner left.current.native right.current.native)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (excluded : left.current.excluded = right.current.excluded)
    (opaquePhase : ∀ phase ∈ left.phases.head?, phase.kind = .commitment)
    (coordinate : CommitAttemptEvent graph) :
    left.SeedRequest owner coordinate ↔ right.SeedRequest owner coordinate := by
  have transport (first second : PhaseRuntimeState graph)
      (paired : BindingFrame program owner first.current.native second.current.native)
      (phases : first.phases = second.phases) (generation : first.generation = second.generation)
      (excluded : first.current.excluded = second.current.excluded)
      (isCommitment : ∀ phase ∈ first.phases.head?, phase.kind = .commitment)
      (requested : first.SeedRequest owner coordinate) : second.SeedRequest owner coordinate := by
    obtain ⟨phase, installed, inside⟩ := requested.2.1
    obtain ⟨low, high⟩ := (phase.mem_events coordinate.event).mp inside
    obtain ⟨who, payload, binding⟩ := by
      simpa only [isCommitment phase installed] using phase.fields coordinate.event low high
    have sameOwner : who = owner := Option.some.inj
      (((graph).actor?_of_outputLayout_binding binding).symm.trans requested.2.2.2.1)
    subst who
    have sameAttempt : first.attempt = second.attempt := by
      simp only [PhaseRuntimeState.attempt, phases, generation]
    refine ⟨requested.1.trans sameAttempt, ⟨phase, ?_, inside⟩,
      (paired.ready coordinate.event payload binding).mp requested.2.2.1,
      requested.2.2.2.1, ?_⟩
    · simpa only [phases] using installed
    · simpa only [excluded] using requested.2.2.2.2
  constructor
  · exact transport left right frame phases generation excluded opaquePhase
  · exact transport right left frame.symm phases.symm generation.symm excluded.symm
      (by simpa only [phases] using opaquePhase)

theorem normalize_eq_drain_of_unfinished_owner (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (installed : phase ∈ state.phases.head?) (owner : Player)
    (survivor : owner ∉ state.current.excluded)
    (unfinished : ∃ event ∈ phase.events, (graph).actor? event = some owner ∧
      event ∉ state.current.native.config.cut.completed) :
    state.normalize = { state with current := phase.drain state.current } := by
  classical
  obtain ⟨event, inside, actor, missing⟩ := unfinished
  have absent : event ∉ (phase.drain state.current).native.config.cut.completed := by
    intro completed
    have retained := phase.drainFuel_completed_survivor
      state.current.native.config.remaining state.current event owner actor survivor
    exact missing (retained.mp completed)
  have notFinished : ¬ phase.Finished (phase.drain state.current) :=
    fun finished => absent (finished inside)
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  simp only [PhaseRuntimeState.normalize, phases, PhaseRuntimeState.settle,
    ite_eq_right notFinished]

theorem normalize_unfinished_owner_frame (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (installed : phase ∈ state.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (valid : state.current.native.Invariant inputs) (owner : Player)
    (survivor : owner ∉ state.current.excluded)
    (unfinished : ∃ event ∈ phase.events, (graph).actor? event = some owner ∧
      event ∉ state.current.native.config.cut.completed) :
    BindingFrame program owner state.current.native state.normalize.current.native := by
  rw [normalize_eq_drain_of_unfinished_owner program state phase installed owner survivor
    unfinished]
  exact commitment_drain_frame program phase commitment state.current inputs valid owner survivor

/-- An actual different-owner binding inclusion, including its automatic
normalization, stutters on a still-requested owner's complete native frame. -/
theorem phase_foreign_binding_frame (runtime : EventGraphRuntime graph)
    (before after : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ before.phases.head?) (commitment : phase.kind = .commitment)
    (inputs : (graph).Inputs) (valid : before.current.native.Invariant inputs)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : before.SeedRequest owner coordinate)
    (message : Message Player (CommitAttemptPacket graph)) (event : (graph).EventId)
    (candidate : Handle graph) (different : message.sender ≠ owner)
    (binding : message.payload.packet.call = .commitment event candidate)
    (handled : before.handle runtime message = some after) :
    BindingFrame program owner before.current.native after.current.native ∧
      after.phases = before.phases := by
  obtain ⟨actualPhase, actualInstalled, inside⟩ := requested.2.1
  have samePhase : actualPhase = phase := by
    have first := Option.mem_def.mp actualInstalled
    have second := Option.mem_def.mp installed
    exact Option.some.inj (first.symm.trans second)
  subst actualPhase
  obtain ⟨low, high⟩ := (phase.mem_events coordinate.event).mp inside
  obtain ⟨who, payload, typed⟩ := by
    simpa only [commitment] using phase.fields coordinate.event low high
  have whoEq : who = owner := Option.some.inj
    (((graph).actor?_of_outputLayout_binding typed).symm.trans requested.2.2.2.1)
  subst who
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · obtain ⟨native, nativeHandled, normalized⟩ := Option.map_eq_some_iff.mp handled
    have nativeBinding := nativeHandled
    rw [binding] at nativeBinding
    have nativeFrame := foreign_binding_frame program runtime before.current.native native inputs
      valid message.id event candidate owner message.sender different rfl nativeBinding
    have nativeValid := handle_invariant runtime before.current.native native
      ⟨message.id, .commitment event candidate⟩ valid nativeBinding
    let raw : PhaseRuntimeState graph :=
      { before with current := ⟨native, before.current.excluded⟩ }
    have rawInstalled : phase ∈ raw.phases.head? := installed
    have unfinished : ∃ pending ∈ phase.events, (graph).actor? pending = some owner ∧
        pending ∉ raw.current.native.config.cut.completed := by
      refine ⟨coordinate.event, inside, requested.2.2.2.1, ?_⟩
      exact ((nativeFrame.ready coordinate.event payload typed).mp requested.2.2.1).1
    have drainFrame := normalize_unfinished_owner_frame program raw phase rawInstalled commitment
      inputs nativeValid owner requested.2.2.2.2 unfinished
    have afterEq : after = raw.normalize := by
      rw [binding] at normalized
      exact normalized.symm
    refine ⟨?_, ?_⟩
    · rw [afterEq]
      exact nativeFrame.trans drainFrame
    · rw [afterEq, normalize_eq_drain_of_unfinished_owner program raw phase rawInstalled owner
        requested.2.2.2.2 unfinished]
  · cases handled

/-- Reflect an actual accepted binding through the native owner frame. Both
normalization results are actual phase handlers; neither is assumed to remain
in the attempt, and the original native witnesses remain in the conclusion. -/
theorem phase_binding_handler_counterpart (runtime : EventGraphRuntime graph)
    (left right next : PhaseRuntimeState graph) (owner : Player)
    (message : Message Player (CommitAttemptPacket graph)) (event : (graph).EventId)
    (candidate : Handle graph)
    (frame : BindingFrame program owner left.current.native right.current.native)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (excluded : left.current.excluded = right.current.excluded)
    (sender : message.sender = owner)
    (binding : message.payload.packet.call = .commitment event candidate)
    (handled : left.handle runtime message = some next) :
    ∃ first second : State graph,
      handle runtime left.current.native ⟨message.id, .commitment event candidate⟩ = some first ∧
      handle runtime right.current.native ⟨message.id, .commitment event candidate⟩ = some second ∧
      next = ({ left with current := ⟨first, left.current.excluded⟩ } :
        PhaseRuntimeState graph).normalize ∧
      right.handle runtime message = some
        (({ right with current := ⟨second, right.current.excluded⟩ } :
          PhaseRuntimeState graph).normalize) ∧
      BindingFrame program owner first second := by
  have attemptEq : left.attempt = right.attempt := by
    simp only [PhaseRuntimeState.attempt, phases, generation]
  have allowed : left.allows message.payload.packet.call =
      right.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, phases]
  have excludedCall : left.current.excludedCall message.payload.packet.call =
      right.current.excludedCall message.payload.packet.call := by
    simp only [RecoveryState.excludedCall, RecoveryState.excludedEvent, excluded]
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · rename_i gate
    obtain ⟨first, native, normalized⟩ := Option.map_eq_some_iff.mp handled
    have nativeBinding := native
    rw [binding] at nativeBinding
    obtain ⟨second, counterpart, nextFrame⟩ :=
      BindingFrame.handle_binding program frame runtime first message.id event candidate sender
        nativeBinding
    have rightGate := gate
    rw [attemptEq, allowed, excludedCall] at rightGate
    refine ⟨first, second, nativeBinding, counterpart, ?_, ?_, nextFrame⟩
    · rw [binding] at normalized
      exact normalized.symm
    · unfold PhaseRuntimeState.handle
      rw [ite_eq_left rightGate]
      rw [binding]
      simp only [counterpart, Option.map_some, RecoveryState.inclusionResult]
  · cases handled

/-- Receipt equality is derived from the actual two phase handlers, even if
one of their accepting results closes its attempt earlier than the other. -/
theorem phase_binding_receipt_congr (runtime : EventGraphRuntime graph)
    (left right : PhaseRuntimeState graph) (owner : Player)
    (message : Message Player (CommitAttemptPacket graph)) (event : (graph).EventId)
    (candidate : Handle graph)
    (frame : BindingFrame program owner left.current.native right.current.native)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (excluded : left.current.excluded = right.current.excluded)
    (sender : message.sender = owner)
    (binding : message.payload.packet.call = .commitment event candidate) :
    (left.handle runtime message).isSome = (right.handle runtime message).isSome := by
  cases first : left.handle runtime message with
  | some next =>
      obtain ⟨_, _, _, _, _, accepted, _⟩ := phase_binding_handler_counterpart program runtime
        left right next owner message event candidate frame phases generation excluded sender
          binding first
      simp only [accepted, Option.isSome_some]
  | none =>
      cases second : right.handle runtime message with
      | none => rfl
      | some next =>
          obtain ⟨_, _, _, _, _, impossible, _⟩ :=
            phase_binding_handler_counterpart program runtime right left next owner message event
              candidate frame.symm phases.symm generation.symm excluded.symm sender binding second
          rw [first] at impossible
          cases impossible

end Vegas.EventGraphRuntime.ReservedEpoch

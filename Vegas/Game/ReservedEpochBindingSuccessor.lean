/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingNormalization
import Vegas.Pending.PhaseResolution

/-! # An actual accepted owned binding exposes the same paired successor -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem phase_binding_successor_pair (runtime : EventGraphRuntime graph)
    (left right nextLeft nextRight : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ left.phases.head?) (commitment : phase.kind = .commitment)
    (inputs : (graph).Inputs) (leftValid : left.Invariant inputs)
    (rightValid : right.Invariant inputs) (ordered : left.Ordered) (owner : Player)
    (active : owner ∉ left.current.excluded)
    (frame : BindingFrame program owner left.current.native right.current.native)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (excluded : left.current.excluded = right.current.excluded)
    (message : Message Player (CommitAttemptPacket graph)) (event : (graph).EventId)
    (candidate : Handle graph) (sender : message.sender = owner)
    (binding : message.payload.packet.call = .commitment event candidate)
    (first : left.handle runtime message = some nextLeft)
    (second : right.handle runtime message = some nextRight)
    (sameAttempt : nextLeft.attempt = left.attempt) (successor : CommitAttemptEvent graph)
    (nextRequest : nextLeft.SeedRequest owner successor) :
    BindingFrame program owner nextLeft.current.native nextRight.current.native ∧
      nextLeft.phases = nextRight.phases ∧ nextLeft.generation = nextRight.generation ∧
      nextLeft.current.excluded = nextRight.current.excluded ∧
      nextRight.SeedRequest owner successor := by
  obtain ⟨firstNative, secondNative, firstStep, secondStep, normalized, counterpart, paired⟩ :=
    phase_binding_handler_counterpart program runtime left right nextLeft owner message event
      candidate frame phases generation excluded sender binding first
  have rightEq := Option.some.inj (second.symm.trans counterpart)
  let firstRaw : PhaseRuntimeState graph :=
    { left with current := ⟨firstNative, left.current.excluded⟩ }
  let secondRaw : PhaseRuntimeState graph :=
    { right with current := ⟨secondNative, right.current.excluded⟩ }
  have firstNormalized : nextLeft = firstRaw.normalize := normalized
  have secondNormalized : nextRight = secondRaw.normalize := rightEq
  have rawAttempt : firstRaw.attempt = firstRaw.normalize.attempt := by
    change left.attempt = firstRaw.normalize.attempt
    rw [← firstNormalized]
    exact sameAttempt.symm
  have exactNormalization := PhaseRuntimeState.settle_of_same_namespace firstRaw.phases
    firstRaw.generation firstRaw.entry firstRaw.current firstRaw.retired ordered rawAttempt
  have rawInstalled : phase ∈ firstRaw.phases.head? := installed
  have drained : firstRaw.normalize =
      { firstRaw with current := phase.drain firstRaw.current } := by
    change PhaseRuntimeState.settle _ _ _ _ _ = _
    rw [exactNormalization]
    simp only [Option.mem_def.mp rawInstalled, Option.elim_some]
  have nextPhases : nextLeft.phases = left.phases := by
    rw [firstNormalized, drained]
  have nextNative : nextLeft.current.native = (phase.drain firstRaw.current).native := by
    rw [firstNormalized, drained]
  obtain ⟨selectedPhase, nextInstalled, inside⟩ := nextRequest.2.1
  have selectedEq : selectedPhase = phase := by
    rw [nextPhases] at nextInstalled
    exact Option.some.inj
      ((Option.mem_def.mp nextInstalled).symm.trans (Option.mem_def.mp installed))
  subst selectedPhase
  have unfinished : ∃ query ∈ phase.events, (graph).actor? query = some owner ∧
      query ∉ firstNative.config.cut.completed := by
    refine ⟨successor.event, inside, nextRequest.2.2.2.1, ?_⟩
    intro completed
    apply nextRequest.2.2.1.1
    rw [nextNative]
    exact phase.drain_completed firstRaw.current completed
  have firstInvariant := handle_invariant runtime left.current.native firstNative
    ⟨message.id, .commitment event candidate⟩ leftValid.active firstStep
  have secondInvariant := handle_invariant runtime right.current.native secondNative
    ⟨message.id, .commitment event candidate⟩ rightValid.active secondStep
  have closedPair := normalize_binding_pair_unfinished program firstRaw secondRaw phase installed
    commitment inputs firstInvariant secondInvariant owner active paired phases excluded unfinished
  have nextFrame : BindingFrame program owner nextLeft.current.native nextRight.current.native := by
    rw [firstNormalized, secondNormalized]
    exact closedPair.1
  have samePhases : nextLeft.phases = nextRight.phases := by
    rw [firstNormalized, secondNormalized, closedPair.2.1, closedPair.2.2.1]
    exact phases
  have sameGeneration : nextLeft.generation = nextRight.generation := by
    rw [firstNormalized, secondNormalized, closedPair.2.2.2.1, closedPair.2.2.2.2.1]
    exact generation
  have sameExcluded : nextLeft.current.excluded = nextRight.current.excluded := by
    rw [firstNormalized, secondNormalized, closedPair.2.2.2.2.2.1, closedPair.2.2.2.2.2.2]
    exact excluded
  refine ⟨nextFrame, samePhases, sameGeneration, sameExcluded, ?_⟩
  apply (phase_binding_request_congr program nextLeft nextRight owner nextFrame samePhases
    sameGeneration sameExcluded ?_ successor).mp nextRequest
  intro actual actualInstalled
  have same : actual = phase := Option.some.inj
    ((Option.mem_def.mp actualInstalled).symm.trans
      (by simpa only [nextPhases] using Option.mem_def.mp installed))
  simpa only [same] using commitment

end Vegas.EventGraphRuntime.ReservedEpoch

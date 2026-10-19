/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochForeignProcessing

/-! # Matching an owned receipt across actual differently ordered FIFO batches -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem processing_owned_receipt_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length)
    (playersLeft playersRight : Player → (phaseApplication runtime leaks).Policy)
    (cycle leftSlot rightSlot : Nat)
    (beforeLeft beforeRight middleLeft middleRight : (phaseApplication runtime leaks).Execution)
    (prefixLeft prefixRight restLeft restRight : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (leftCursor : beforeLeft.environmentRecall.length =
      cycle * cycleWidth («graph» := graph) packetBudget + leftSlot)
    (rightCursor : beforeRight.environmentRecall.length =
      cycle * cycleWidth («graph» := graph) packetBudget + rightSlot)
    (leftRoom : leftSlot + prefixLeft.length + 1 ≤ packetBudget)
    (rightRoom : rightSlot + prefixRight.length + 1 ≤ packetBudget)
    (epoch : tape.processes cycle = true)
    (leftPending : beforeLeft.network.pending = prefixLeft ++ message :: restLeft)
    (rightPending : beforeRight.network.pending = prefixRight ++ message :: restRight)
    (phase : RuntimePhase graph)
    (leftInstalled : phase ∈ beforeLeft.application.phases.head?)
    (rightInstalled : phase ∈ beforeRight.application.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (leftValid : beforeLeft.application.Invariant inputs)
    (rightValid : beforeRight.application.Invariant inputs)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (leftRequest : beforeLeft.application.SeedRequest owner coordinate)
    (rightRequest : beforeRight.application.SeedRequest owner coordinate)
    (frame : BindingFrame program owner beforeLeft.application.current.native
      beforeRight.application.current.native)
    (phases : beforeLeft.application.phases = beforeRight.application.phases)
    (excluded : beforeLeft.application.current.excluded = beforeRight.application.current.excluded)
    (leftForeign : ∀ packet ∈ prefixLeft,
      packet.sender ≠ owner ∨ packet.payload.attempt ≠ coordinate.attempt)
    (rightForeign : ∀ packet ∈ prefixRight,
      packet.sender ≠ owner ∨ packet.payload.attempt ≠ coordinate.attempt)
    (event : (graph).EventId) (candidate : Handle graph) (sender : message.sender = owner)
    (binding : message.payload.packet.call = .commitment event candidate)
    (leftReached : middleLeft ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) playersLeft prefixLeft.length beforeLeft).support)
    (rightReached : middleRight ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) playersRight
        prefixRight.length beforeRight).support) :
    middleLeft.network.pending = message :: restLeft ∧
      middleRight.network.pending = message :: restRight ∧
      (middleLeft.application.handle runtime message).isSome =
        (middleRight.application.handle runtime message).isSome ∧
      BindingFrame program owner middleLeft.application.current.native
        middleRight.application.current.native ∧
      middleLeft.application.phases = middleRight.application.phases ∧
      middleLeft.application.generation = middleRight.application.generation ∧
      middleLeft.application.current.excluded = middleRight.application.current.excluded ∧
      middleLeft.application.SeedRequest owner coordinate ∧
      middleRight.application.SeedRequest owner coordinate ∧
      middleLeft.application.phases = beforeLeft.application.phases ∧
      middleRight.application.phases = beforeRight.application.phases := by
  have left := foreign_processing_prefix_frame program runtime leaks packetBudget tape playersLeft
    cycle leftSlot prefixLeft (message :: restLeft) beforeLeft middleLeft
      leftCursor (by omega) epoch leftPending phase
        leftInstalled commitment inputs leftValid owner coordinate leftRequest leftForeign
          leftReached
  have right := foreign_processing_prefix_frame program runtime leaks packetBudget tape playersRight
    cycle rightSlot prefixRight (message :: restRight) beforeRight middleRight
      rightCursor (by omega) epoch rightPending phase
        rightInstalled commitment inputs rightValid owner coordinate rightRequest rightForeign
          rightReached
  have leftPhysical := processing_prefix_application runtime leaks packetBudget tape playersLeft
    cycle leftSlot prefixLeft (message :: restLeft) beforeLeft middleLeft
      leftCursor (by omega) epoch leftPending leftReached
  have rightPhysical := processing_prefix_application runtime leaks packetBudget tape playersRight
    cycle rightSlot prefixRight (message :: restRight) beforeRight middleRight
      rightCursor (by omega) epoch rightPending rightReached
  have paired := left.1.symm.trans (frame.trans right.1)
  have samePhases := left.2.2.1.trans (phases.trans right.2.2.1.symm)
  have sameExcluded := left.2.2.2.trans (excluded.trans right.2.2.2.symm)
  have sameAttempt := left.2.1.1.symm.trans right.2.1.1
  have sameGeneration : middleLeft.application.generation = middleRight.application.generation :=
    congrArg CommitAttemptId.generation sameAttempt
  exact ⟨leftPhysical.1, rightPhysical.1, phase_binding_receipt_congr program runtime
    middleLeft.application middleRight.application owner message event candidate paired samePhases
      sameGeneration sameExcluded sender binding, paired, samePhases, sameGeneration, sameExcluded,
    left.2.1, right.2.1, left.2.2.1, right.2.2.1⟩

end Vegas.EventGraphRuntime.ReservedEpoch

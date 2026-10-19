/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochMatchedPacket
import Vegas.Pending.ReservedEpochPendingFrontier

/-! # Authentic frontier matching inside actual reserved processing batches -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

/-- Actual counted provenance discharges the foreign-prefix condition of
frontier matching. Both returned native witnesses are the real handlers before
normalization, even when their FIFO positions or namespace-exit positions differ. -/
theorem counted_processing_owned_packet (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : (graph).RevealRelaxedOrdered) (initialInputs : PMF (graph).Inputs)
    (horizon : Nat) {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (playersLeft playersRight : Player → (phaseApplication runtime leaks).Policy)
    (cycle leftSlot rightSlot leftRemaining rightRemaining : Nat)
    (beforeLeft beforeRight afterLeft afterRight : (phaseApplication runtime leaks).Execution)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (initialInputs.map (PhaseRuntimeState.initial plan)) horizon
        (family runtime leaks packetBudget tape)).Trace (some ⟨leftRemaining, none, beforeLeft⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (initialInputs.map (PhaseRuntimeState.initial plan)) horizon
        (family runtime leaks packetBudget tape)).Trace (some ⟨rightRemaining, none, beforeRight⟩))
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
    (sender : message.sender = owner) (attempt : message.payload.attempt = coordinate.attempt)
    (event : (graph).EventId) (candidate : Handle graph)
    (binding : message.payload.packet.call = .commitment event candidate)
    (leftReached : afterLeft ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) playersLeft
        (prefixLeft.length + 1) beforeLeft).support)
    (rightReached : afterRight ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) playersRight
        (prefixRight.length + 1) beforeRight).support) :
    (∀ packet ∈ restLeft,
      packet.sender ≠ owner ∨ packet.payload.attempt ≠ coordinate.attempt) ∧
      (∀ packet ∈ restRight,
        packet.sender ≠ owner ∨ packet.payload.attempt ≠ coordinate.attempt) ∧
      ∃ middleLeft middleRight : (phaseApplication runtime leaks).Execution,
        middleLeft ∈ ((phaseApplication runtime leaks).runRounds
          (family runtime leaks packetBudget tape) playersLeft prefixLeft.length
            beforeLeft).support ∧
        middleRight ∈ ((phaseApplication runtime leaks).runRounds
          (family runtime leaks packetBudget tape) playersRight prefixRight.length
            beforeRight).support ∧
        BindingFrame program owner middleLeft.application.current.native
          middleRight.application.current.native ∧
        middleLeft.application.phases = middleRight.application.phases ∧
        middleLeft.application.generation = middleRight.application.generation ∧
        middleLeft.application.current.excluded = middleRight.application.current.excluded ∧
        middleLeft.application.SeedRequest owner coordinate ∧
        middleRight.application.SeedRequest owner coordinate ∧
        middleLeft.application.phases = beforeLeft.application.phases ∧
        middleRight.application.phases = beforeRight.application.phases ∧
        ∃ accepted : Bool,
          (message.id, accepted) ∈ afterLeft.receipts ∧
          (message.id, accepted) ∈ afterRight.receipts ∧
          (accepted = true → ∃ first second : State graph,
            handle runtime middleLeft.application.current.native
              ⟨message.id, .commitment event candidate⟩ = some first ∧
            handle runtime middleRight.application.current.native
              ⟨message.id, .commitment event candidate⟩ = some second ∧
            middleLeft.application.handle runtime message = some afterLeft.application ∧
            middleRight.application.handle runtime message = some afterRight.application ∧
            afterLeft.application = ({ middleLeft.application with
              current := ⟨first, middleLeft.application.current.excluded⟩ } :
                PhaseRuntimeState graph).normalize ∧
            afterRight.application = ({ middleRight.application with
              current := ⟨second, middleRight.application.current.excluded⟩ } :
                PhaseRuntimeState graph).normalize ∧
            BindingFrame program owner first second) := by
  have leftSurroundings := pending_frontier_surroundings runtime leaks bounds plan ordered
    initialInputs horizon (family runtime leaks packetBudget tape) ⟨leftRemaining, none, beforeLeft⟩
      leftTrace phase leftInstalled commitment owner coordinate leftRequest message sender attempt
        prefixLeft restLeft leftPending
  have rightSurroundings := pending_frontier_surroundings runtime leaks bounds plan ordered
    initialInputs horizon (family runtime leaks packetBudget tape)
      ⟨rightRemaining, none, beforeRight⟩ rightTrace phase rightInstalled commitment owner
      coordinate rightRequest message sender attempt
        prefixRight restRight rightPending
  exact ⟨leftSurroundings.2, rightSurroundings.2,
    processing_owned_packet_congr program runtime leaks packetBudget tape playersLeft playersRight
      cycle leftSlot rightSlot beforeLeft beforeRight afterLeft afterRight prefixLeft prefixRight
      restLeft restRight message leftCursor rightCursor leftRoom rightRoom epoch leftPending
      rightPending phase leftInstalled rightInstalled commitment inputs leftValid rightValid owner
      coordinate leftRequest rightRequest frame phases excluded
      leftSurroundings.1 rightSurroundings.1
      event candidate sender binding leftReached rightReached⟩

end Vegas.EventGraphRuntime.ReservedEpoch

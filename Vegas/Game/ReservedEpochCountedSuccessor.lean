/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochCountedProcessing
import Vegas.Game.ReservedEpochBindingSuccessor
import Interaction.ReactivePolicyInvariant

/-! # Actual counted frontier processing exposes the same owned successor -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

/-- Both differently positioned frontier envelopes are actually processed. If
the accepting left execution still has an owned successor, the right execution
has that same successor and normalized owner frame, without a supplied
counterpart handler or counterpart request. -/
theorem counted_processing_owned_successor (runtime : EventGraphRuntime graph)
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
        (prefixRight.length + 1) beforeRight).support)
    (sameAttempt : afterLeft.application.attempt = beforeLeft.application.attempt) :
    ∃ middleLeft middleRight : (phaseApplication runtime leaks).Execution,
      middleLeft ∈ ((phaseApplication runtime leaks).runRounds
        (family runtime leaks packetBudget tape) playersLeft prefixLeft.length beforeLeft).support ∧
      middleRight ∈ ((phaseApplication runtime leaks).runRounds
        (family runtime leaks packetBudget tape) playersRight
          prefixRight.length beforeRight).support ∧
      ∃ accepted : Bool,
        (message.id, accepted) ∈ afterLeft.receipts ∧
        (message.id, accepted) ∈ afterRight.receipts ∧
        (accepted = true → ∀ successor : CommitAttemptEvent graph,
          afterLeft.application.SeedRequest owner successor →
          BindingFrame program owner afterLeft.application.current.native
            afterRight.application.current.native ∧
          afterLeft.application.phases = afterRight.application.phases ∧
          afterLeft.application.generation = afterRight.application.generation ∧
          afterLeft.application.current.excluded = afterRight.application.current.excluded ∧
          afterRight.application.SeedRequest owner successor) := by
  let app := phaseApplication runtime leaks
  let scheduler := family runtime leaks packetBudget tape
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := initialInputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨_leftSuffix, _rightSuffix, middleLeft, middleRight, leftPrefix, rightPrefix,
    paired, middlePhases, middleGeneration, middleExcluded, leftMiddleRequest,
    _rightMiddleRequest, leftMiddlePhases, _rightMiddlePhases, accepted, leftReceipt,
    rightReceipt, handlers⟩ :=
    counted_processing_owned_packet program runtime leaks bounds plan ordered initialInputs horizon
      packetBudget tape playersLeft playersRight cycle leftSlot rightSlot leftRemaining
        rightRemaining beforeLeft beforeRight afterLeft afterRight leftTrace rightTrace
        prefixLeft prefixRight
        restLeft restRight message leftCursor rightCursor leftRoom rightRoom epoch leftPending
        rightPending phase leftInstalled rightInstalled commitment inputs leftValid rightValid owner
        coordinate leftRequest rightRequest frame phases excluded sender attempt event candidate
        binding leftReached rightReached
  refine ⟨middleLeft, middleRight, leftPrefix, rightPrefix, accepted, leftReceipt, rightReceipt, ?_⟩
  intro acceptedTrue successor nextRequest
  obtain ⟨_first, _second, _firstNative, _secondNative, firstHandled, secondHandled,
    _leftNormalized, _rightNormalized, _rawFrame⟩ := handlers acceptedTrue
  have firstInvariant := ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_invariant runtime leaks inputs) playersLeft
  have secondInvariant := ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_invariant runtime leaks inputs) playersRight
  have firstValid := firstInvariant.runRounds scheduler prefixLeft.length beforeLeft middleLeft
    leftValid leftPrefix
  have secondValid := secondInvariant.runRounds scheduler prefixRight.length beforeRight middleRight
    rightValid rightPrefix
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (by
      intro state supported
      obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input)
    (menu.toRawTrace initial horizon scheduler leftTrace)
  have orderedInvariant := ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_seedOrder runtime leaks) playersLeft
  have middleOrdered := orderedInvariant.runRounds scheduler prefixLeft.length beforeLeft middleLeft
    firstOrdered leftPrefix
  have installed : phase ∈ middleLeft.application.phases.head? := by
    rw [leftMiddlePhases]
    exact leftInstalled
  have original : beforeLeft.application.attempt = middleLeft.application.attempt :=
    leftRequest.1.symm.trans leftMiddleRequest.1
  exact phase_binding_successor_pair program runtime middleLeft.application middleRight.application
    afterLeft.application afterRight.application phase installed commitment inputs firstValid
      secondValid middleOrdered owner leftMiddleRequest.2.2.2.2 paired middlePhases
      middleGeneration middleExcluded message event candidate sender binding firstHandled
      secondHandled (sameAttempt.trans original) successor nextRequest

end Vegas.EventGraphRuntime.ReservedEpoch

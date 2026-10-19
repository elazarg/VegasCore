/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochMatchedProcessing
import Interaction.ReactiveStopping

/-! # Actual paired processing of a foreign owner’s next binding packet -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

private theorem processing_step_execution (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (players : Player → (phaseApplication runtime leaks).Policy) (cycle slot : Nat)
    (before after : (phaseApplication runtime leaks).Execution)
    (message : Message Player (CommitAttemptPacket graph))
    (rest : List (Message Player (CommitAttemptPacket graph)))
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth («graph» := graph) packetBudget + slot)
    (room : slot < packetBudget) (epoch : tape.processes cycle = true)
    (pending : before.network.pending = message :: rest)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) players 1 before).support) :
    after = { before.includePending (phaseApplication runtime leaks) message.id with
      environmentRecall := before.environmentRecall ++
        [⟨before.observeEnvironment (phaseApplication runtime leaks), .include message.id⟩] } := by
  simp only [ReactiveApplication.runRounds, PMF.bind_pure, ReactiveApplication.round,
    family, PMF.pure_bind] at reached
  rw [cursor, processing_at runtime leaks packetBudget tape cycle slot _ room epoch,
    process_dispatch runtime leaks players before message rest pending] at reached
  exact (PMF.mem_support_pure_iff _ _).mp reached

theorem processing_owned_packet_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length)
    (playersLeft playersRight : Player → (phaseApplication runtime leaks).Policy)
    (cycle leftSlot rightSlot : Nat)
    (beforeLeft beforeRight afterLeft afterRight : (phaseApplication runtime leaks).Execution)
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
    (leftReached : afterLeft ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) playersLeft
        (prefixLeft.length + 1) beforeLeft).support)
    (rightReached : afterRight ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) playersRight
        (prefixRight.length + 1) beforeRight).support) :
    ∃ middleLeft middleRight : (phaseApplication runtime leaks).Execution,
      middleLeft ∈ ((phaseApplication runtime leaks).runRounds
        (family runtime leaks packetBudget tape) playersLeft prefixLeft.length beforeLeft).support ∧
      middleRight ∈ ((phaseApplication runtime leaks).runRounds
        (family runtime leaks packetBudget tape) playersRight
          prefixRight.length beforeRight).support ∧
      ∃ accepted : Bool,
        (message.id, accepted) ∈ afterLeft.receipts ∧
        (message.id, accepted) ∈ afterRight.receipts ∧
        (accepted = true → ∃ first second : State graph,
          handle runtime middleLeft.application.current.native
            ⟨message.id, .commitment event candidate⟩ = some first ∧
          handle runtime middleRight.application.current.native
            ⟨message.id, .commitment event candidate⟩ = some second ∧
          afterLeft.application = ({ middleLeft.application with
            current := ⟨first, middleLeft.application.current.excluded⟩ } :
              PhaseRuntimeState graph).normalize ∧
          afterRight.application = ({ middleRight.application with
            current := ⟨second, middleRight.application.current.excluded⟩ } :
              PhaseRuntimeState graph).normalize ∧
          BindingFrame program owner first second) := by
  rw [(phaseApplication runtime leaks).runRounds_add
    (family runtime leaks packetBudget tape) playersLeft prefixLeft.length 1 beforeLeft]
    at leftReached
  rw [(phaseApplication runtime leaks).runRounds_add
    (family runtime leaks packetBudget tape) playersRight prefixRight.length 1 beforeRight]
    at rightReached
  obtain ⟨middleLeft, leftPrefix, leftLast⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ leftReached)
  obtain ⟨middleRight, rightPrefix, rightLast⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rightReached)
  have paired := processing_owned_receipt_congr program runtime leaks packetBudget tape
    playersLeft playersRight cycle leftSlot rightSlot beforeLeft beforeRight middleLeft middleRight
    prefixLeft prefixRight restLeft restRight message leftCursor rightCursor
    leftRoom rightRoom epoch
    leftPending rightPending phase leftInstalled rightInstalled commitment inputs
    leftValid rightValid
    owner coordinate leftRequest rightRequest frame phases excluded leftForeign rightForeign
    event candidate sender binding leftPrefix rightPrefix
  have leftLength := (phaseApplication runtime leaks).runRounds_environmentRecall_length
    (family runtime leaks packetBudget tape) playersLeft prefixLeft.length _ _ leftPrefix
  have rightLength := (phaseApplication runtime leaks).runRounds_environmentRecall_length
    (family runtime leaks packetBudget tape) playersRight prefixRight.length _ _ rightPrefix
  have leftExecution := processing_step_execution program runtime leaks packetBudget tape
    playersLeft
    cycle (leftSlot + prefixLeft.length) middleLeft afterLeft message restLeft
    (by rw [leftLength, leftCursor]; omega) (by omega) epoch paired.1 leftLast
  have rightExecution := processing_step_execution program runtime leaks packetBudget tape
    playersRight
    cycle (rightSlot + prefixRight.length) middleRight afterRight message restRight
    (by rw [rightLength, rightCursor]; omega) (by omega) epoch paired.2.1 rightLast
  have leftReceipt := (include_head runtime leaks middleLeft message restLeft paired.1).2.2
  have rightReceipt := (include_head runtime leaks middleRight message restRight paired.2.1).2.2
  refine ⟨middleLeft, middleRight, leftPrefix, rightPrefix,
    (middleLeft.application.handle runtime message).isSome, ?_, ?_, ?_⟩
  · rw [leftExecution]
    change (message.id, _) ∈ (middleLeft.includePending (phaseApplication runtime leaks)
      message.id).receipts
    rw [leftReceipt]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [rightExecution, paired.2.2.1]
    change (message.id, _) ∈ (middleRight.includePending (phaseApplication runtime leaks)
      message.id).receipts
    rw [rightReceipt]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro accepted
    cases handled : middleLeft.application.handle runtime message with
    | none => simp only [handled, Option.isSome_none, Bool.false_eq_true] at accepted
    | some next =>
        obtain ⟨first, second, firstStep, secondStep, normalized, counterpart, retained⟩ :=
          phase_binding_handler_counterpart program runtime middleLeft.application
            middleRight.application next owner message event candidate paired.2.2.2.1
              paired.2.2.2.2.1 paired.2.2.2.2.2.1 paired.2.2.2.2.2.2 sender binding handled
        have leftFound : middleLeft.network.lookup message.id = some message := by
          simp [MessageNetwork.lookup, paired.1]
        have rightFound : middleRight.network.lookup message.id = some message := by
          simp [MessageNetwork.lookup, paired.2.1]
        refine ⟨first, second, firstStep, secondStep, ?_, ?_, retained⟩
        · rw [leftExecution]
          change (middleLeft.includePending (phaseApplication runtime leaks)
            message.id).application = _
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            leftFound]
          change (middleLeft.application.handle runtime message).getD middleLeft.application = _
          rw [handled, Option.getD_some]
          exact normalized
        · rw [rightExecution]
          change (middleRight.includePending (phaseApplication runtime leaks)
            message.id).application = _
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            rightFound]
          change (middleRight.application.handle runtime message).getD middleRight.application = _
          rw [counterpart, Option.getD_some]

end Vegas.EventGraphRuntime.ReservedEpoch

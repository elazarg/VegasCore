/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochProcessingProjection
import Vegas.Pending.ReservedEpochBatchApplication
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Interaction.ReactivePolicyInvariant

/-! # Actual processing prefixes and original images at their first attempt exit -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

/-- A marked FIFO prefix preserving its actual namespace stutters on a
surviving foreign owner's cone, whether that owner's chain is live or done. -/
theorem processing_original_prefix_frame (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (players : Player → (phaseApplication runtime leaks).Policy) (cycle slot : Nat)
    (packets untouched : List (Message Player (CommitAttemptPacket graph)))
    (before after : (phaseApplication runtime leaks).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth («graph» := graph) packetBudget + slot)
    (room : slot + packets.length ≤ packetBudget) (epoch : tape.processes cycle = true)
    (pending : before.network.pending = packets ++ untouched)
    (phase : RuntimePhase graph) (installed : phase ∈ before.application.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (valid : before.application.Invariant inputs) (ordered : before.application.Ordered)
    (owner : Player) (active : owner ∉ before.application.current.excluded)
    (other : ∀ message ∈ packets,
      message.sender ≠ owner ∨ message.payload.attempt ≠ before.application.attempt)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) players packets.length before).support)
    (same : after.application.attempt = before.application.attempt) :
    after.network.pending = untouched ∧
      BindingFrame program owner before.application.current.native
        after.application.current.native ∧
      after.application.phases = before.application.phases ∧
      after.application.generation = before.application.generation ∧
      after.application.current.excluded = before.application.current.excluded := by
  have actual := processing_prefix_application runtime leaks packetBudget tape players cycle slot
    packets untouched before after cursor room epoch pending reached
  change after.network.pending = untouched ∧ after.application = packets.foldl
    (fun state message => (state.handle runtime message).getD state) before.application at actual
  have retained := same_attempt_foreign_batch program runtime leaks packets before.application
    phase installed commitment inputs valid ordered owner active other (by
      have comparison := congrArg (fun state : PhaseRuntimeState graph => state.attempt) actual.2
      exact comparison.symm.trans same)
  refine ⟨actual.1, ?_⟩
  exact actual.2.symm ▸ retained

/-- At the first namespace-changing inclusion of a foreign backlog segment,
retain the exact original completed native image. The post-reset live store
is deliberately not used as that old attempt's result. -/
theorem processing_foreign_exit_snapshot (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (players : Player → (phaseApplication runtime leaks).Policy) (cycle slot : Nat)
    (packets : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (untouched : List (Message Player (CommitAttemptPacket graph)))
    (before after : (phaseApplication runtime leaks).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth («graph» := graph) packetBudget + slot)
    (room : slot + packets.length + 1 ≤ packetBudget) (epoch : tape.processes cycle = true)
    (pending : before.network.pending = packets ++ message :: untouched)
    (phase : RuntimePhase graph) (installed : phase ∈ before.application.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (valid : before.application.Invariant inputs) (ordered : before.application.Ordered)
    (owner : Player) (active : owner ∉ before.application.current.excluded)
    (other : ∀ packet ∈ packets ++ [message],
      packet.sender ≠ owner ∨ packet.payload.attempt ≠ before.application.attempt)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) players (packets.length + 1) before).support)
    (stayed : ∀ middle ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) players packets.length before).support,
      middle.application.attempt = before.application.attempt)
    (closed : after.application.attempt ≠ before.application.attempt) :
    ∃ middle : (phaseApplication runtime leaks).Execution,
      middle ∈ ((phaseApplication runtime leaks).runRounds
        (family runtime leaks packetBudget tape) players packets.length before).support ∧
      middle.application.attempt = before.application.attempt ∧
      ∃ (event : (graph).EventId) (candidate : Handle graph) (native : State graph),
        message.payload.packet.call = .commitment event candidate ∧
        handle runtime middle.application.current.native
          ⟨message.id, .commitment event candidate⟩ = some native ∧
        after.application = ({ middle.application with
          current := ⟨native, middle.application.current.excluded⟩ } :
            PhaseRuntimeState graph).normalize ∧
        phase.Finished (phase.drain ⟨native, middle.application.current.excluded⟩) ∧
        BindingFrame program owner before.application.current.native
          (phase.drain ⟨native, middle.application.current.excluded⟩).native := by
  rw [(phaseApplication runtime leaks).runRounds_add
    (family runtime leaks packetBudget tape) players packets.length 1 before] at reached
  obtain ⟨middle, prefixReached, lastReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have middleSame := stayed middle prefixReached
  have prefixFrame := processing_original_prefix_frame program runtime leaks packetBudget tape
    players cycle slot packets (message :: untouched) before middle cursor (by omega) epoch pending
      phase installed commitment inputs valid ordered owner active
      (fun packet member => other packet (List.mem_append_left _ member)) prefixReached middleSame
  have middleLength := (phaseApplication runtime leaks).runRounds_environmentRecall_length
    (family runtime leaks packetBudget tape) players packets.length before middle prefixReached
  have last := processing_prefix_application runtime leaks packetBudget tape players cycle
    (slot + packets.length) [message] untouched middle after
      (by rw [middleLength, cursor]; omega) (by simp only [List.length_singleton]; omega)
      epoch (by simpa only [List.singleton_append] using prefixFrame.1)
      (by simpa only [List.length_singleton] using lastReached)
  have applicationStep : after.application =
      ((phaseApplication runtime leaks).handle middle.application message).getD
        middle.application := by
    simpa only [List.foldl_cons, List.foldl_nil] using last.2
  change after.application = (middle.application.handle runtime message).getD middle.application
    at applicationStep
  have validFuture := ReactiveApplication.Invariant.policyInvariant
    (phaseApplication runtime leaks) (phaseApplication_invariant runtime leaks inputs) players
  have middleValid := validFuture.runRounds (family runtime leaks packetBudget tape) packets.length
    before middle valid prefixReached
  have middleInstalled : phase ∈ middle.application.phases.head? := by
    simpa only [prefixFrame.2.2.1] using installed
  have middleActive : owner ∉ middle.application.current.excluded := by
    simpa only [prefixFrame.2.2.2.2] using active
  cases handled : middle.application.handle runtime message with
  | none =>
      rw [handled, Option.getD_none] at applicationStep
      apply (closed ?_).elim
      rw [applicationStep]
      exact middleSame
  | some next =>
      rw [handled, Option.getD_some] at applicationStep
      subst next
      have different : message.sender ≠ owner := by
        rcases other message (List.mem_append_right _ (List.mem_singleton_self _)) with
          different | stale
        · exact different
        · have rejected := middle.application.handle_retired runtime message
            (by simpa only [middleSame] using stale)
          rw [rejected] at handled
          cases handled
      obtain ⟨event, candidate, native, call, nativeStep, actual, _nativeFrame, retained⟩ :=
        binding_processing_snapshot program runtime middle.application after.application phase
          middleInstalled commitment inputs middleValid owner middleActive message handled
      have finished := PhaseRuntimeState.finished_of_normalize_attempt_ne
        ({ middle.application with current := ⟨native, middle.application.current.excluded⟩ } :
          PhaseRuntimeState graph) phase middleInstalled (by
            change ({ middle.application with
              current := ⟨native, middle.application.current.excluded⟩ } :
                PhaseRuntimeState graph).normalize.attempt ≠ middle.application.attempt
            rw [← actual]
            exact fun same => closed (same.trans middleSame))
      exact ⟨middle, prefixReached, middleSame, event, candidate, native, call, nativeStep,
        actual, finished, prefixFrame.2.1.trans (retained different)⟩

end Vegas.EventGraphRuntime.ReservedEpoch

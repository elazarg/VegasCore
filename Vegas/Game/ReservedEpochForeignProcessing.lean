/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochBatchApplication
import Vegas.Game.ReservedEpochPhaseBindingFrame
import Vegas.Pending.PhaseBindingCountedIncludeMemory
import Vegas.Pending.PhaseSeedPhysicalIsolation
import Vegas.Pending.PhaseExclusionOrigin

/-! # Actual foreign processing prefixes preserve a live binding chain -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem foreign_processing_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (packets : List (Message Player (CommitAttemptPacket graph))) (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (installed : phase ∈ state.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (valid : state.Invariant inputs) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : state.SeedRequest owner coordinate)
    (foreign : ∀ message ∈ packets,
      message.sender ≠ owner ∨ message.payload.attempt ≠ coordinate.attempt) :
    let next := packets.foldl (fun state message => (state.handle runtime message).getD state) state
    next.Invariant inputs ∧ BindingFrame program owner state.current.native next.current.native ∧
      next.SeedRequest owner coordinate ∧ next.phases = state.phases ∧
      next.current.excluded = state.current.excluded := by
  induction packets generalizing state with
  | nil => exact ⟨valid, BindingFrame.refl owner state.current.native, requested, rfl, rfl⟩
  | cons message rest ih =>
      have other := foreign message (List.mem_cons_self ..)
      have tail : ∀ packet ∈ rest,
          packet.sender ≠ owner ∨ packet.payload.attempt ≠ coordinate.attempt :=
        fun packet member => foreign packet (List.mem_cons_of_mem _ member)
      cases handled : state.handle runtime message with
      | none =>
          simpa only [List.foldl_cons, handled, Option.getD_none] using
            ih state installed valid requested tail
      | some next =>
          have other : message.sender ≠ owner := by
            rcases other with different | stale
            · exact different
            · have rejected := state.handle_retired runtime message
                (by simpa only [requested.1] using stale)
              rw [rejected] at handled
              cases handled
          have opaquePhase : ∀ actual ∈ state.phases.head?, actual.kind = .commitment := by
            intro actual actualInstalled
            have same : actual = phase := Option.some.inj
              ((Option.mem_def.mp actualInstalled).symm.trans (Option.mem_def.mp installed))
            simpa only [same] using commitment
          obtain ⟨event, candidate, call⟩ := BindingShadow.accepted_call_in_commitment runtime
            state next opaquePhase message handled
          obtain ⟨frame, phases⟩ := phase_foreign_binding_frame program runtime state next phase
            installed commitment inputs valid.active owner coordinate requested message event
              candidate other call handled
          have nextValid : next.Invariant inputs :=
            (phaseApplication_invariant runtime leaks inputs).handle
              state message next valid handled
          have nextRequest := state.handle_foreign_request runtime next valid message handled owner
            coordinate requested other.symm
          have exclusions := state.handle_commitment_phase_excluded runtime next phase installed
            commitment message handled
          have nextInstalled : phase ∈ next.phases.head? := by
            simpa only [phases] using installed
          have after := ih next nextInstalled nextValid nextRequest tail
          simpa only [List.foldl_cons, handled, Option.getD_some] using
            And.intro after.1 ⟨frame.trans after.2.1, after.2.2.1,
              after.2.2.2.1.trans phases, after.2.2.2.2.trans exclusions⟩

theorem foreign_processing_prefix_frame [Fintype Player]
    (runtime : EventGraphRuntime graph)
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
    (valid : before.application.Invariant inputs) (owner : Player)
    (coordinate : CommitAttemptEvent graph)
    (requested : before.application.SeedRequest owner coordinate)
    (foreign : ∀ message ∈ packets,
      message.sender ≠ owner ∨ message.payload.attempt ≠ coordinate.attempt)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks packetBudget tape) players packets.length before).support) :
    BindingFrame program owner before.application.current.native after.application.current.native ∧
      after.application.SeedRequest owner coordinate ∧
      after.application.phases = before.application.phases ∧
      after.application.current.excluded = before.application.current.excluded := by
  have physical := processing_prefix_application runtime leaks packetBudget tape players cycle slot
    packets untouched before after cursor room epoch pending reached
  have paired := foreign_processing_application program runtime leaks packets before.application
    phase installed commitment inputs valid owner coordinate requested foreign
  change after.network.pending = untouched ∧ after.application = packets.foldl
    (fun state message => (state.handle runtime message).getD state) before.application at physical
  rw [physical.2]
  exact paired.2

end Vegas.EventGraphRuntime.ReservedEpoch

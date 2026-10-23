/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReadback
import Vegas.Pending.PhaseProposalRetention
import Vegas.Source.ProposalRecoveryDisclosure
import Vegas.Game.PhaseProposalAddress
import Vegas.Game.PhaseProposalSourceArchive
import Vegas.Source.ProposalRecoveryRank

/-! # Exact typed proposal deltas in native source replay -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Derived native prestate readback supplies the entire source proposal
delta, including the literal phase and generation. Disclosure labels alone
never choose its type, value or address. -/
theorem source_proposal_delta_of_readback
    (setup : Setup (Player := Player) (L := L))
    {graph : Vegas.EventGraph Player L} (native : EventGraphRuntime.State graph)
    (state : CommitRecoveryState setup.program)
    (readback : NativeProposalReadback native 0 setup.program state.point)
    (owner : Player) (acting : ProtocolState.actor setup.program state.point = some owner)
    (notCommit : ProtocolState.atCommit setup.program state.point = false)
    (surviving : owner ∉ state.excluded)
    (coordinate : CommitAttemptEvent graph) (payload : L.Ty) (value : L.Val payload)
    (ranked : coordinate.event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program state.point)
    (phase : setup.program.publicationBlockLow coordinate.event.val = coordinate.attempt.phase)
    (generation : state.generation = coordinate.attempt.generation)
    (stored : nativeStoredProposal? native coordinate.event.val = some ⟨payload, value⟩)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (disclosed : ((joint owner).map (·.discloses)).getD false = true) :
    setup.proposalRecoveryProposalOf (some state) joint =
      some ⟨EventGraphRuntime.PhaseProposal.sourceAddress coordinate, payload, value⟩ := by
  let masked := fun who => if who ∈ state.excluded then none else joint who
  have actual := readback masked
  simp only [nativeRecoveryProposal?, notCommit, Bool.false_eq_true, ite_false,
    acting, Option.bind_some, masked, surviving, ite_false, disclosed, ite_true,
    Nat.zero_add, ← ranked, stored] at actual
  obtain ⟨pair, original, sameValue⟩ := Option.map_eq_some_iff.mp actual
  have rankEq := ProtocolState.recoveryProposal_rank setup.program state.point masked
    pair.1 pair.2 original
  have paired : pair = (coordinate.event.val, ⟨payload, value⟩) :=
    Prod.ext (rankEq.trans ranked.symm) sameValue
  rw [paired] at original
  simp only [Setup.proposalRecoveryProposalOf, Option.bind_some, original,
    Option.map_some, phase, generation, EventGraphRuntime.PhaseProposal.sourceAddress]

namespace EventGraphRuntime.PhaseProposal

variable [Fintype Player] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The proposal's exact value is still readable at any semantic extension
of its actual publication-attempt prefix, including the completed phase image
used by the compiler's source-order replay. -/
theorem submitted_proposal_replay_value
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw))
    (sameAttempt : coordinate.attempt = current.execution.application.attempt)
    (image : EventGraphRuntime.State graph)
    (kept : KeepsStore current.execution.application.current.native image) :
    nativeStoredProposal? image coordinate.event.val = some ⟨raw.ty, raw.value⟩ := by
  obtain ⟨before, prior, owner, payload, binding, checks, outputEq, codeEq, value,
    _retained, _sender, _acting, _request, _node, _typed, _stored⟩ :=
    submitted_proposal_binding_meaning runtime leaks bounds plan ordered inputs horizon scheduler
      current trace message submitted coordinate raw proposed
  obtain ⟨actual, typed, stored⟩ := submitted_proposal_current_binding_meaning runtime leaks bounds
    plan ordered inputs horizon scheduler current trace message submitted coordinate raw proposed
      sameAttempt owner payload binding checks outputEq codeEq
  have imageStored := kept_reference kept binding (.success actual) stored
  have readback := nativeStoredProposal?_resolve image coordinate.event binding checks outputEq
    codeEq (.success actual) imageStored
  rw [typed]
  exact readback

end EventGraphRuntime.PhaseProposal

end Vegas

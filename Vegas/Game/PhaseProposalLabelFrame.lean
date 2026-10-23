/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLabels

/-! # Current emissions preserve consumed proposal labels -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The label of an earlier source coordinate depends only on strictly earlier
proposal buckets. An emission in the current physical phase cannot alter it. -/
theorem nativeArchiveLabels_eq_of_earlier
    (setup : Setup (Player := Player) (L := L))
    (first second : Finset (ProposalRecoveryProposal L)) (cutoff : Nat)
    (same : first.filter (fun proposal => proposal.address.phase < cutoff) =
      second.filter (fun proposal => proposal.address.phase < cutoff))
    (event : setup.commitRecoveryProtocol.StepEvent) (owner : Player)
    (state : CommitRecoveryState setup.program) (source : event.source = some state)
    (earlier : setup.program.publicationBlockLow (instructionCount setup.program -
      ProtocolState.remaining setup.program state.point) < cutoff) :
    nativeArchiveLabels setup first event owner = nativeArchiveLabels setup second event owner := by
  apply Bool.eq_iff_iff.mpr
  rw [nativeArchiveLabels_some setup first event owner state source,
    nativeArchiveLabels_some setup second event owner state source]
  constructor
  · rintro ⟨proposal, present, address⟩
    have bounded : proposal.address.phase < cutoff := by
      rw [address]
      exact earlier
    have retained : proposal ∈ second.filter (fun item => item.address.phase < cutoff) :=
      same ▸ Finset.mem_filter.mpr ⟨present, bounded⟩
    exact ⟨proposal, (Finset.mem_filter.mp retained).1, address⟩
  · rintro ⟨proposal, present, address⟩
    have bounded : proposal.address.phase < cutoff := by
      rw [address]
      exact earlier
    have retained : proposal ∈ first.filter (fun item => item.address.phase < cutoff) :=
      same.symm ▸ Finset.mem_filter.mpr ⟨present, bounded⟩
    exact ⟨proposal, (Finset.mem_filter.mp retained).1, address⟩

namespace EventGraphRuntime.PhaseProposal

variable {graph : Vegas.EventGraph Player L}

/-- This is a physical timestamp fact, not a claim about truthful content or
admission. Even a malformed, rejected or stale opening emitted now cannot add
an entry to a strictly earlier physical-phase bucket. -/
theorem sourceArchive_before_append
    (messages : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph)) (cutoff : Nat)
    (phase : message.payload.attempt.phase = cutoff) :
    (sourceArchive (messages ++ [message])).filter (fun proposal => proposal.address.phase <
      cutoff) =
      (sourceArchive messages).filter (fun proposal => proposal.address.phase < cutoff) := by
  apply Finset.ext
  intro proposal
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨present, earlier⟩
    obtain ⟨raw, submitted, decoded⟩ := (mem_sourceArchive _ _).mp present
    obtain ⟨envelope, included, proposed⟩ := (mem_archive _ _).mp submitted
    rcases List.mem_append.mp included with old | recent
    · exact ⟨(mem_sourceArchive _ _).mpr ⟨raw,
        (mem_archive _ _).mpr ⟨envelope, old, proposed⟩, decoded⟩, earlier⟩
    · have same := List.mem_singleton.mp recent
      subst envelope
      obtain ⟨attempt, _candidate, _call⟩ := opening_of_packetProposal message.payload raw.1 raw.2
        proposed
      have address := sourceProposal?_address raw proposal decoded
      have equal : proposal.address.phase = cutoff :=
        (congrArg ProposalRecoveryAddress.phase address).trans
          ((congrArg CommitAttemptId.phase attempt).symm.trans phase)
      omega
  · rintro ⟨present, earlier⟩
    obtain ⟨raw, submitted, decoded⟩ := (mem_sourceArchive _ _).mp present
    obtain ⟨envelope, included, proposed⟩ := (mem_archive _ _).mp submitted
    exact ⟨(mem_sourceArchive _ _).mpr ⟨raw, (mem_archive _ _).mpr
      ⟨envelope, List.mem_append_left _ included, proposed⟩, decoded⟩, earlier⟩

/-- A real response attaches the current application attempt regardless of
its packet syntax. Therefore earlier canonical proposal buckets are unchanged. -/
theorem sourceArchive_respond_before (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) (owner : Player)
    (response : (phaseApplication runtime leaks).Action) :
    Finset.filter (fun proposal => proposal.address.phase < execution.application.attempt.phase)
        (sourceArchive
          (execution.respond (phaseApplication runtime leaks) owner response).network.inputs) =
      (sourceArchive execution.network.inputs).filter
        (fun proposal => proposal.address.phase < execution.application.attempt.phase) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      let app := phaseApplication runtime leaks
      let next := execution.application.submit owner material
      let packet := app.packet next owner (execution.network.known owner) material
      let message : Message Player app.Payload :=
        ⟨(owner, execution.network.nextSerial owner), packet⟩
      change (sourceArchive (execution.network.inputs ++ [message])).filter _ = _
      apply sourceArchive_before_append execution.network.inputs message
        execution.application.attempt.phase
      rfl

end EventGraphRuntime.PhaseProposal
end Vegas

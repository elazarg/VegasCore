/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReplay
import Vegas.Pending.PhaseProposalTyping

/-! # Current-namespace archive entries retain the replayed binding value -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- This readback uses an actual counted archive member and its literal
current address; no publication acceptance or sender survival is assumed. -/
theorem archived_proposal_image_value
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (proposal : ProposalRecoveryProposal L)
    (member : proposal ∈ sourceArchive current.execution.network.inputs)
    (event : graph.EventId)
    (address : proposal.address = sourceAddress ⟨current.execution.application.attempt, event⟩)
    (image : EventGraphRuntime.State graph)
    (kept : KeepsStore current.execution.application.current.native image) :
    nativeStoredProposal? image event.val = some ⟨proposal.payload, proposal.value⟩ := by
  obtain ⟨rawProposal, archived, decoded⟩ := (mem_sourceArchive _ _).mp member
  have coordinate := sourceAddress_injective
    ((sourceProposal?_address rawProposal proposal decoded).symm.trans address)
  rcases rawProposal with ⟨coordinate', raw⟩
  change coordinate' = ⟨current.execution.application.attempt, event⟩ at coordinate
  subst coordinate'
  obtain ⟨message, submitted, proposed⟩ := (mem_archive _ _).mp archived
  have read := submitted_proposal_replay_value runtime leaks bounds plan ordered inputs horizon
    scheduler current trace message submitted _ raw proposed rfl image kept
  obtain ⟨payload, value, publication, typed⟩ := archive_publication_typed runtime leaks bounds
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler current trace _ raw archived
  have canonical := sourceProposal?_publication
    ⟨current.execution.application.attempt, event⟩ payload publication value
  rw [typed, canonical] at decoded
  have same := Option.some.inj decoded
  subst proposal
  rw [typed] at read
  exact read

end Vegas.EventGraphRuntime.PhaseProposal

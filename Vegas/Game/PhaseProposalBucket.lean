/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalPublicationImage

/-! # Only an installed publication phase can have a current proposal bucket -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] [Fintype Player] in
private theorem decoded_proposal_publication
    (raw : Proposal graph) (proposal : ProposalRecoveryProposal L)
    (decoded : sourceProposal? raw = some proposal) :
    ∃ payload, graph.outputLayout raw.1.event = .publication payload := by
  cases output : graph.outputLayout raw.1.event with
  | publication payload => exact ⟨payload, rfl⟩
  | binding | privateInput | publicData =>
      simp only [sourceProposal?, output] at decoded
      cases decoded

/-- No publication packet can be retroactively attributed to an installed
commitment or sampling interval. Its typed archive address has actual counted
emission provenance, rather than a sender-supplied static phase tag. -/
theorem sourceArchive_nonpublication_bucket_empty
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (kind : phase.kind ≠ .reveal) :
    (sourceArchive current.execution.network.inputs).filter
      (fun proposal => proposal.address.phase = current.execution.application.attempt.phase) =
      ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro proposal member
  obtain ⟨archived, samePhase⟩ := Finset.mem_filter.mp member
  obtain ⟨event, inside, address⟩ := archived_proposal_in_installed_phase runtime leaks bounds plan
    ordered inputs horizon scheduler current trace phase installed proposal archived samePhase
  obtain ⟨raw, _archived, decoded⟩ := (mem_sourceArchive _ _).mp archived
  have same := sourceAddress_injective
    ((sourceProposal?_address raw proposal decoded).symm.trans address)
  obtain ⟨payload, output⟩ := decoded_proposal_publication raw proposal decoded
  rw [same] at output
  have interval := (phase.mem_events event).mp inside
  have field := phase.fields event interval.1 interval.2
  cases phaseKind : phase.kind with
  | commitment =>
      simp only [phaseKind, RuntimePhaseKind.Matches, output] at field
      obtain ⟨owner, actual, impossible⟩ := field
      cases impossible
  | reveal => exact (kind phaseKind).elim
  | sample =>
      simp only [phaseKind, RuntimePhaseKind.Matches, output] at field
      obtain ⟨actual, impossible⟩ := field
      cases impossible

end Vegas.EventGraphRuntime.PhaseProposal

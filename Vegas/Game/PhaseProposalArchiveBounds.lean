/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceArchive
import Vegas.Pending.PhaseInputNamespace

/-! # Submitted proposal buckets cannot belong to a future physical phase -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem sourceArchive_phase_le
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some current))
    (proposal : SourceProgram.ProposalRecoveryProposal L)
    (member : proposal ∈ sourceArchive current.execution.network.inputs) :
    proposal.address.phase ≤ current.execution.application.attempt.phase := by
  obtain ⟨rawProposal, archived, decoded⟩ := (mem_sourceArchive _ _).mp member
  obtain ⟨message, submitted, proposed⟩ := (mem_archive _ _).mp archived
  obtain ⟨attempt, _candidate, _call⟩ := opening_of_packetProposal message.payload rawProposal.1
    rawProposal.2 proposed
  have address := sourceProposal?_address rawProposal proposal decoded
  have namespaces := inputNamespaces_history runtime leaks
    (inputs.map (PhaseRuntimeState.initial plan)) (by
      intro state supported
      obtain ⟨input, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input) horizon scheduler trace
  calc
    proposal.address.phase = rawProposal.1.attempt.phase :=
      congrArg SourceProgram.ProposalRecoveryAddress.phase address
    _ = message.payload.attempt.phase := (congrArg CommitAttemptId.phase attempt).symm
    _ ≤ current.execution.application.attempt.phase := (namespaces.bounded message submitted).2

/-- This also covers phases consumed automatically inside one environment
step: no participant could have submitted a counted opening for them yet. -/
theorem sourceArchive_future_bucket_empty
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some current)) (phase : Nat)
    (future : current.execution.application.attempt.phase < phase) :
    (sourceArchive current.execution.network.inputs).filter
      (fun proposal => proposal.address.phase = phase) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro proposal member
  obtain ⟨archived, exactPhase⟩ := Finset.mem_filter.mp member
  have bound := sourceArchive_phase_le runtime leaks plan inputs horizon scheduler current trace
    proposal archived
  omega

end Vegas.EventGraphRuntime.PhaseProposal

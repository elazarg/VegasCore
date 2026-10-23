/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalNormalization
import Vegas.Game.PhaseProposalBucket
import Vegas.Game.PhaseProposalArchiveBounds

/-! # Consumed proposal archives carried by actual source checkpoints -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace RecoverySourceCheckpoint

/-- The checkpoint contains exactly the already consumed physical proposal
buckets. Proposals in a live publication interval are retained by the execution
and enter this equality only when that interval is consumed. -/
def ArchivedProposals
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (messages : List (Message Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))) : Prop :=
  ∀ who, who ∉ state.current.excluded →
    let archive := PhaseProposal.sourceArchive messages
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who
          (setup.proposalRecoveryLiftTrace (nativeArchiveLabels setup archive) checkpoint.trace)) =
      archive.filter (fun proposal => proposal.address.phase < state.attempt.phase)

/-- The increment derived by the actual normalizer extends an accumulated
archive invariant on that SAME selected source checkpoint. The external input
list is fixed throughout one native normalization. -/
theorem ArchivedProposals.normalize
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode state.normalize)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some anchor))
    (frame : PhaseProposal.NormalizationFrame runtime leaks anchor state)
    (ordered : state.Ordered)
    (prior : checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (delta : checkpoint.ProposalDelta plan next) :
    next.ArchivedProposals anchor.execution.network.inputs := by
  intro who active
  let archive := PhaseProposal.sourceArchive anchor.execution.network.inputs
  have survives : who ∉ state.current.excluded := by
    have excluded := (PhaseRuntimeState.settle_physical state.phases state.generation state.entry
      state.current state.retired).1
    simpa only [PhaseRuntimeState.normalize, excluded] using active
  have old := prior who survives
  have step := delta runtime leaks bounds inputs horizon scheduler anchor trace frame who
  dsimp only at old step ⊢
  rw [step, old]
  have monotone := (PhaseRuntimeState.settle_namespace state.phases state.generation state.entry
    state.current state.retired ordered).2
  apply Finset.ext
  intro proposal
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨present, lower⟩ | ⟨present, _lower, upper⟩)
    · exact ⟨present, lt_of_lt_of_le lower monotone⟩
    · exact ⟨present, upper⟩
  · rintro ⟨present, upper⟩
    by_cases earlier : proposal.address.phase < state.attempt.phase
    · exact Or.inl ⟨present, earlier⟩
    · exact Or.inr ⟨present, Nat.le_of_not_gt earlier, upper⟩

/-- At a commitment decision every submitted typed proposal belongs to an
already consumed interval. This turns the accumulated invariant into the full
canonical archive readout needed by the enriched source information map. -/
theorem ArchivedProposals.binding
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (checkpoint : RecoverySourceCheckpoint setup mode current.execution.application)
    (prior : checkpoint.ArchivedProposals current.execution.network.inputs)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (installed : current.execution.application.phases.head? = some phase)
    (kind : phase.kind = .commitment) (who : Player)
    (active : who ∉ current.execution.application.current.excluded) :
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who
          (setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive current.execution.network.inputs))
            checkpoint.trace)) = PhaseProposal.sourceArchive current.execution.network.inputs := by
  rw [prior who active]
  apply Finset.filter_eq_self.mpr
  intro proposal present
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have bounded := PhaseProposal.sourceArchive_phase_le runtime leaks plan inputs horizon scheduler
    current rawTrace proposal present
  have noCurrent := PhaseProposal.sourceArchive_nonpublication_bucket_empty runtime leaks bounds
    plan
    ((toEventGraph setup.program).withMode_revealRelaxedOrdered
      (toEventGraph_barrierOrdered setup.program) mode) inputs horizon scheduler current trace phase
    installed (by simp only [kind]; decide)
  by_contra notBefore
  have equal : proposal.address.phase = current.execution.application.attempt.phase := by omega
  have included : proposal ∈ (PhaseProposal.sourceArchive current.execution.network.inputs).filter
      (fun proposed => proposed.address.phase = current.execution.application.attempt.phase) :=
    Finset.mem_filter.mpr ⟨present, equal⟩
  rw [noCurrent] at included
  exact Finset.notMem_empty proposal included

end RecoverySourceCheckpoint
end Vegas

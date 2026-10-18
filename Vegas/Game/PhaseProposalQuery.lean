/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceArchive
import Vegas.Game.PhaseObservableSourceQuery

/-! # Observable source queries with the complete typed proposal archive

The actual local query retains the existing normalized failure/address controls
and adjoins the archive reconstructed from own recall and complete packet
observation. Its source component uses the owning all-raw genuine-query theorem.
This readout does not assert any equality of conditional beliefs.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The source control query and canonical proposals are both functions of the
actual ordinary decision input; neither reads the scheduler's private history. -/
def phaseProposalQuery? (setup : Setup (Player := Player) (L := L))
    (mode : ExecutionMode) (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    Option (setup.commitRecoveryModel.InfoState who × Finset (ProposalRecoveryProposal L)) :=
  (phaseVirtualSourceQuery? setup mode runtime leaks plan who event view).map fun source =>
    (source, PhaseProposal.observedSourceArchive runtime leaks past view)

/-- At every actual ready binding decision, the source component is genuine
and the archive is exactly the typed proposal set of the physical submitted
traffic, including failed and stale openings. The source witness is supplied by
the existing all-raw source query; no counterpart or posterior premise is used. -/
theorem phaseProposalQuery?_genuine_base
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (complete : leaks = MessageNetwork.completePendingObservation)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      ProtocolState.actor setup.program current.point = some who ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.point =
        event.val ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      phaseProposalQuery? setup mode runtime leaks plan who event
          (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) =
        some (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryNoMissInformation who
            (setup.commitRecoveryModel.infoOf who sourceTrace)),
          PhaseProposal.sourceArchive control.execution.network.inputs) := by
  obtain ⟨current, sourceTrace, actor, rank, decision, queried⟩ :=
    phaseVirtualSourceQuery?_genuine_of_ready_binding setup mode runtime leaks plan maximal
      horizon scheduler trace who event payload binding request
  refine ⟨current, sourceTrace, actor, rank, decision, ?_⟩
  simp only [phaseProposalQuery?, queried, Option.map_some]
  rw [PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete _ horizon scheduler
    control trace who active]

end Vegas

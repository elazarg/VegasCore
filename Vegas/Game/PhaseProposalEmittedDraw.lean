/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinaryDraw
import Vegas.Game.PhaseProposalUnflaggedBinding

/-! # Literal emitted binding draws on the chosen ordinary source replay -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual first binding response samples the table at the SAME chosen
ordinary source trace. Its typed preparation is retained before admission;
the source counterpart is not selected again after the packet is delivered. -/
theorem RecoverySourceWitness.ordinary_binding_preparation_law
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (complete : leaks = MessageNetwork.completePendingObservation)
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversOutputValues)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (witness : RecoverySourceWitness setup mode plan execution.application)
    (archived : witness.checkpoint.ArchivedProposals execution.network.inputs)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) :
    ∃ (original : CommitRecoveryState setup.program)
      (originalTrace : setup.commitRecoveryProtocol.Trace (some original)),
      let labels := nativeArchiveLabels setup (PhaseProposal.sourceArchive execution.network.inputs)
      let lifted := setup.proposalRecoveryLiftTrace labels originalTrace
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who lifted) =
        PhaseProposal.sourceArchive execution.network.inputs ∧
      (ProtocolState.BindingsHoldValues who setup.program original.point →
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
          (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).map
          (fun response => response.transmission.bind PhaseProposal.bindingPreparation) =
        (values who (setup.proposalRecoveryQuery who
          (setup.proposalRecoveryModel.infoOf who lifted))).map (fun choice =>
            some (⟨payload, phaseRecoveryDomainValue setup mode event who payload binding
              choice.val.val⟩ : Raw L))) := by
  obtain ⟨original, originalTrace, archive, draw⟩ :=
    RecoverySourceWitness.ordinary_binding_draw setup mode runtime leaks complete bounds plan
      maximal values horizon scheduler ⟨remaining, some who, execution⟩ trace witness archived who
        rfl event payload binding request
  refine ⟨original, originalTrace, archive, ?_⟩
  intro ordinary
  obtain ⟨key, queried, law⟩ := phaseProposalUnflaggedBinding_preparation_law setup mode runtime
    leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      remaining who execution trace event payload binding request unsent
  have same := Option.some.inj (queried.symm.trans (draw ordinary).1)
  cases same
  exact law

end Vegas

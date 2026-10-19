/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalPublicationImage
import Vegas.Game.PhaseProposalDisclosure
import Vegas.Game.PhaseProposalAddress

/-! # Actual replay disclosures produce canonical archived proposals -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open SourceProgram.Setup

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem proposal_discloses_of_semantic
    (joint : Player → Option (ProposalRecoveryMove Player L)) (owner : Player)
    (disclosed : OwnAction.disclosure
      (((proposalRecoveryJoint joint) owner).map (·.action)) = true) :
    ((joint owner).map (·.discloses)).getD false = true := by
  cases selected : joint owner with
  | none =>
      simp only [proposalRecoveryJoint, selected, Option.map_none,
        OwnAction.disclosure] at disclosed
      cases disclosed
  | some move =>
      simp only [proposalRecoveryJoint, selected, Option.map_some] at disclosed
      simp only [Option.map_some, Option.getD_some, ProposalRecoveryMove.discloses,
        disclosed, Bool.true_or]

/-- An ordinary true source disclosure in the reconstructed phase retains
the actual native message, full physical address and successful binding value.
The completed publication may itself have failed its guard. -/
theorem source_replay_disclosure_in_archive
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (ordered : ((toEventGraph setup.program).withMode mode).RevealRelaxedOrdered)
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (installed : current.execution.application.phases.head? = some phase)
    (kind : phase.kind = .reveal)
    (image : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (origins : PhaseProposal.OpeningOrigins current.execution.network.inputs image)
    (kept : KeepsStore current.execution.application.current.native image)
    (sourceState : CommitRecoveryState setup.program)
    (readback : NativeProposalReadback image 0 setup.program sourceState.point)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (disclosure : NativeDisclosureReadback image 0 setup.program sourceState.point
      sourceState.excluded (proposalRecoveryJoint joint))
    (owner : Player) (acting : ProtocolState.actor setup.program sourceState.point = some owner)
    (surviving : owner ∉ sourceState.excluded)
    (notCommit : ProtocolState.atCommit setup.program sourceState.point = false)
    (generation : sourceState.generation = current.execution.application.attempt.generation)
    (lower : phase.low ≤ instructionCount setup.program -
      ProtocolState.remaining setup.program sourceState.point)
    (upper : instructionCount setup.program -
      ProtocolState.remaining setup.program sourceState.point < phase.high)
    (disclosed : OwnAction.disclosure
      (((proposalRecoveryJoint joint) owner).map (·.action)) = true) :
    ∃ proposal : ProposalRecoveryProposal L,
      setup.proposalRecoveryProposalOf (some sourceState) joint = some proposal ∧
      proposal ∈ PhaseProposal.sourceArchive current.execution.network.inputs := by
  obtain ⟨event, payload, publication, action, ranked, recorded, selected⟩ :=
    disclosure owner acting surviving
  have selectedTrue := selected.trans disclosed
  simp only [Nat.zero_add] at ranked
  have inside : event ∈ phase.events := phase.mem_events event |>.mpr (by omega)
  obtain ⟨value, archived, stored⟩ :=
    PhaseProposal.publication_image_disclosure_typed_archive runtime leaks bounds plan ordered
      inputs horizon scheduler current trace phase installed image origins kept ⟨event, action⟩
      inside recorded payload publication selectedTrue
  let coordinate : CommitAttemptEvent ((toEventGraph setup.program).withMode mode) :=
    ⟨current.execution.application.attempt, event⟩
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
  have member := suffix.subset (List.mem_of_mem_head? installed)
  have low : current.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  have phaseAddress : setup.program.publicationBlockLow coordinate.event.val =
      coordinate.attempt.phase :=
    (publicationBlockLow_of_phase setup.program mode plan maximal phase member kind event
      inside).trans low.symm
  refine ⟨⟨PhaseProposal.sourceAddress coordinate, payload, value⟩, ?_, archived⟩
  exact source_proposal_delta_of_readback setup image sourceState readback owner acting notCommit
    surviving coordinate payload value ranked phaseAddress generation stored joint
    (proposal_discloses_of_semantic joint owner disclosed)

end Vegas

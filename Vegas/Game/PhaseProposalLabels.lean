/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReplay
import Vegas.Source.ProposalRecoveryLift
import Vegas.Source.ProposalRecoveryChronology

/-! # Replay labels determined by the actual canonical proposal archive -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The label reads only whether the actual submitted archive contains the
current source coordinate. It never supplies a plaintext or source state. -/
def nativeArchiveLabels (setup : Setup (Player := Player) (L := L))
    (archive : Finset (ProposalRecoveryProposal L))
    (event : setup.commitRecoveryProtocol.StepEvent) (_owner : Player) : Bool := by
  classical
  exact match event.source with
  | none => false
  | some state => decide (∃ proposal ∈ archive, proposal.address =
      ⟨setup.program.publicationBlockLow
          (instructionCount setup.program - ProtocolState.remaining setup.program state.point),
        state.generation,
        instructionCount setup.program - ProtocolState.remaining setup.program state.point⟩)

theorem nativeArchiveLabels_some (setup : Setup (Player := Player) (L := L))
    (archive : Finset (ProposalRecoveryProposal L))
    (event : setup.commitRecoveryProtocol.StepEvent) (owner : Player)
    (state : CommitRecoveryState setup.program) (source : event.source = some state) :
    nativeArchiveLabels setup archive event owner = true ↔
      ∃ proposal ∈ archive, proposal.address =
        ⟨setup.program.publicationBlockLow
            (instructionCount setup.program - ProtocolState.remaining setup.program state.point),
          state.generation,
          instructionCount setup.program - ProtocolState.remaining setup.program state.point⟩ := by
  simp only [nativeArchiveLabels, source, decide_eq_true_eq]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem label_requested_of_no_disclosure
    (move : CommitRecoveryMove Player L) (requested : Bool)
    (silent : OwnAction.disclosure (some move.action) = false)
    (exposed : (ProposalRecoveryMove.label move requested).discloses = true) :
    requested = true := by
  rcases move with ⟨action, missing⟩
  cases action with
  | commit => cases exposed
  | reveal _ _ disclose =>
      cases disclose with
      | false => exact exposed
      | true => cases silent

theorem liftJoint_requested_of_no_disclosure
    (setup : Setup (Player := Player) (L := L))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (event : setup.commitRecoveryProtocol.StepEvent) (owner : Player)
    (silent : OwnAction.disclosure ((event.joint owner).map (·.action)) = false)
    (exposed : (((setup.proposalRecoveryLiftJoint labels event) owner).map
      (·.discloses)).getD false = true) : labels event owner = true := by
  cases chosen : event.joint owner with
  | none =>
      simp only [Setup.proposalRecoveryLiftJoint, chosen, Option.map_none,
        Option.getD_none] at exposed
      cases exposed
  | some move =>
      simp only [Setup.proposalRecoveryLiftJoint, chosen, Option.map_some,
        Option.getD_some] at exposed
      simp only [chosen, Option.map_some] at silent
      exact label_requested_of_no_disclosure move _ silent exposed

/-- A successful enriched delta identifies an active, nonexcluded source
actor and the exact successful native binding read at that source rank. -/
theorem source_proposal_readback_origin
    (setup : Setup (Player := Player) (L := L))
    {graph : Vegas.EventGraph Player L} (native : EventGraphRuntime.State graph)
    (state : CommitRecoveryState setup.program)
    (readback : NativeProposalReadback native 0 setup.program state.point)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (proposal : ProposalRecoveryProposal L)
    (decoded : setup.proposalRecoveryProposalOf (some state) joint = some proposal) :
    ∃ owner,
      ProtocolState.actor setup.program state.point = some owner ∧
      ProtocolState.atCommit setup.program state.point = false ∧
      owner ∉ state.excluded ∧
      ((joint owner).map (·.discloses)).getD false = true ∧
      nativeStoredProposal? native proposal.address.event =
        some ⟨proposal.payload, proposal.value⟩ ∧
      proposal.address =
        ⟨setup.program.publicationBlockLow
            (instructionCount setup.program - ProtocolState.remaining setup.program state.point),
          state.generation,
          instructionCount setup.program - ProtocolState.remaining setup.program state.point⟩ := by
  let filtered := fun who => if who ∈ state.excluded then none else joint who
  change Option.map _ (ProtocolState.recoveryProposal setup.program state.point filtered) =
    some proposal at decoded
  obtain ⟨pair, original, same⟩ := Option.map_eq_some_iff.mp decoded
  have ranked := ProtocolState.recoveryProposal_rank setup.program state.point filtered
    pair.1 pair.2 original
  have viewed := readback filtered
  rw [original, Option.map_some] at viewed
  simp only [nativeRecoveryProposal?] at viewed
  split at viewed
  · cases viewed
  · rename_i notCommit
    cases acting : ProtocolState.actor setup.program state.point with
    | none => simp only [acting, Option.bind_none] at viewed; cases viewed
    | some owner =>
      simp only [acting, Option.bind_some] at viewed
      split at viewed
      · rename_i disclosed
        have surviving : owner ∉ state.excluded := by
          intro excluded
          simp only [filtered, excluded, ite_true, Option.map_none, Option.getD_none] at disclosed
          cases disclosed
        have exposed : ((joint owner).map (·.discloses)).getD false = true := by
          simpa only [filtered, surviving, ite_false] using disclosed
        have eventRank := congrArg (fun value : ProposalRecoveryProposal L => value.address.event)
          same
        have valueEq := congrArg (fun value : ProposalRecoveryProposal L =>
          (⟨value.payload, value.value⟩ : Sigma L.Val)) same
        simp only at eventRank valueEq
        refine ⟨owner, rfl, Bool.eq_false_of_not_eq_true notCommit, surviving, exposed, ?_, ?_⟩
        · rw [← eventRank, ← valueEq]
          simpa only [Nat.zero_add, ← ranked] using viewed.symm
        · have address := congrArg (fun value : ProposalRecoveryProposal L => value.address) same
          simpa only [ranked] using address.symm
      · cases viewed

end Vegas

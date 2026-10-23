/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryChronology
import Vegas.Source.CommitRecoveryCursor

/-! # Recovering the last proposal from its canonical archive and source cursor -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoveryCursor (state : setup.proposalRecoveryProtocol.State) : Option (Nat × Nat) :=
  state.map fun current => (current.generation,
    instructionCount setup.program - ProtocolState.remaining setup.program current.point)

def proposalRecoveryCursorWord : ∀ {state : setup.proposalRecoveryProtocol.State},
    setup.proposalRecoveryProtocol.Trace state → List (Option (Nat × Nat))
  | _, .start => []
  | _, @Trace.extend _ _ before _ prior _ _ _ =>
      setup.proposalRecoveryCursor before :: proposalRecoveryCursorWord prior

theorem proposalRecoveryProposalOf_cursor
    (state : setup.proposalRecoveryProtocol.State)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (proposal : ProposalRecoveryProposal L)
    (decoded : setup.proposalRecoveryProposalOf state joint = some proposal) :
    some (proposal.address.generation, proposal.address.event) =
      setup.proposalRecoveryCursor state := by
  cases state with
  | none => cases decoded
  | some current =>
      have ranked := setup.proposalRecoveryProposalOf_some_rank current joint proposal decoded
      exact congrArg some (Prod.ext ranked.1 ranked.2)

theorem proposalRecovery_prefix_eq_of_same_cursor
    (first second : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some first))
    (right : setup.proposalRecoveryProtocol.Trace (some second)) (kept : TracePrefix left right)
    (same : setup.proposalRecoveryCursor (some first) =
      setup.proposalRecoveryCursor (some second)) :
    (⟨some first, left⟩ : setup.proposalRecoveryProtocol.History) = ⟨some second, right⟩ := by
  have cursors := Option.some.inj same
  have generation := congrArg Prod.fst cursors
  have rank := congrArg Prod.snd cursors
  have leftBound := ProtocolState.remaining_le_instructionCount setup.program first.point
  have rightBound := ProtocolState.remaining_le_instructionCount setup.program second.point
  have remaining : ProtocolState.remaining setup.program first.point =
      ProtocolState.remaining setup.program second.point := by
    change instructionCount setup.program - _ = instructionCount setup.program - _ at rank
    omega
  have oldKept := setup.proposalRecoveryEraseTrace_prefix kept
  have lengths := setup.commitRecovery_same_generation_length oldKept.reachesWithin
    first second rfl rfl generation
  rw [remaining, setup.proposalRecoveryEraseTrace_length,
    setup.proposalRecoveryEraseTrace_length] at lengths
  exact kept.eq_of_length (Nat.add_left_cancel lengths).symm

/-- Even a silent current action has no earlier proposal at its source cursor. -/
theorem proposalRecovery_archive_cursor_fresh (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (proposal : ProposalRecoveryProposal L)
    (member : proposal ∈ setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who trace)) :
    some (proposal.address.generation, proposal.address.event) ≠
      setup.proposalRecoveryCursor state := by
  intro repeated
  have wordMember : proposal ∈ setup.proposalRecoveryProposalWord who
      (setup.proposalRecoveryModel.infoOf who trace) := List.mem_toFinset.mp member
  obtain ⟨before, after, prior, joint, legal, supported, kept, decoded⟩ :=
    setup.proposalRecovery_proposal_word_origin who trace proposal wordMember
  have origin := setup.proposalRecoveryProposalOf_cursor before joint proposal decoded
  cases before with
  | none => cases decoded
  | some before =>
      cases state with
      | none => cases repeated
      | some current =>
          have cursorEq : setup.proposalRecoveryCursor (some before) =
              setup.proposalRecoveryCursor (some current) := origin.symm.trans repeated
          have priorKept : TracePrefix prior trace :=
            (TracePrefix.extend .refl joint legal supported).trans kept
          have equal := setup.proposalRecovery_prefix_eq_of_same_cursor
            before current prior trace priorKept cursorEq
          have length := congrArg (fun history => history.trace.length) equal
          change prior.length = trace.length at length
          have shorter := kept.length_le
          simp only [Trace.length] at shorter
          omega

theorem proposalRecoveryArchive_extend (who : Player)
    {before after : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (prior.extend joint legal supported)) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who prior) ∪
        (setup.proposalRecoveryProposalOf before joint).toList.toFinset := by
  simp only [proposalRecoveryArchive, setup.proposalRecoveryProposalWord_extend,
    List.toFinset_append]

end Vegas.SourceProgram.Setup

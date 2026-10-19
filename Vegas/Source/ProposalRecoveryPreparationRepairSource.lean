/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryPreparationRepairTransition
import Vegas.Source.ProposalRecoveryPreparationRepairLabels

/-! # Selective partners in the initialized proposal-labeled source protocol -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Legal excluded players have no literal action or proposal label. -/
theorem proposalRecoveryJoint_mask_eq {current : CommitRecoveryState setup.program}
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint) :
    (fun owner => if owner ∈ current.excluded then none else joint owner) = joint := by
  funext owner
  by_cases excluded : owner ∈ current.excluded
  · simp only [excluded, ↓reduceIte]
    cases chosen : joint owner with
    | none => rfl
    | some move =>
        have offered := legal.2 owner
        rw [chosen] at offered
        exact (offered.1.2 excluded).elim
  · simp only [excluded, ↓reduceIte]

/-- One initialized-protocol step retains the SAME actual semantic closure
and every public typed proposal, including those of an excluded author. -/
theorem proposalRecovery_preparation_step (owner : Player)
    (original repaired : CommitRecoveryState setup.program)
    (related : CommitRecoveryState.FocalRepair owner original repaired)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some original) joint)
    (after : setup.proposalRecoveryProtocol.State)
    (reached : after ∈ (setup.proposalRecoveryProtocol.step (some original)
      ⟨joint, legal⟩).support) :
    ∃ target : CommitRecoveryState setup.program,
      ∃ translated : Player → Option (ProposalRecoveryMove Player L),
        translated = ProtocolState.repairPreparationJoint owner setup.program original.point joint ∧
        (∀ observer, observer ≠ owner → translated observer = joint observer) ∧
        ∃ permitted : setup.proposalRecoveryProtocol.Legal (some repaired) translated,
          some target ∈ (setup.proposalRecoveryProtocol.step (some repaired)
            ⟨translated, permitted⟩).support ∧
          (∃ current, after = some current ∧ CommitRecoveryState.FocalRepair owner current target) ∧
          setup.proposalRecoveryProposalOf (some repaired) translated =
            setup.proposalRecoveryProposalOf (some original) joint := by
  obtain ⟨current, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  have semanticLegal := setup.proposalRecoveryJoint_legal (state := some original) joint legal.2
  obtain ⟨changed, described, foreign, allowed, target, admitted, relation⟩ :=
    related.preparation_step (proposalRecoveryJoint joint) semanticLegal current supported
  let translated := ProtocolState.repairPreparationJoint owner setup.program original.point joint
  have semantic : proposalRecoveryJoint translated = changed :=
    (ProtocolState.repairPreparationJoint_semantic owner setup.program original.point joint).trans
      described.symm
  have valid : ∀ observer move, joint observer = some move → move.Valid := by
    intro observer move chosen
    have offered := legal.2 observer
    rw [chosen] at offered
    exact offered.2.2
  have permitted : setup.proposalRecoveryProtocol.Legal (some repaired) translated := by
    apply setup.proposalRecovery_legal_of_semantic
    · refine ⟨?_, ?_⟩
      · change ¬ ProtocolState.terminal setup.program repaired.point
        exact fun terminal => legal.1
          ((ProtocolState.FocalRepair.terminal_iff owner setup.program original.point repaired.point
            related.point).mp terminal)
      · change IsLegalJoint repaired.Active repaired.available (proposalRecoveryJoint translated)
        rw [semantic]
        exact allowed
    · exact ProtocolState.repairPreparationJoint_valid owner setup.program original.point joint
        valid
  refine ⟨target, translated, rfl, ?_, permitted, ?_, ⟨current, rfl, relation⟩, ?_⟩
  · intro observer outside
    exact ProtocolState.repairPreparationJoint_foreign owner observer setup.program original.point
      joint outside
  · change some target ∈ ((repaired.step (proposalRecoveryJoint translated)).map some).support
    rw [semantic]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨target, admitted, rfl⟩
  · unfold proposalRecoveryProposalOf
    simp only [Option.bind_some]
    rw [setup.proposalRecoveryJoint_mask_eq joint legal,
      setup.proposalRecoveryJoint_mask_eq translated permitted, related.generation]
    exact congrArg (Option.map fun pair =>
      (⟨⟨setup.program.publicationBlockLow pair.1, original.generation, pair.1⟩,
        pair.2.1, pair.2.2⟩ : ProposalRecoveryProposal L))
      (ProtocolState.FocalRepair.recoveryProposal_preparation owner setup.program
        original.point repaired.point related.point joint)

/-- The full original typed view of every other owner is literal. -/
theorem proposalRecovery_private_of_preparation (owner observer : Player)
    (original repaired : CommitRecoveryState setup.program)
    (related : CommitRecoveryState.FocalRepair owner original repaired)
    (foreign : observer ≠ owner) :
    setup.commitRecoveryPrivate observer (some repaired) =
      setup.commitRecoveryPrivate observer (some original) := by
  exact congrArg some (ProtocolState.FocalRepair.foreign_observe owner observer setup.program
    original.point repaired.point related.point foreign)

/-- Failure controls and the saved source cursor remain literal even when
an unusable author's publication has already permanently excluded them. -/
theorem proposalRecovery_public_of_preparation (owner : Player)
    (original repaired : CommitRecoveryState setup.program)
    (related : CommitRecoveryState.FocalRepair owner original repaired) :
    setup.commitRecoveryPublic (some repaired) = setup.commitRecoveryPublic (some original) := by
  have saved := ProtocolState.FocalRepair.control owner setup.program original.saved repaired.saved
    related.saved
  simp only [commitRecoveryPublic, related.excluded, related.generation, saved.1]

end Vegas.SourceProgram.Setup

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryMenuKind
import Vegas.Source.ProposalRecoveryWordLift

/-! # Literal ordinary labels throughout an actual commitment instruction -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem ProposalRecoveryMove.label_false (move : CommitRecoveryMove Player L) :
    label move false = ordinary move := by
  rcases move with ⟨action, missing⟩
  cases action with
  | commit => rfl
  | reveal _ _ disclose => cases disclose <;> rfl

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- A legal commitment response cannot use a reveal-only proposal label. -/
theorem proposalRecovery_option_ordinary_of_atCommit
    (current : CommitRecoveryState setup.program)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (who : Player) (choice : Option (ProposalRecoveryMove Player L))
    (legal : LegalOption setup.proposalRecoveryProtocol (some current) who choice) :
    (choice.map (·.semantic)).map ProposalRecoveryMove.ordinary = choice := by
  cases chosen : choice with
  | none => rfl
  | some move =>
      rw [chosen] at legal
      have allowed : move.semantic ∈ ProtocolView.recoveryAvailable who setup.program
          (ProtocolState.observe who setup.program current.point) := legal.2.1
      have valid : move.Valid := legal.2.2
      have absent : move.proposed = false := by
        apply Bool.eq_false_iff.mpr
        intro proposed
        obtain ⟨owner, name, revealing⟩ := valid proposed
        have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal who
          setup.program current.point move.semantic allowed ⟨owner, name, false, revealing⟩
        rw [committing] at notCommit
        cases notCommit
      change some (ProposalRecoveryMove.ordinary move.semantic) = some move
      cases move with
      | mk semantic proposed => cases absent; rfl

/-- Every actual commitment joint is the ordinary lift of its literal
semantic joint, including responses that declare unusable material. -/
theorem proposalRecovery_joint_ordinary_of_atCommit
    (current : CommitRecoveryState setup.program)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint) :
    (fun who => (proposalRecoveryJoint joint who).map ProposalRecoveryMove.ordinary) = joint := by
  funext who
  exact setup.proposalRecovery_option_ordinary_of_atCommit current committing who (joint who)
    (by cases selected : joint who <;>
          simpa only [LegalOption, selected] using legal.2 who)

/-- The same actual supported step extends the ordinary lift; no new
source path or alternative chance transition is chosen. -/
theorem proposalRecovery_ordinary_extend_of_atCommit
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (ordinary : setup.proposalRecoveryLiftTrace (fun _ _ => false)
      (setup.proposalRecoveryEraseTrace prior) = prior)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {after : setup.proposalRecoveryProtocol.State}
    (reached : after ∈ (setup.proposalRecoveryProtocol.step (some current) ⟨joint,
      legal⟩).support) :
    setup.proposalRecoveryLiftTrace (fun _ _ => false)
        (setup.proposalRecoveryEraseTrace (prior.extend joint legal reached)) =
      prior.extend joint legal reached := by
  have actions := setup.proposalRecovery_joint_ordinary_of_atCommit current committing joint legal
  have lifted : setup.proposalRecoveryLiftJoint (fun _ _ => false)
      ⟨some current, proposalRecoveryJoint joint,
        setup.proposalRecovery_erase_legal joint legal, after, reached⟩ = joint := by
    change (fun who => (proposalRecoveryJoint joint who).map
      (fun move => ProposalRecoveryMove.label move false)) = joint
    simpa only [ProposalRecoveryMove.label_false] using actions
  change (setup.proposalRecoveryLiftTrace (fun _ _ => false)
    (setup.proposalRecoveryEraseTrace prior)).extend _ _ _ = _
  simp only [ordinary, lifted]

end Setup
end Vegas.SourceProgram

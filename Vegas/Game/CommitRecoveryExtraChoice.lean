/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryBlockDebt
import Vegas.Source.CommitRecoveryDeviation

/-! # First extra source choices enter permanent recovery debt -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A first extra source choice creates public exclusion or hidden current-block
debt, using a genuine intended witness rather than a foreign-retention premise. -/
theorem commitRecovery_first_extra_debt (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player) (current : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some current))
    (original : setup.intendedProtocol.Trace (some current.point))
    (clear : current.excluded = ∅)
    (observed : ∀ observer, observer ≠ who →
      setup.commitRecoveryModel.infoOf observer prior =
        setup.commitRecoveryModel.infoOf observer
          (setup.commitRecoveryLiftHistory wellFormed ⟨some current.point, original⟩).trace)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    (foreignSupport : ∀ observer, observer ≠ who → joint observer ∈
      ((target observer (setup.commitRecoveryModel.infoOf observer prior)).map
        Subtype.val).support)
    (move : CommitRecoveryMove Player L) (chosen : joint who = some move)
    (extra : move.missing = true ∨
      move.action ∉ ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program current.point))
    (next : CommitRecoveryState setup.program)
    (reached : some next ∈
      (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    setup.CheckpointedDebt who (some next) ∨
      setup.HiddenCommitDebt wellFormed who
        ⟨some next, prior.extend joint legal reached⟩ := by
  have permitted := legal.2 who
  rw [chosen] at permitted
  have nativeReached : next ∈ (current.step joint).support := by
    change some next ∈ ((current.step joint).map some).support at reached
    rw [PMF.support_map] at reached
    obtain ⟨value, member, equality⟩ := reached
    cases Option.some.inj equality
    exact member
  have intended := setup.intendedState_trace wellFormed original
  change ProtocolState.Intended setup.program current.point at intended
  rcases current.deviation who clear intended joint move chosen permitted.1.1 permitted.2
      extra next nativeReached with excluded | latent
  · exact Or.inl (Or.inl excluded)
  · have focalNoMiss : CommitRecoveryMove.missed (joint who) = false := by
      apply Bool.eq_false_iff.mpr
      intro missing
      have excluded := current.missed_excludes who joint latent.2.1 permitted.1.1
        missing next nativeReached
      rw [latent.1] at excluded
      exact Finset.notMem_empty _ excluded
    obtain ⟨_clear, image, imagePoint, imageState, related, information⟩ :=
      setup.hidden_commit_recovery_step wellFormed source target copies who current current.point
        prior original clear (ProtocolState.hiddenBindings_refl who setup.program current.point)
        observed latent.2.1 joint legal foreignSupport focalNoMiss next reached
    by_cases nextCommit : ProtocolState.atCommit setup.program next.point = true
    · right
      rcases image with ⟨imageStateValue, imageTrace⟩
      dsimp only at imageState
      subst imageStateValue
      exact ⟨next, imagePoint, imageTrace, rfl, latent.1, latent.2.2, nextCommit,
        related, information⟩
    · left
      have notCommit : ProtocolState.atCommit setup.program next.point = false :=
        Bool.eq_false_iff.mpr nextCommit
      have frontier := setup.commitRecovery_blockFrontier (prior.extend joint legal reached)
      have saved := frontier.saved_eq_point_of_not_atCommit notCommit
      exact Or.inr ⟨saved.symm ▸ latent.2.2, latent.2.2⟩

end Vegas.SourceProgram.Setup

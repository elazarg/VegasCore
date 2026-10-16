/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryContinuingExtension
import GameTheoryExtensions.Analysis.Protocol.RetainedDeviation

/-! # One source-site changes with unchanged auxiliary continuation laws -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- Updating one intended-source lottery and its copied auxiliary lottery
preserves the extension and continuing support. Both are literal one-site
updates, so their original continuation laws remain unchanged elsewhere. -/
theorem commitRecovery_local_source_patch
    (wellFormed : setup.WellFormed)
    (source : ∀ owner, setup.intendedModel.BehavioralPolicy owner)
    (target : ∀ owner, setup.commitRecoveryModel.BehavioralPolicy owner)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (continuing : ∀ owner (site : setup.commitRecoveryModel.InformationSite owner),
      ∀ choice ∈ (target owner site.1).support,
        setup.CommitRecoveryContinues owner site.1 choice.1)
    (who : Player) (selected : setup.intendedModel.InformationSite who)
    (law : PMF (setup.intendedModel.Choice who selected.1)) :
    let restriction := setup.commitRecoveryRestriction wellFormed
    let changed := Profile.update (sig := setup.intendedModel.behavioralSignature) source who
      ((source who).withLaw selected.1 law)
    let patched := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) target who
      ((target who).withLaw (restriction.information who selected.1)
        (law.map (restriction.choice who selected.1)))
    restriction.ExtendsProfile changed patched ∧
      ∀ owner (site : setup.commitRecoveryModel.InformationSite owner),
        ∀ choice ∈ (patched owner site.1).support,
          setup.CommitRecoveryContinues owner site.1 choice.1 := by
  classical
  intro restriction changed patched
  have extended : restriction.ExtendsProfile changed patched := by
    apply copies.update who ((source who).withLaw selected.1 law)
      ((target who).withLaw (restriction.information who selected.1)
        (law.map (restriction.choice who selected.1)))
    intro original
    by_cases same : original.1 = selected.1
    · have sameSite : original = selected := Subtype.ext same
      subst original
      simp only [InformationModel.BehavioralPolicy.withLaw_self]
      exact InformationModel.BehavioralPolicy.withLaw_self (target who)
        (restriction.information who selected.1) (law.map (restriction.choice who selected.1))
    · have distinct : restriction.information who original.1 ≠
          restriction.information who selected.1 := fun equal =>
        same ((restriction.information who).injective equal)
      rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ distinct,
        InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ same]
      exact copies who original
  refine ⟨extended, ?_⟩
  intro owner site choice supported
  by_cases sameOwner : owner = who
  · subst owner
    by_cases sameInput : site.1 = restriction.information who selected.1
    · have sameSite : site = restriction.site who selected := Subtype.ext sameInput
      subst site
      have lawEq : patched who (restriction.information who selected.1) =
          law.map (restriction.choice who selected.1) := by
        dsimp only [patched]
        rw [Profile.update_same, InformationModel.BehavioralPolicy.withLaw_self]
      change choice ∈ (patched who (restriction.information who selected.1)).support at supported
      rw [lawEq] at supported
      obtain ⟨sourceChoice, _member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have values : (restriction.choice who selected.1 sourceChoice).1 =
          CommitRecoveryMove.lift sourceChoice.1 := rfl
      have selectedMove := values.symm.trans (congrArg Subtype.val equal)
      intro move chosen
      rw [chosen] at selectedMove
      cases raw : sourceChoice.1 with
      | none => rw [raw] at selectedMove; cases selectedMove
      | some action =>
          rw [raw] at selectedMove
          have sameMove : (⟨action, false⟩ : CommitRecoveryMove Player L) = move :=
            Option.some.inj selectedMove
          subst move
          exact ⟨rfl, fun _ => setup.intendedMenu_not_failure who selected.1 sourceChoice.1
            sourceChoice.2 action raw⟩
    · have lawEq : patched who site.1 = target who site.1 := by
        dsimp only [patched]
        rw [Profile.update_same, InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ sameInput]
      rw [lawEq] at supported
      exact continuing who site choice supported
  · have lawEq : patched owner site.1 = target owner site.1 := by
      dsimp only [patched]
      rw [Profile.update_of_ne _ _ sameOwner]
    rw [lawEq] at supported
    exact continuing owner site choice supported

end Vegas.SourceProgram.Setup

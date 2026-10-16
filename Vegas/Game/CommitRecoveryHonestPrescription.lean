/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryHonestPins
import Vegas.Game.CommitRecoveryRestriction
import Vegas.Game.CommitRecoveryPooledCompletion
import Vegas.Game.ExclusionMoveExtension

/-! # Actual honest domain pins for normalized source completion

A given intended behavioral profile defines legal domain distributions on
its genuine normalized queries. Original honest information is reconstructed
from the key, so choosing a witness does not change the resulting raw law.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Embed an actual intended action as a legal ordinary part at its normalized
source query. Accepted failure and omission are not part of this domain law. -/
def commitRecoveryHonestDomainChoice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) (choice : setup.intendedModel.Choice who view) :
    setup.CommitRecoveryValueChoice who
      (setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryInformation wellFormed who view))) :=
  ⟨setup.commitRecoveryNoMissErasedChoice who
    (setup.commitRecoveryInformation wellFormed who view)
    (setup.commitRecoveryChoice wellFormed who view choice), by
      intro move selected
      change CommitRecoveryMove.lift choice.val = some move at selected
      cases chosen : choice.val with
      | none => rw [chosen] at selected; cases selected
      | some action =>
          rw [chosen] at selected
          cases Option.some.inj selected
          exact ⟨rfl, setup.intendedMenu_not_failure who view choice.val choice.property action
            chosen⟩⟩

omit [Fintype Player] in
/-- Normalizing the source query preserves the literal intended raw action. -/
theorem commitRecoveryHonestDomainChoice_raw (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) (choice : setup.intendedModel.Choice who view) :
    (setup.commitRecoveryHonestDomainChoice wellFormed who view choice).val.val =
      CommitRecoveryMove.lift choice.val := rfl

omit [Fintype Player] in
private theorem domain_cast_raw (who : Player)
    {first second : setup.commitRecoveryModel.InfoState who} (same : first = second)
    (choice : setup.CommitRecoveryValueChoice who first) :
    (Eq.mp (congrArg (setup.CommitRecoveryValueChoice who) same) choice).val.val =
      choice.val.val := by cases same; rfl

/-- Prescribe the given honest law exactly on every query with a genuine
intended witness. All other pools remain available to the existing completion. -/
def commitRecoveryHonestPoolPins (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (pool : setup.CommitRecoveryValuePool finite) :
    Option (PMF (setup.CommitRecoveryPoolPart finite pool)) := by
  classical
  exact if found : ∃ history : setup.intendedProtocol.History,
      setup.commitRecoveryErasedInformation pool.1
        (setup.commitRecoveryNoMissInformation pool.1
          (setup.commitRecoveryInformation wellFormed pool.1
            (setup.intendedModel.infoOf pool.1 history.trace))) = pool.2.val then
    some ((source pool.1 (setup.intendedModel.infoOf pool.1 found.choose.trace)).map
      fun choice => Eq.mp (congrArg (setup.CommitRecoveryValueChoice pool.1) found.choose_spec)
        (setup.commitRecoveryHonestDomainChoice wellFormed pool.1
          (setup.intendedModel.infoOf pool.1 found.choose.trace) choice))
  else none

/-- The selected pin's literal raw law is the original intended law at EVERY
genuine honest witness. Witness selection contributes no information premise. -/
theorem commitRecoveryHonestPoolPins_raw (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (pool : setup.CommitRecoveryValuePool finite) (history : setup.intendedProtocol.History)
    (atQuery : setup.commitRecoveryErasedInformation pool.1
      (setup.commitRecoveryNoMissInformation pool.1
        (setup.commitRecoveryInformation wellFormed pool.1
          (setup.intendedModel.infoOf pool.1 history.trace))) = pool.2.val) :
    (setup.commitRecoveryHonestPoolPins finite wellFormed source pool).map
      (fun law => law.map (fun choice => choice.val.val)) =
        some ((source pool.1 (setup.intendedModel.infoOf pool.1 history.trace)).map
          (fun choice => CommitRecoveryMove.lift choice.val)) := by
  classical
  have present : ∃ other : setup.intendedProtocol.History,
      setup.commitRecoveryErasedInformation pool.1
        (setup.commitRecoveryNoMissInformation pool.1
          (setup.commitRecoveryInformation wellFormed pool.1
            (setup.intendedModel.infoOf pool.1 other.trace))) = pool.2.val := ⟨history, atQuery⟩
  have sameInfo := setup.commitRecovery_honest_information_eq_of_query_eq wellFormed pool.1
    present.choose history (present.choose_spec.trans atQuery.symm)
  unfold commitRecoveryHonestPoolPins
  rw [dite_eq_left present]
  simp only [Option.map_some, PMF.map_comp, Function.comp_def]
  have rawMap : (source pool.1 (setup.intendedModel.infoOf pool.1 present.choose.trace)).map
      (fun choice =>
        (Eq.mp (congrArg (setup.CommitRecoveryValueChoice pool.1) present.choose_spec)
          (setup.commitRecoveryHonestDomainChoice wellFormed pool.1
            (setup.intendedModel.infoOf pool.1 present.choose.trace) choice)).val.val) =
      (source pool.1 (setup.intendedModel.infoOf pool.1 present.choose.trace)).map
        (fun choice => CommitRecoveryMove.lift choice.val) := by
    apply congrArg (fun f =>
      (source pool.1 (setup.intendedModel.infoOf pool.1 present.choose.trace)).map f)
    funext choice
    exact (setup.domain_cast_raw pool.1 present.choose_spec _).trans
      (setup.commitRecoveryHonestDomainChoice_raw wellFormed pool.1 _ choice)
  rw [rawMap, sameInfo]

open Classical in
/-- The ACTUAL pooled ordinary law at an honest query is precisely its fixed
uniform floor mixed with the given honest raw law, for arbitrary completion
weights. Thus non-honest values enter this query only through that floor. -/
theorem commitRecoveryPooledDomainLaw_honest_raw (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (pool : setup.CommitRecoveryValuePool finite) (history : setup.intendedProtocol.History)
    (atQuery : setup.commitRecoveryErasedInformation pool.1
      (setup.commitRecoveryNoMissInformation pool.1
        (setup.commitRecoveryInformation wellFormed pool.1
          (setup.intendedModel.infoOf pool.1 history.trace))) = pool.2.val) :
    (setup.commitRecoveryPooledDomainLaw finite floor nonnegative bounded
      (setup.commitRecoveryHonestPoolPins finite wellFormed source) weights pool.1 pool.2.val).map
        (fun choice => choice.val.val) =
      mix floor nonnegative bounded
        ((setup.commitRecoveryValueReference finite pool.1 pool.2.val).map
          (fun choice => choice.val.val))
        ((source pool.1 (setup.intendedModel.infoOf pool.1 history.trace)).map
          (fun choice => CommitRecoveryMove.lift choice.val)) := by
  classical
  have pin := setup.commitRecoveryHonestPoolPins_raw finite wellFormed source pool history atQuery
  unfold commitRecoveryPooledDomainLaw
  rw [mix_map, dite_eq_left pool.2.property]
  congr 1
  cases pool with
  | mk who query =>
      cases query with
      | mk info played =>
          change ((setup.commitRecoveryHonestPoolPins finite wellFormed source
              ⟨who, ⟨info, played⟩⟩).getD (weights ⟨who, ⟨info, played⟩⟩)).map
              (fun choice => choice.val.val) = _
          cases selected : setup.commitRecoveryHonestPoolPins finite wellFormed source
              ⟨who, ⟨info, played⟩⟩ with
          | none => rw [selected] at pin; cases pin
          | some law =>
              rw [selected] at pin
              exact Option.some.inj pin

end Vegas.SourceProgram.Setup

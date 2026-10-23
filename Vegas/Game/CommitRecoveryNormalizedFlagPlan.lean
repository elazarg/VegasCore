/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFlagPlan
import Vegas.Game.CommitRecoveryNoMissContinuation

/-! # One initialized occurrence plan realizes the normalized original source

The domain table is the original table on genuine erased source queries.
Actual full-information policies read that same table at the normalized
query. Logical-clock preservation supplies nonrecurrence; the analytical
erased signal model is not used as a recursive normalized information model.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
/-- The selected domain prescription and separate source failure rates are
read at the genuine combined query in the ORIGINAL full source game. -/
def commitRecoveryNormalizedTrembledProfile
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info)) :
    ∀ owner, setup.commitRecoveryModel.BehavioralPolicy owner :=
  setup.commitRecoveryNoMissErasedProfile (fun owner info =>
    setup.commitRecoveryValueTremble owner info omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values owner info))

omit [Fintype Player] in
private theorem original_record_clocks (who : Player)
    (history : setup.commitRecoveryProtocol.History) :
    ((setup.commitRecoveryModel.ownPlay who history.trace).map
      (fun record => record.1.1.2.length)).Nodup := by
  have clocks := setup.commitRecoveryErasedModel_record_clock_nodup who history.trace
  rw [setup.commitRecoveryErasedModel_ownPlay, List.map_map] at clocks
  simpa only [commitRecoveryErasedInformation, List.length_map, Function.comp_def] using clocks

omit [Fintype Player] in
private theorem original_current_clock (who : Player)
    (history : setup.commitRecoveryProtocol.History) :
    (setup.commitRecoveryModel.infoOf who history.trace).1.2.length = history.trace.length := by
  have clock := setup.commitRecoveryErasedModel_word_length who history.trace
  rw [setup.commitRecoveryErasedModel_infoOf] at clock
  simpa only [commitRecoveryErasedInformation, List.length_map] using clock

omit [Fintype Player] in
private theorem original_record_clock_lt (who : Player)
    (history : setup.commitRecoveryProtocol.History)
    (record : setup.commitRecoveryModel.InfoState who × CommitRecoveryMove Player L)
    (recorded : record ∈ setup.commitRecoveryModel.ownPlay who history.trace) :
    record.1.1.2.length < history.trace.length := by
  have reduced : (setup.commitRecoveryErasedInformation who record.1, record.2) ∈
      setup.commitRecoveryErasedModel.ownPlay who history.trace := by
    rw [setup.commitRecoveryErasedModel_ownPlay]
    exact List.mem_map.mpr ⟨record, recorded, rfl⟩
  have acted : setup.commitRecoveryErasedInformation who record.1 ∈
      setup.commitRecoveryErasedModel.actedAt who history.trace := by
    rw [setup.commitRecoveryErasedModel.actedAt_eq_map_ownPlay]
    exact List.mem_map.mpr ⟨_, reduced, rfl⟩
  have earlier := setup.commitRecoveryErasedModel_record_word_length_lt who
    history.trace _ acted
  simpa only [commitRecoveryErasedInformation, List.length_map] using earlier

omit [Fintype Player] in
private theorem normalized_tremble_choice
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values who info =
      (setup.commitRecoveryValueTremble who
        (setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who info))
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        (values who (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryNoMissInformation who info)))).map
            (setup.commitRecoveryNoMissErasedChoice who info).symm := by
  unfold commitRecoveryNormalizedTrembledProfile
  apply pmf_map_injective Subtype.val_injective
  rw [setup.commitRecoveryNoMissErasedProfile_raw, PMF.map_comp]
  rfl

omit [Fintype Player] in
private theorem normalized_tremble_fullSupport
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (full : ∀ owner info, FullSupport (values owner info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    FullSupport (setup.commitRecoveryNormalizedTrembledProfile omission
      omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values who info) := by
  rw [setup.normalized_tremble_choice]
  intro choice
  refine (PMF.mem_support_map_iff _ _ _).mpr
    ⟨(setup.commitRecoveryNoMissErasedChoice who info) choice, ?_, ?_⟩
  · exact setup.commitRecoveryValueTremble_fullSupport who _ omission omissionPositive omissionSmall
      bad badPositive badSmall _ (full who _) _
  · exact (setup.commitRecoveryNoMissErasedChoice who info).symm_apply_apply choice

end Vegas.SourceProgram.Setup

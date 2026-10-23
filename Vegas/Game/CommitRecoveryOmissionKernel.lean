/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNormalizedFlagPlan

/-! # Actual omission marginals of the normalized original source prescription

The original raw choice law retains omission separately from accepted failure
and domain values. This identifies its public kernel before comparing any
failed-attempt continuation.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem inactive_choice_none (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who info)
    (inactive : ¬ setup.commitRecoveryActive who info.1.1) : choice.val = none := by
  cases selected : choice.val with
  | none => rfl
  | some move =>
      have legal := choice.property
      change setup.commitRecoveryMenu who info choice.val at legal
      rw [selected] at legal
      exact (inactive legal.1).elim

private theorem failure_missed (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (active : setup.commitRecoveryActive who info.1.1)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (omitted : Bool) :
    CommitRecoveryMove.missed (setup.commitRecoveryFailureChoice who info omitted).val =
      omitted := by
  cases chosen : (setup.commitRecoveryFailureChoice who info omitted).val with
  | none =>
      have legal := (setup.commitRecoveryFailureChoice who info omitted).property
      change setup.commitRecoveryMenu who info _ at legal
      rw [chosen] at legal
      exact (legal active).elim
  | some move =>
      have property := (setup.commitRecoveryFailureChoice_spec who info omitted move chosen).2
      simpa only [CommitRecoveryMove.missed, Option.elim_some, committing,
        Bool.true_and] using property

private theorem value_missed (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (value : setup.CommitRecoveryValueChoice who info) :
    CommitRecoveryMove.missed value.val.val = false := by
  cases selected : value.val.val with
  | none => rfl
  | some move => exact (value.property move selected).1

/-- At any active original commitment input, the public omission law is
exactly the prescribed omission coin. Accepted failures remain nonmissing;
no conditional posterior or value-independence premise is used. -/
theorem commitRecoveryValueTremble_missed_law (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (active : setup.commitRecoveryActive who info.1.1)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) :
    (setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values).map
          (fun choice => CommitRecoveryMove.missed choice.val) =
      mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false) := by
  have ordinary : values.map (fun value => CommitRecoveryMove.missed value.val.val) =
      PMF.pure false := by
    calc
      _ = values.map (fun _ => false) := by
        apply congrArg (fun f => values.map f)
        funext value
        exact setup.value_missed who info value
      _ = _ := PMF.map_const _ _
  simp only [commitRecoveryValueTremble, committing, ↓reduceIte, mix_map, PMF.pure_map,
    PMF.map_comp, Function.comp_def,
    setup.failure_missed who info active committing true,
    setup.failure_missed who info active committing false]
  exact congrArg (mix omission omissionNonnegative omissionBounded (PMF.pure true))
    ((congrArg (mix bad badNonnegative badBounded (PMF.pure false)) ordinary).trans
      (mix_self bad badNonnegative badBounded (PMF.pure false)))

private theorem normalized_commit (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who info)).1.1.1.elim false
        (ProtocolView.atCommit who setup.program) = true := by
  have view : (setup.commitRecoveryNoMissInformation who info).1.1.1 = info.1.1.1 := by
    unfold commitRecoveryNoMissInformation
    split
    · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ info).1
    · rfl
  change ((setup.commitRecoveryNoMissInformation who info).1.1.1.map
    (ProtocolView.eraseHistory who setup.program)).elim false
      (ProtocolView.atCommit who setup.program) = true
  rw [view]
  cases current : info.1.1.1 with
  | none => simp only [current, Option.elim_none, Bool.false_eq_true] at committing
  | some observed =>
      simpa only [Option.map_some, Option.elim_some, ProtocolView.atCommit_eraseHistory,
        current] using committing

open Classical in
/-- The actual normalized full-information prescription has one fixed
omission coin at active commitment inputs and no omission at inactive inputs.
Its full private query, domain values and accepted-failure rate do not enter
this public marginal. -/
theorem commitRecoveryNormalizedTrembledProfile_missed_law
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded values who info).map
        (fun choice => CommitRecoveryMove.missed choice.val) =
      if setup.commitRecoveryActive who info.1.1 then
        mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false)
      else PMF.pure false := by
  classical
  by_cases active : setup.commitRecoveryActive who info.1.1
  · rw [ite_eq_left active]
    let query := setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who info)
    have queryActive : setup.commitRecoveryActive who query.1.1 := by
      by_contra inactive
      let choice : setup.commitRecoveryModel.Choice who query := ⟨none, inactive⟩
      have original := ((setup.commitRecoveryNoMissErasedChoice who info).symm choice).property
      change ¬ setup.commitRecoveryActive who info.1.1 at original
      exact original active
    change (setup.commitRecoveryNoMissErasedProfile
      (fun owner query => setup.commitRecoveryValueTremble owner query omission
        omissionNonnegative omissionBounded bad badNonnegative badBounded (values owner query))
        who info).map (CommitRecoveryMove.missed ∘ Subtype.val) = _
    rw [← PMF.map_comp, setup.commitRecoveryNoMissErasedProfile_raw, PMF.map_comp]
    exact setup.commitRecoveryValueTremble_missed_law who query queryActive
      (setup.normalized_commit who info committing) omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values who query)
  · rw [ite_eq_right active]
    calc
      _ = (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative
        omissionBounded bad badNonnegative badBounded values who info).map (fun _ => false) := by
          apply congrArg (fun f => PMF.map f _)
          funext choice
          rw [setup.inactive_choice_none who info choice active]
          rfl
      _ = _ := PMF.map_const _ _

variable [Fintype Player]

end Vegas.SourceProgram.Setup

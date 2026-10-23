/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryValueTremble
import Vegas.Source.CommitRecoveryErasedModel
import Vegas.Game.CommitRecoveryReference
import Interaction.ReactivePolicyMixture

/-! # Original occurrence flags independent of reduced domain tables

Source logical time is public and strictly advances at each instruction.
Counterfactual private queries at the same occurrence share their failure
flags. Domain values remain independent coordinates of the original table.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Omission and accepted source failure are independent, fixed-rate draws. -/
def commitRecoveryFlagLaw
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1) : PMF (Bool × Bool) :=
  (mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false)).bind
    fun omitted =>
      (mix bad badNonnegative badBounded (PMF.pure true) (PMF.pure false)).map (Prod.mk omitted)

omit [Fintype Player] in
/-- At a single query the independent occurrence flags and ordinary domain
draw give exactly the original legal three-class source perturbation. -/
theorem commitRecoveryFlagLaw_choice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) :
    (commitRecoveryFlagLaw omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded).bind
        (fun flags => values.map (setup.commitRecoveryValueFlags who info flags.1 flags.2)) =
      setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values := by
  rw [commitRecoveryFlagLaw, PMF.bind_bind]
  simp only [PMF.bind_map]
  exact setup.commitRecoveryValueFlags_law who info omission omissionNonnegative omissionBounded
    bad badNonnegative badBounded values

omit [Fintype Player] in
/-- Genuine chronological own actions have distinct public source times,
including actions in retired attempts and passive source transitions. -/
theorem commitRecoveryErasedModel_record_clock_nodup (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      ((setup.commitRecoveryErasedModel.ownPlay who trace).map
        (fun record => record.1.1.2.length)).Nodup
  | _, .start => by
      change ([] : List Nat).Nodup
      exact List.nodup_nil
  | _, .extend prior joint legal supported => by
      rw [InfoSignals.ownPlay_extend]
      cases chosen : joint who with
      | none =>
          exact commitRecoveryErasedModel_record_clock_nodup who prior
      | some action =>
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, commitRecoveryErasedModel_record_clock_nodup who prior⟩
          intro member
          obtain ⟨record, recorded, same⟩ := List.mem_map.mp member
          have acted : record.1 ∈ setup.commitRecoveryErasedModel.actedAt who prior := by
            rw [setup.commitRecoveryErasedModel.actedAt_eq_map_ownPlay]
            exact List.mem_map.mpr ⟨record, recorded, rfl⟩
          have earlier := setup.commitRecoveryErasedModel_record_word_length_lt who
            prior record.1 acted
          rw [same, setup.commitRecoveryErasedModel_word_length who prior] at earlier
          exact Nat.lt_irrefl _ earlier

end Vegas.SourceProgram.Setup

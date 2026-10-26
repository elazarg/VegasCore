/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.Bayes
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Multiplicative certificates for consistent beliefs

A product identity between actual history reach weights survives Bayesian
normalization when both sides use the same information sites. It therefore
holds along every common fully mixed Bayes sequence and in its consistent
limit. The identity may arise from shared behavioral choices in history
monomials; no restriction to power sequences is made.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter
open scoped ENNReal

variable {ι : Type} [Fintype ι] {E : ExecutionProtocol ι} {M : InformationModel E}
  {Index : Type} [Fintype Index]

/-- A balanced identity of actual reach monomials is necessary for consistency.
The histories on opposite sides may differ, but their normalization sites agree. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.belief_prod_eq
    {assessment : M.BehavioralAssessment} {antichain : M.DecisionInformationAntichain}
    (consistent : assessment.IsSequentiallyConsistent antichain)
    (who : Index → ι) (site : ∀ index, M.InformationSite (who index))
    (left right : ∀ index, M.InformationHistory (who index) (site index).1)
    (reach : ∀ profile : ∀ player, M.BehavioralPolicy player,
      ∏ index, (M.historyReachWeight profile (left index).1).toReal =
        ∏ index, (M.historyReachWeight profile (right index).1).toReal) :
    ∏ index, (assessment.belief (who index) (site index) (left index)).toReal =
      ∏ index, (assessment.belief (who index) (site index) (right index)).toReal := by
  classical
  obtain ⟨sequence, approximate, converges⟩ := consistent
  have identity (n : Nat) :
      ∏ index, ((sequence n).belief (who index) (site index) (left index)).toReal =
        ∏ index, ((sequence n).belief (who index) (site index) (right index)).toReal := by
    obtain ⟨mixed, bayes⟩ := approximate n
    have positive (index : Index) :
        0 < M.informationMass (sequence n).strategy (who index) (site index) := by
      apply (M.informationMass_pos_iff _ _ _).mpr
      refine ⟨left index, ?_⟩
      exact pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp
        (mixed.history_supported (left index).1.trace))
    calc
      _ = ∏ index, (M.historyReachWeight (sequence n).strategy (left index).1).toReal /
          (M.informationMass (sequence n).strategy (who index) (site index)).toReal :=
        Finset.prod_congr rfl fun index _ => by rw [bayes _ _ (positive index), ENNReal.toReal_div]
      _ = ∏ index, (M.historyReachWeight (sequence n).strategy (right index).1).toReal /
          (M.informationMass (sequence n).strategy (who index) (site index)).toReal := by
        rw [Finset.prod_div_distrib, Finset.prod_div_distrib, reach]
      _ = _ := Finset.prod_congr rfl fun index _ => by
        rw [bayes _ _ (positive index), ENNReal.toReal_div]
  have leftLimit := tendsto_finsetProd Finset.univ fun index _ =>
    (converges.belief (who index) (site index)).toReal (left index)
  have rightLimit := tendsto_finsetProd Finset.univ fun index _ =>
    (converges.belief (who index) (site index)).toReal (right index)
  apply tendsto_nhds_unique leftLimit
  apply rightLimit.congr'
  filter_upwards [] with n
  exact (identity n).symm

end GameTheory.Protocol.InformationModel

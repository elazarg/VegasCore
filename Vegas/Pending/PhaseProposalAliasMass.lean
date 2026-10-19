/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalResponseAliases

/-! # Quantitative alias factors in the actual counted response fibers -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (who : Player)
  (past : List (phaseApplication runtime leaks).PlayerEntry)
  (view : (phaseApplication runtime leaks).PlayerView)

/-- The fixed uniform mass of one actual raw preimage. This depends on the
literal local menu and emitted packet, but not source weights or bad flags. -/
def responseAliasMass (response : Response runtime leaks bounds who past view) : ℝ :=
  ((PMF.fiberUniform (projectResponse runtime leaks bounds who past view)
    (canonicalResponse runtime leaks bounds who past view)
    (project_canonicalResponse runtime leaks bounds who past view)
    (projectResponse runtime leaks bounds who past view response)) response).toReal

/-- Every genuine raw alias has a positive fixed uniform preimage mass. -/
theorem responseAliasMass_positive (response : Response runtime leaks bounds who past view) :
    0 < responseAliasMass runtime leaks bounds who past view response := by
  apply ENNReal.toReal_pos
  · exact (PMF.mem_support_iff _ _).mp
      ((PMF.fiberUniform_supported _ _ _ _ response).mpr rfl)
  · exact PMF.apply_ne_top _ _

/-- Splitting adds no mass outside the selected semantic packet class. -/
theorem splitResponseLaw_probability_le_class
    (law : PMF (ResponseClass runtime leaks bounds who past view))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (response : Response runtime leaks bounds who past view) :
    ((splitResponseLaw runtime leaks bounds who past view law weight nonnegative atMostOne)
        response).toReal ≤
      (law (projectResponse runtime leaks bounds who past view response)).toReal := by
  rw [splitResponseLaw_probability]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pmf_toReal_apply_le_one _ _)

/-- A positive alias tier gives a raw atom a lower bound with its actual
preimage factor. Private evidence menu sizes need not agree across worlds. -/
theorem splitResponseLaw_probability_ge_alias
    (law : PMF (ResponseClass runtime leaks bounds who past view))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (response : Response runtime leaks bounds who past view) :
    (law (projectResponse runtime leaks bounds who past view response)).toReal * weight *
        responseAliasMass runtime leaks bounds who past view response ≤
      ((splitResponseLaw runtime leaks bounds who past view law weight nonnegative atMostOne)
        response).toReal := by
  rw [splitResponseLaw_probability, PMF.splitKernel, mix_apply_toReal]
  have remainder : 0 ≤ (1 - weight) * ((PMF.pure
      (canonicalResponse runtime leaks bounds who past view
        (projectResponse runtime leaks bounds who past view response))) response).toReal :=
    mul_nonneg (sub_nonneg.mpr atMostOne) ENNReal.toReal_nonneg
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact le_add_of_nonneg_right remainder

end Vegas.EventGraphRuntime.PhaseProposal

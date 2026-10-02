/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Sequential equilibrium depends only on terminal payoffs

Changing a payoff at nonterminal histories preserves every complete continuation
comparison and its expectation domain. This also applies to truncated contexts
when their horizon is certified to complete play. No bounded-payoff assumption
or common decision depth is needed.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E}

namespace BehavioralAssessment

variable (assessment : M.BehavioralAssessment)

theorem isSequentiallyRationalAt_iff_of_terminal_payoff_eq
    (certificate : E.WellFoundedHistories) {who : Player} (site : M.InformationSite who)
    (first second : E.History → ℝ)
    (equal : ∀ final, E.terminal final.state → first final = second final) :
    assessment.IsSequentiallyRationalAt site
        (assessment.continuationContext certificate site first) ↔
      assessment.IsSequentiallyRationalAt site
        (assessment.continuationContext certificate site second) := by
  have agreement (alternative : M.BehavioralPolicy who) :
      ∀ final ∈ ((assessment.continuationContext certificate site first).outcome
        alternative).support, first final = second final := fun final supported =>
    equal final (assessment.continuationContext_support_terminal certificate site first
      alternative final supported)
  exact Context.isLocallyOptimal_congr
    (fun alternative => hasExpectation_congr_on_support (agreement alternative))
    (fun alternative => extendedExpect_congr_on_support (agreement alternative))

theorem isSequentialEquilibrium_iff_of_terminal_payoff_eq
    (antichain : M.DecisionInformationAntichain) (certificate : E.WellFoundedHistories)
    (first second : Player → E.History → ℝ)
    (equal : ∀ who final, E.terminal final.state → first who final = second who final) :
    assessment.IsSequentialEquilibrium antichain certificate first ↔
      assessment.IsSequentialEquilibrium antichain certificate second := by
  unfold IsSequentialEquilibrium IsSequentialEquilibriumFor
  apply and_congr_left
  intro _
  unfold IsSequentiallyRationalFor
  apply forall_congr'
  intro who
  apply forall_congr'
  intro site
  exact assessment.isSequentiallyRationalAt_iff_of_terminal_payoff_eq certificate site
    (first who) (second who) (equal who)

theorem isSequentialEquilibriumFor_iff_of_bounded_terminal_payoff_eq
    (antichain : M.DecisionInformationAntichain) (certificate : E.WellFoundedHistories)
    {horizon : Nat} (bounded : E.BoundedHorizon horizon)
    (first second : Player → E.History → ℝ)
    (equal : ∀ who final, E.terminal final.state → first who final = second who final) :
    assessment.IsSequentialEquilibriumFor antichain (fun who site =>
        assessment.truncatedContinuationContext site (first who) horizon) ↔
      assessment.IsSequentialEquilibriumFor antichain (fun who site =>
        assessment.truncatedContinuationContext site (second who) horizon) :=
  (assessment.isSequentialEquilibrium_iff_truncated_of_bounded M antichain certificate bounded
    first).symm.trans
      ((assessment.isSequentialEquilibrium_iff_of_terminal_payoff_eq antichain certificate
        first second equal).trans
          (assessment.isSequentialEquilibrium_iff_truncated_of_bounded M antichain certificate
            bounded second))

end BehavioralAssessment

end GameTheory.Protocol.InformationModel

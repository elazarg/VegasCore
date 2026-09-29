/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Equivalent continuation horizons after a bounded prefix

A remaining-horizon context and a full-horizon context have identical outcome
laws once both reach termination. This connects clocked one-shot theorems to
continuation simulations stated with a single global evaluation bound.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)

omit [DecidableEq Player] in
theorem runBehavioralFrom_remaining
    (profile : ∀ who, M.BehavioralPolicy who) (horizon : Nat)
    (bounded : E.BoundedHorizon horizon) (history : E.History) :
    M.runBehavioralFrom profile (horizon - history.trace.length) history =
      M.runBehavioralFrom profile horizon history := by
  have terminal (last : E.History)
      (supported : last ∈ (M.runBehavioralFrom profile
        (horizon - history.trace.length) history).support) : E.terminal last.state := by
    rcases E.runRandomizedFor_terminal_or_length (M.randomizedChooser profile)
      (horizon - history.trace.length) history last supported with stopped | length
    · exact stopped
    · exact bounded last.state last.trace (by omega)
  have split : horizon = (horizon - history.trace.length) +
      (horizon - (horizon - history.trace.length)) := by omega
  conv_rhs => rw [split, M.runBehavioralFrom_add]
  symm
  refine Eq.trans (bind_congr_on_support _ fun last supported => ?_) (PMF.bind_pure _)
  exact M.runBehavioralFrom_of_terminal profile _ (terminal last supported)

theorem BehavioralAssessment.continuationContext_remaining
    (assessment : M.BehavioralAssessment) (horizon : Nat)
    (bounded : E.BoundedHorizon horizon) (who : Player) (site : M.InformationSite who)
    (depth : Nat) (clock : InformationSite.CommonDepth M site depth)
    (payoff : E.History → ℝ) :
    assessment.continuationContext site payoff (horizon - depth) =
      assessment.continuationContext site payoff horizon := by
  have outcomes : (fun alternative : M.BehavioralPolicy who =>
      (assessment.belief who site).bind fun history =>
        M.runBehavioralFrom
          (GameTheory.Profile.update (sig := M.behavioralSignature)
            assessment.strategy who alternative) (horizon - depth) history.1) =
      (fun alternative => (assessment.belief who site).bind fun history =>
        M.runBehavioralFrom
          (GameTheory.Profile.update (sig := M.behavioralSignature)
            assessment.strategy who alternative) horizon history.1) := by
    funext alternative
    apply bind_congr_on_support _
    intro history _
    rw [← clock history]
    exact M.runBehavioralFrom_remaining _ horizon bounded history.1
  exact congrArg (fun outcome => GameTheory.Protocol.Context.mk outcome payoff) outcomes

theorem BehavioralAssessment.sequentialEquilibrium_remaining_iff
    [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]
    (assessment : M.BehavioralAssessment) (antichain : M.DecisionInformationAntichain)
    (horizon : Nat) (bounded : E.BoundedHorizon horizon)
    (depth : ∀ who, M.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth M site (depth who site))
    (payoff : Player → E.History → ℝ) :
    assessment.IsSequentialEquilibriumFor antichain (fun who site =>
      assessment.continuationContext site (payoff who) (horizon - depth who site)) ↔
    assessment.IsSequentialEquilibriumFor antichain (fun who site =>
      assessment.continuationContext site (payoff who) horizon) := by
  have contexts : (fun who site => assessment.continuationContext site
      (payoff who) (horizon - depth who site)) =
      (fun who site => assessment.continuationContext site (payoff who) horizon) := by
    funext who site
    exact assessment.continuationContext_remaining M horizon bounded who site
      (depth who site) (clock who site) (payoff who)
  rw [contexts]

end GameTheory.Protocol.InformationModel

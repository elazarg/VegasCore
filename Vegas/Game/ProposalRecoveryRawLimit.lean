/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryAcceptedFailure
import GameTheory.Analysis.Protocol.SequentialLimits

/-! # Actual accepted-failure comparisons at the same enriched source limit -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
  (limit : setup.proposalRecoveryModel.BehavioralAssessment)
  (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
  (omission bad delivery : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (deliveryNonnegative : ∀ n, 0 ≤ delivery n) (deliveryBounded : ∀ n, delivery n ≤ 1)
  (values : ℕ → (who : Player) → (key : setup.ProposalRecoveryComponent who) →
    PMF (setup.CommitRecoveryValueChoice who key.1))
  (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
    (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
    (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
      setup.proposalRecoveryNormalizedTrembledProfile
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n)
        (delivery n) (deliveryNonnegative n) (deliveryBounded n)
        (values n) who (setup.proposalRecoveryModel.infoOf who history.trace))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
  (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)

include finite converges prescribed below

open Classical in
/-- Whole actual continuations, including every retry, pass to the SAME
assessment limit. Only the finite terminal-value convergence engine is used. -/
theorem proposalRecovery_normalized_limit_accepted_failure_le
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (choice : setup.proposalRecoveryModel.Choice focal site.1)
    (failed : ∃ move, choice.val.map (·.semantic) = some move ∧
      move.action.IsFailure ∧ move.missing = false)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site.1))
    (nonmissing : ∀ selected ∈ law.support,
      CommitRecoveryMove.missed (selected.val.map (·.semantic)) = false) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 (PMF.pure choice)) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          ((limit.strategy focal).withLaw site.1 law) := by
  classical
  let _ : Finite setup.proposalRecoveryProtocol.History :=
    setup.proposalRecovery_finite_history finite
  let _ := Fintype.ofFinite setup.proposalRecoveryProtocol.History
  let payoff := setup.proposalRecoveryPayoff utility excludedPayoff focal
  let total := ∑ final : setup.proposalRecoveryProtocol.History, |payoff final|
  have totalBound (final : setup.proposalRecoveryProtocol.History) : |payoff final| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ final)
  have value (current : PMF (setup.proposalRecoveryModel.Choice focal site.1)) :
      Tendsto (fun n =>
        ((sequence n).continuationContext
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          site payoff).value (((sequence n).strategy focal).withLaw site.1 current))
        atTop (nhds ((limit.continuationContext
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site payoff).value
            ((limit.strategy focal).withLaw site.1 current))) := by
    apply setup.proposalRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal site (converges.belief focal site)
      _ payoff total ((abs_nonneg _).trans (totalBound setup.proposalRecoveryProtocol.initHistory))
      (fun final _ => totalBound final)
    intro decision
    by_cases here : decision.1 = site.1
    · have eqSite : decision = site := Subtype.ext here
      subst decision
      simpa only [InformationModel.BehavioralPolicy.withLaw_self] using
        pmfConvergesPointwise_const current
    · simpa only [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here] using
        converges.strategy focal decision
  exact le_of_tendsto_of_tendsto' (value _) (value _) (fun n =>
    setup.proposalRecovery_normalized_accepted_failure_conditional_value_le
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n)
      (delivery n) (deliveryNonnegative n) (deliveryBounded n) (values n) finite
      (sequence n) (prescribed n) utility excludedPayoff below focal site committing
      choice failed law nonmissing)

end Vegas.SourceProgram.Setup

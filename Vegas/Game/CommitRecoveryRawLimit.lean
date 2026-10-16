/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFailedLimit
import Vegas.Game.CommitRecoveryAcceptedFailure

/-! # All raw alternatives at the original source limit

Accepted failure is compared through its actual original commitment window,
including every later reset. Voluntary failure pays the terminal floor.
Together these comparisons extend domain optimality to the full source menu.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

section Limits

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (limit : setup.commitRecoveryModel.BehavioralAssessment)
  (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
  (omission bad : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (values : ℕ → (who : Player) → (info : setup.commitRecoveryModel.InfoState who) →
    PMF (setup.CommitRecoveryValueChoice who info))
  (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
    (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
    (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
      setup.commitRecoveryNormalizedTrembledProfile
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n) (values n) who
          (setup.commitRecoveryModel.infoOf who history.trace))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
  (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)

include finite converges prescribed below

open Classical in
/-- The ACTUAL accepted-failure comparison passes to the same source limit.
The entire later original continuation, including retries, remains in both
values. No assumed limit payoff comparison or future optimality is used. -/
theorem commitRecovery_normalized_limit_accepted_failure_le
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (law : PMF (setup.CommitRecoveryValueChoice focal site.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1
          (PMF.pure (setup.commitRecoveryFailureChoice focal site.1 false))) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((limit.strategy focal).withLaw site.1 (law.map Subtype.val)) := by
  classical
  let _ : Finite setup.commitRecoveryProtocol.History := setup.commitRecovery_finite_history finite
  let _ := Fintype.ofFinite setup.commitRecoveryProtocol.History
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let total := ∑ final : setup.commitRecoveryProtocol.History, |payoff final|
  have totalBound (final : setup.commitRecoveryProtocol.History) : |payoff final| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ final)
  have value (current : PMF (setup.commitRecoveryModel.Choice focal site.1)) :
      Tendsto (fun n =>
        ((sequence n).continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
          site payoff).value (((sequence n).strategy focal).withLaw site.1 current))
        atTop (nhds ((limit.continuationContext
          setup.commitRecoveryProtocol_bounded.wellFoundedHistories site payoff).value
            ((limit.strategy focal).withLaw site.1 current))) := by
    apply setup.commitRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal site (converges.belief focal site)
      _ payoff total ((abs_nonneg _).trans (totalBound setup.commitRecoveryProtocol.initHistory))
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
    setup.commitRecovery_normalized_accepted_failure_conditional_value_le
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n) finite (sequence n) (prescribed n)
      utility excludedPayoff below focal site committing law)

open Classical in
/-- Domain local optimality at the same original source limit controls EVERY
raw local law. Accepted failure is dominated by a domain value through the
actual original runner, and omission pays the terminal floor. -/
theorem commitRecovery_normalized_limit_localOptimal_of_domain
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (domainOptimal : ∀ domain : PMF (setup.CommitRecoveryValueChoice focal site.1),
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((limit.strategy focal).withLaw site.1 (domain.map Subtype.val)) ≤
        (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
          (setup.commitRecoveryPayoff utility excludedPayoff focal)).value (limit.strategy focal))
    (law : PMF (setup.commitRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let _ : Finite setup.commitRecoveryProtocol.History := setup.commitRecovery_finite_history finite
  let _ := setup.commitRecovery_finite_choice finite focal site.1
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  rw [limit.continuationContext_withLaw_eq_expect
    (setup.commitRecoveryModel.decisionRecall_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall).actsOnceWhereItMatters
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal) law]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro choice _supported
  let reference := setup.commitRecoveryValueReference finite focal site.1
  have allChoices := setup.commitRecoveryValueTremble_fullSupport focal site.1
    (1 / 2) (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    reference (setup.commitRecoveryValueReference_fullSupport finite focal site.1) choice
  simp only [commitRecoveryValueTremble, committing, ↓reduceIte] at allChoices
  rcases support_mix_subset _ _ _ _ _ allChoices with omitted | other
  · have equal := (PMF.mem_support_pure_iff _ _).mp omitted
    subst choice
    have fails : ¬ setup.CommitRecoveryContinues focal site.1
        (setup.commitRecoveryFailureChoice focal site.1 true).val := by
      intro continues
      obtain ⟨history, _running, action, offered⟩ := site.property
      have active : setup.commitRecoveryActive focal site.1.1.1 := offered.1
      cases selected : (setup.commitRecoveryFailureChoice focal site.1 true).val with
      | none =>
          have legal := (setup.commitRecoveryFailureChoice focal site.1 true).property
          change setup.commitRecoveryMenu focal site.1 _ at legal
          rw [selected] at legal
          exact legal active
      | some move =>
          have missing := (setup.commitRecoveryFailureChoice_spec focal site.1 true move selected).2
          rw [committing, Bool.true_and] at missing
          exact Bool.noConfusion (missing.symm.trans (continues move selected).1)
    rw [setup.commitRecovery_voluntaryFailure_context_value limit focal site _ fails
      utility excludedPayoff]
    exact setup.commitRecovery_conditional_value_lower limit utility excludedPayoff below
      focal site (limit.strategy focal)
  · rcases support_mix_subset _ _ _ _ _ other with accepted | ordinary
    · have equal := (PMF.mem_support_pure_iff _ _).mp accepted
      subst choice
      let domain := (setup.commitRecoveryValueChoice_nonempty focal site.1).some
      have dominates := setup.commitRecovery_normalized_limit_accepted_failure_le finite
        sequence limit converges omission bad omissionNonnegative omissionBounded
        badNonnegative badBounded values prescribed utility excludedPayoff below focal site
        committing (PMF.pure domain)
      have optimal := domainOptimal (PMF.pure domain)
      have compared := dominates.trans optimal
      convert compared using 1
      rfl
    · obtain ⟨domain, _selected, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp ordinary
      have optimal := domainOptimal (PMF.pure domain)
      simp only [PMF.pure_map, equal] at optimal
      convert optimal using 1
      rfl

end Limits

end Vegas.SourceProgram.Setup

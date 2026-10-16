/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryOrdinaryLimitCopies
import Vegas.Game.CommitRecoveryVoluntaryFailurePayoff
import GameTheory.Analysis.Protocol.RestrictionIncentives

/-! # Raw source rationality at known-failed limit sites

The actual finite-stage terminal coupling identifies all nonmissing choices.
Only the prescribed omission mass can remain suboptimal, and it vanishes in
the same original assessment limit. No belief transport is used here.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- The original terminal payoff floor bounds every original conditional
continuation policy, with its actual full-information assessment belief. -/
theorem commitRecovery_conditional_value_lower [Finite setup.commitRecoveryProtocol.History]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (policy : setup.commitRecoveryModel.BehavioralPolicy focal) :
    excludedPayoff focal ≤
      (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value policy := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value]
  let law := (assessment.belief focal site).bind fun history =>
    setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
        assessment.strategy focal policy) history.1
  change excludedPayoff focal ≤ expect law _
  rw [← expect_constant law (excludedPayoff focal)]
  apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  intro final supported
  obtain ⟨history, _supported, child⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  exact setup.commitRecovery_terminal_payoff_lower utility excludedPayoff below focal final
    (setup.commitRecoveryModel.runBehavioralTerminalFrom_support_terminal
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories _ history.1 final child)

open Classical in
/-- Every raw one-site law is unprofitable at a known-failed site of the SAME
source assessment limit. Actual nonmissing indifference and the prescribed
vanishing omission law suffice; neither Bayes nor a representative is assumed. -/
theorem commitRecovery_normalized_failed_limit_localOptimal
    [Finite setup.commitRecoveryProtocol.History]
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
    (omissionVanishes : Tendsto omission atTop (nhds 0))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (failed : ∀ history : setup.commitRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧ first.NewFailure)
    (law : PMF (setup.commitRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let _ := Fintype.ofFinite setup.commitRecoveryProtocol.History
  let missed := fun choice : setup.commitRecoveryModel.Choice focal site.1 =>
    CommitRecoveryMove.missed choice.val
  obtain ⟨history, running, action, offered⟩ := site.property
  have active : setup.commitRecoveryActive focal site.1.1.1 := offered.1
  have omissionLaw (n : ℕ) : ((sequence n).strategy focal site.1).map missed =
      mix (omission n) (omissionNonnegative n) (omissionBounded n)
        (PMF.pure true) (PMF.pure false) := by
    have actual := prescribed n focal history.1 running
    rw [history.property] at actual
    rw [actual, setup.commitRecoveryNormalizedTrembledProfile_missed_law
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n) focal site.1 committing,
      ite_eq_left active]
  have retained : (limit.strategy focal site.1).map missed = PMF.pure false := by
    have flags := pmfConvergesPointwise_mix_zero omission omissionNonnegative omissionBounded
      omissionVanishes (PMF.pure true) (PMF.pure false)
    exact ((converges.strategy focal site).map missed).unique
      (by simpa only [omissionLaw] using flags)
  let ref := (setup.commitRecoveryValueChoice_nonempty focal site.1).some
  have refMissed : missed ref.val = false := by
    cases chosen : ref.val.val with
    | none => simp only [missed, chosen, CommitRecoveryMove.missed, Option.elim_none]
    | some move =>
        simpa only [missed, chosen, CommitRecoveryMove.missed, Option.elim_some] using
          (ref.property move chosen).1
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let total := ∑ final : setup.commitRecoveryProtocol.History, |payoff final|
  have totalBound (final : setup.commitRecoveryProtocol.History) : |payoff final| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ final)
  have value (replacement : ℕ → setup.commitRecoveryModel.BehavioralPolicy focal)
      (policy : setup.commitRecoveryModel.BehavioralPolicy focal)
      (policies : ∀ decision : setup.commitRecoveryModel.InformationSite focal,
        PMFConvergesPointwise (fun n => replacement n decision.1) (policy decision.1)) :=
    setup.commitRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal site (converges.belief focal site)
      policies payoff total
      ((abs_nonneg _).trans (totalBound setup.commitRecoveryProtocol.initHistory))
      (fun final _ => totalBound final)
  have pureConverges (choice : setup.commitRecoveryModel.Choice focal site.1)
      (decision : setup.commitRecoveryModel.InformationSite focal) :
      PMFConvergesPointwise
        (fun n => ((sequence n).strategy focal).commit site.1 choice decision.1)
        ((limit.strategy focal).commit site.1 choice decision.1) := by
    by_cases here : decision.1 = site.1
    · have eqSite : decision = site := Subtype.ext here
      subst decision
      simpa only [InformationModel.BehavioralPolicy.commit_self] using
        pmfConvergesPointwise_const (PMF.pure choice)
    · simpa only [InformationModel.BehavioralPolicy.commit_of_ne _ _ _ here] using
        converges.strategy focal decision
  have equal (choice : setup.commitRecoveryModel.Choice focal site.1)
      (nonmissing : missed choice = false) :
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value ((limit.strategy focal).commit site.1 choice) =
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value ((limit.strategy focal).commit site.1 ref.val) := by
    have exactValue (n : ℕ) :=
      setup.commitRecovery_normalized_failed_conditional_value_eq
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n) (values n) (sequence n) (prescribed n)
        utility excludedPayoff setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        focal site failed (PMF.pure choice) (PMF.pure ref.val)
        (by
          change (PMF.pure choice).map missed = (PMF.pure ref.val).map missed
          simp only [PMF.pure_map, nonmissing, refMissed])
    exact tendsto_nhds_unique (value _ _ (pureConverges choice))
      ((value _ _ (pureConverges ref.val)).congr'
        (Eventually.of_forall fun n => (exactValue n).symm))
  have nonmissing (choice : setup.commitRecoveryModel.Choice focal site.1)
      (supported : choice ∈ (limit.strategy focal site.1).support) : missed choice = false := by
    have member : missed choice ∈ ((limit.strategy focal site.1).map missed).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨choice, supported, rfl⟩
    rw [retained, PMF.mem_support_pure_iff] at member
    exact member
  have baseline :
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value (limit.strategy focal) =
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value ((limit.strategy focal).commit site.1 ref.val) := by
    have mixture := limit.continuationContext_withLaw_eq_expect
      (setup.commitRecoveryModel.decisionRecall_of_perfectRecall
        setup.commitRecoveryModel_perfectRecall).actsOnceWhereItMatters
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal)
      (limit.strategy focal site.1) payoff
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at mixture
    rw [mixture]
    calc
      _ = expect (limit.strategy focal site.1) (fun _ =>
          (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
            payoff).value ((limit.strategy focal).commit site.1 ref.val)) := by
        apply expect_congr_on_support
        intro choice supported
        exact equal choice (nonmissing choice supported)
      _ = _ := expect_constant _ _
  rw [limit.continuationContext_withLaw_eq_expect
    (setup.commitRecoveryModel.decisionRecall_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall).actsOnceWhereItMatters
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal) law]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro choice _supported
  by_cases keeps : missed choice = false
  · exact (equal choice keeps).le.trans baseline.ge
  · have fails : ¬ setup.CommitRecoveryContinues focal site.1 choice.val := by
      intro continued
      cases selected : choice.val with
      | none =>
          exact keeps (by simp only [missed, selected, CommitRecoveryMove.missed, Option.elim_none])
      | some move =>
          apply keeps
          simpa only [missed, selected, CommitRecoveryMove.missed, Option.elim_some] using
            (continued move selected).1
    rw [setup.commitRecovery_voluntaryFailure_context_value limit focal site choice fails
      utility excludedPayoff]
    exact setup.commitRecovery_conditional_value_lower limit utility excludedPayoff below
      focal site (limit.strategy focal)

end Vegas.SourceProgram.Setup

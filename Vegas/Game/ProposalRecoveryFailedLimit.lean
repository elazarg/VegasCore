/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryFailedContext
import Vegas.Game.ProposalRecoveryVoluntaryFailurePayoff
import GameTheory.Analysis.Protocol.SequentialLimits

/-! # Rationality at known-failed sites of the same enriched source limit -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- Every raw one-site law is unprofitable at a known-failed site of the SAME
source assessment limit. Actual nonmissing indifference and the prescribed
vanishing omission law suffice; neither Bayes nor a representative is assumed. -/
theorem proposalRecovery_normalized_failed_limit_localOptimal
    [Finite setup.proposalRecoveryProtocol.History]
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
          (delivery n) (deliveryNonnegative n) (deliveryBounded n) (values n) who
            (setup.proposalRecoveryModel.infoOf who history.trace))
    (omissionVanishes : Tendsto omission atTop (nhds 0))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (failed : ∀ history : setup.proposalRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧ first.NewFailure)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let _ := Fintype.ofFinite setup.proposalRecoveryProtocol.History
  let missed := fun choice : setup.proposalRecoveryModel.Choice focal site.1 =>
    CommitRecoveryMove.missed (choice.val.map (·.semantic))
  obtain ⟨history, running, action, offered⟩ := site.property
  have active : setup.proposalRecoveryActive focal site.1.1.1 := offered.1
  have omissionLaw (n : ℕ) : ((sequence n).strategy focal site.1).map missed =
      mix (omission n) (omissionNonnegative n) (omissionBounded n)
        (PMF.pure true) (PMF.pure false) := by
    have actual := prescribed n focal history.1 running
    rw [history.property] at actual
    rw [actual, setup.proposalRecoveryNormalizedTrembledProfile_missed_law
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
      (values n) focal site.1 committing,
      ite_eq_left active]
  have retained : (limit.strategy focal site.1).map missed = PMF.pure false := by
    have flags := pmfConvergesPointwise_mix_zero omission omissionNonnegative omissionBounded
      omissionVanishes (PMF.pure true) (PMF.pure false)
    exact ((converges.strategy focal site).map missed).unique
      (by simpa only [omissionLaw] using flags)
  let domain := (setup.commitRecoveryValueChoice_nonempty focal
    (setup.proposalRecoveryEraseInfo focal site.1)).some
  let ref := setup.proposalRecoveryLabelChoice focal site.1 false domain.val
  have refMissed : missed ref = false := by
    change CommitRecoveryMove.missed ((domain.val.val.map
      (fun move => ProposalRecoveryMove.label move false)).map (·.semantic)) = false
    simp only [Option.map_map, Function.comp_def, ProposalRecoveryMove.label_semantic]
    cases selected : domain.val.val with
    | none => rfl
    | some move =>
        simpa only [selected, Option.map_some, CommitRecoveryMove.missed, Option.elim_some] using
          (domain.property move selected).1
  let payoff := setup.proposalRecoveryPayoff utility excludedPayoff focal
  let total := ∑ final : setup.proposalRecoveryProtocol.History, |payoff final|
  have totalBound (final : setup.proposalRecoveryProtocol.History) : |payoff final| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ final)
  have value (replacement : ℕ → setup.proposalRecoveryModel.BehavioralPolicy focal)
      (policy : setup.proposalRecoveryModel.BehavioralPolicy focal)
      (policies : ∀ decision : setup.proposalRecoveryModel.InformationSite focal,
        PMFConvergesPointwise (fun n => replacement n decision.1) (policy decision.1)) :=
    setup.proposalRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal site (converges.belief focal site)
      policies payoff total
      ((abs_nonneg _).trans (totalBound setup.proposalRecoveryProtocol.initHistory))
      (fun final _ => totalBound final)
  have pureConverges (choice : setup.proposalRecoveryModel.Choice focal site.1)
      (decision : setup.proposalRecoveryModel.InformationSite focal) :
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
  have equal (choice : setup.proposalRecoveryModel.Choice focal site.1)
      (nonmissing : missed choice = false) :
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value ((limit.strategy focal).commit site.1 choice) =
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value ((limit.strategy focal).commit site.1 ref) := by
    have exactValue (n : ℕ) :=
      setup.proposalRecovery_normalized_failed_conditional_value_eq
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
        (values n) (sequence n) (prescribed n)
        utility excludedPayoff setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        focal site failed (PMF.pure choice) (PMF.pure ref)
        (by
          change (PMF.pure choice).map missed = (PMF.pure ref).map missed
          simp only [PMF.pure_map, nonmissing, refMissed])
    exact tendsto_nhds_unique (value _ _ (pureConverges choice))
      ((value _ _ (pureConverges ref)).congr'
        (Eventually.of_forall fun n => (exactValue n).symm))
  have nonmissing (choice : setup.proposalRecoveryModel.Choice focal site.1)
      (supported : choice ∈ (limit.strategy focal site.1).support) : missed choice = false := by
    have member : missed choice ∈ ((limit.strategy focal site.1).map missed).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨choice, supported, rfl⟩
    rw [retained, PMF.mem_support_pure_iff] at member
    exact member
  have baseline :
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value (limit.strategy focal) =
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        payoff).value ((limit.strategy focal).commit site.1 ref) := by
    have mixture := limit.continuationContext_withLaw_eq_expect
      (setup.proposalRecoveryModel.decisionRecall_of_perfectRecall
        setup.proposalRecoveryModel_perfectRecall).actsOnceWhereItMatters
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal)
      (limit.strategy focal site.1) payoff
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at mixture
    rw [mixture]
    calc
      _ = expect (limit.strategy focal site.1) (fun _ =>
          (limit.continuationContext
            setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
            payoff).value ((limit.strategy focal).commit site.1 ref)) := by
        apply expect_congr_on_support
        intro choice supported
        exact equal choice (nonmissing choice supported)
      _ = _ := expect_constant _ _
  rw [limit.continuationContext_withLaw_eq_expect
    (setup.proposalRecoveryModel.decisionRecall_of_perfectRecall
      setup.proposalRecoveryModel_perfectRecall).actsOnceWhereItMatters
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal) law]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro choice _supported
  by_cases keeps : missed choice = false
  · exact (equal choice keeps).le.trans baseline.ge
  · have fails : ¬ setup.CommitRecoveryContinues focal
        (setup.proposalRecoveryEraseInfo focal site.1) (choice.val.map (·.semantic)) := by
      intro continued
      cases selected : choice.val.map (·.semantic) with
      | none =>
          exact keeps (by simp only [missed, selected, CommitRecoveryMove.missed, Option.elim_none])
      | some move =>
          apply keeps
          simpa only [missed, selected, CommitRecoveryMove.missed, Option.elim_some] using
            (continued move selected).1
    rw [setup.proposalRecovery_voluntaryFailure_context_value limit focal site choice fails
      utility excludedPayoff]
    exact setup.proposalRecovery_conditional_value_lower limit utility excludedPayoff below
      focal site (limit.strategy focal)

end Vegas.SourceProgram.Setup

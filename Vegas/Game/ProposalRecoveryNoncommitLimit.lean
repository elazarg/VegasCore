/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryCommitLimit
import Vegas.Game.CommitRecoveryOpeningMass

/-! # Truthful publication and full rationality at enriched noncommitment sites -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

variable (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
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
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (deliveryVanishes : Tendsto delivery atTop (nhds 0))

include converges prescribed omissionVanishes deliveryVanishes

open Classical in
omit [Fintype Player] in
theorem proposalRecovery_normalized_noncommit_limit_choice
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (notCommit : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = false) :
    ∃ chosen : setup.CommitRecoveryValueChoice focal
        (setup.proposalRecoveryQuery focal site.1).1,
      limit.strategy focal site.1 = PMF.pure
        ((setup.proposalRecoveryComponentChoice focal site.1).symm
          (setup.proposalRecoveryComponentLabelChoice focal
            (setup.proposalRecoveryQuery focal site.1) false chosen.val)) := by
  let query := setup.proposalRecoveryQuery focal site.1
  let old := setup.proposalRecoveryEraseInfo focal site.1
  have oldNotCommit : old.1.1.1.elim false
      (ProtocolView.atCommit focal setup.program) = false := notCommit
  have unchanged : setup.commitRecoveryNoMissInformation focal old = old := by
    simp only [commitRecoveryNoMissInformation, oldNotCommit, Bool.false_eq_true,
      false_and, ite_false]
  have queryNotCommit : query.1.1.1.1.elim false
      (ProtocolView.atCommit focal setup.program) = false := by
    change ((setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal old)).1.1.1).elim false _ = false
    rw [unchanged]
    change (old.1.1.1.map (ProtocolView.eraseHistory focal setup.program)).elim false _ = false
    cases current : old.1.1.1 with
    | none => rfl
    | some view =>
        simpa only [current, Option.map_some, Option.elim_some,
          ProtocolView.atCommit_eraseHistory] using oldNotCommit
  let chosen := (setup.commitRecoveryValueChoice_nonempty focal query.1).some
  have continues : setup.CommitRecoveryContinues focal query.1 chosen.val.val := by
    intro move selected
    exact ⟨(chosen.property move selected).1, fun _ => (chosen.property move selected).2⟩
  have domainLaw (n : ℕ) : (values n focal query).map Subtype.val = PMF.pure chosen.val := by
    calc
      _ = (values n focal query).map (fun _ => chosen.val) := by
        apply congrArg (PMF.map · (values n focal query))
        funext choice
        exact setup.continuing_noncommit_unique focal query.1 queryNotCommit choice.val chosen.val
          (fun move selected => ⟨(choice.property move selected).1,
            fun _ => (choice.property move selected).2⟩) continues
      _ = _ := PMF.map_const _ _
  let failure := setup.commitRecoveryFailureChoice focal query.1 true
  have semantic (n : ℕ) : setup.commitRecoveryValueTremble focal query.1
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n focal query) =
      mix (omission n) (omissionNonnegative n) (omissionBounded n)
        (PMF.pure failure) (PMF.pure chosen.val) := by
    rw [commitRecoveryValueTremble, queryNotCommit]
    simp only [Bool.false_eq_true, ite_false, domainLaw]
    rfl
  have semanticLimit := pmfConvergesPointwise_mix_zero omission omissionNonnegative omissionBounded
    omissionVanishes (PMF.pure failure) (PMF.pure chosen.val)
  have labelLimit := pmfConvergesPointwise_mix_zero delivery deliveryNonnegative deliveryBounded
    deliveryVanishes (PMF.pure true) (PMF.pure false)
  have result := (semanticLimit.bind (fun choice => labelLimit.map
    (fun requested => setup.proposalRecoveryComponentLabelChoice focal query requested choice))).map
      (setup.proposalRecoveryComponentChoice focal site.1).symm
  simp only [PMF.pure_bind, PMF.pure_map] at result
  refine ⟨chosen, (converges.strategy focal site).unique ?_⟩
  convert result using 1
  funext n
  obtain ⟨history, running, _offered⟩ := site.property
  have actual := prescribed n focal history.1 running
  rw [history.property] at actual
  rw [actual]
  change ((setup.proposalRecoveryComponentTrembledLaw focal query
    (omission n) (omissionNonnegative n) (omissionBounded n)
    (bad n) (badNonnegative n) (badBounded n)
    (delivery n) (deliveryNonnegative n) (deliveryBounded n) (values n focal query)).map
      (setup.proposalRecoveryComponentChoice focal site.1).symm) = _
  rw [proposalRecoveryComponentTrembledLaw, semantic]

open Classical in
/-- Extra publication clues do not erase any actual information. At this
full information site every alternative is either the unique continuing
truthful response or voluntary own exclusion at the weak global floor. -/
theorem proposalRecovery_normalized_noncommit_limit_localOptimal
    [Finite setup.proposalRecoveryProtocol.History]
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (notCommit : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = false)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  obtain ⟨domain, retained⟩ := setup.proposalRecovery_normalized_noncommit_limit_choice
    sequence limit converges omission bad delivery omissionNonnegative omissionBounded
    badNonnegative badBounded deliveryNonnegative deliveryBounded values prescribed
    omissionVanishes deliveryVanishes focal site notCommit
  let semantic := (setup.commitRecoveryNoMissErasedChoice focal
    (setup.proposalRecoveryEraseInfo focal site.1)).symm domain.val
  let chosen := setup.proposalRecoveryLabelChoice focal site.1 false semantic
  have sameChosen : chosen = (setup.proposalRecoveryComponentChoice focal site.1).symm
      (setup.proposalRecoveryComponentLabelChoice focal
        (setup.proposalRecoveryQuery focal site.1) false domain.val) := rfl
  have continues : setup.CommitRecoveryContinues focal
      (setup.proposalRecoveryEraseInfo focal site.1) semantic.val := by
    intro move selected
    exact ⟨(domain.property move selected).1, fun _ => (domain.property move selected).2⟩
  have baseline : (limit.strategy focal).commit site.1 chosen = limit.strategy focal := by
    funext information
    by_cases same : information = site.1
    · subst information
      rw [InformationModel.BehavioralPolicy.commit_self, retained, sameChosen]
    · rw [InformationModel.BehavioralPolicy.commit_of_ne _ _ _ same]
  rw [limit.continuationContext_withLaw_eq_expect
    (setup.proposalRecoveryModel.decisionRecall_of_perfectRecall
      setup.proposalRecoveryModel_perfectRecall).actsOnceWhereItMatters
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal) law]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro choice _supported
  by_cases keeps : setup.CommitRecoveryContinues focal
      (setup.proposalRecoveryEraseInfo focal site.1) (choice.val.map (·.semantic))
  · have currentNotCommit : (setup.proposalRecoveryEraseInfo focal site.1).1.1.1.elim false
        (ProtocolView.atCommit focal setup.program) = false := notCommit
    have sameSemantic := setup.continuing_noncommit_unique focal _ currentNotCommit
      (setup.proposalRecoverySemanticChoice focal site.1 choice) semantic keeps continues
    have reconstruct := setup.proposalRecovery_domain_label_reconstruct focal site.1 choice
      (fun move selected => (keeps move selected).2 currentNotCommit)
    have same : choice = chosen := reconstruct.symm.trans
      (congrArg (setup.proposalRecoveryLabelChoice focal site.1 false) sameSemantic)
    rw [same, baseline]
  · rw [setup.proposalRecovery_voluntaryFailure_context_value limit focal site choice keeps
      utility excludedPayoff]
    exact setup.proposalRecovery_conditional_value_lower limit utility excludedPayoff below
      focal site (limit.strategy focal)

end Vegas.SourceProgram.Setup

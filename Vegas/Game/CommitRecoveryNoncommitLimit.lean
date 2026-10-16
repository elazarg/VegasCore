/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryOpeningMass
import Vegas.Game.CommitRecoveryFailedLimit

/-! # Full raw limit rationality at noncommitment source decisions -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

section Prescription

variable (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
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

include converges prescribed omissionVanishes

open Classical in
omit [Fintype Player] in
/-- A genuine noncommitment decision has its unique domain action with
probability one in the SAME normalized source limit. Only omission vanishes;
no convergence of the arbitrary domain coordinates is assumed. -/
theorem commitRecovery_normalized_noncommit_limit_choice
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (notCommit : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = false) :
    ∃ chosen : setup.CommitRecoveryValueChoice focal site.1,
      limit.strategy focal site.1 = PMF.pure chosen.val := by
  let chosen := (setup.commitRecoveryValueChoice_nonempty focal site.1).some
  have continues : setup.CommitRecoveryContinues focal site.1 chosen.val.val := by
    intro move selected
    exact ⟨(chosen.property move selected).1, fun _ => (chosen.property move selected).2⟩
  let query := setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal site.1)
  have unchanged : setup.commitRecoveryNoMissInformation focal site.1 = site.1 := by
    simp only [commitRecoveryNoMissInformation, notCommit, Bool.false_eq_true,
      false_and, ite_false]
  have queryNotCommit : query.1.1.1.elim false
      (ProtocolView.atCommit focal setup.program) = false := by
    dsimp only [query]
    rw [unchanged]
    change (site.1.1.1.1.map (ProtocolView.eraseHistory focal setup.program)).elim false
      (ProtocolView.atCommit focal setup.program) = false
    cases current : site.1.1.1.1 with
    | none => rfl
    | some view =>
        simpa only [current, Option.map_some, Option.elim_some,
          ProtocolView.atCommit_eraseHistory] using notCommit
  let failure := (setup.commitRecoveryNoMissErasedChoice focal site.1).symm
    (setup.commitRecoveryFailureChoice focal query true)
  have domainRaw (n : ℕ) : ((values n focal query).map (fun choice => choice.val.val)) =
      PMF.pure chosen.val.val := by
    calc
      _ = (values n focal query).map (fun _ => chosen.val.val) := by
        apply congrArg (PMF.map · (values n focal query))
        funext choice
        let actual := (setup.commitRecoveryNoMissErasedChoice focal site.1).symm choice.val
        have safe : setup.CommitRecoveryContinues focal site.1 actual.val := by
          intro move selected
          exact ⟨(choice.property move selected).1, fun _ => (choice.property move selected).2⟩
        exact congrArg Subtype.val
          (setup.continuing_noncommit_unique focal site.1 notCommit actual chosen.val
            safe continues)
      _ = _ := PMF.map_const _ _
  have actual (n : ℕ) : (sequence n).strategy focal site.1 =
      mix (omission n) (omissionNonnegative n) (omissionBounded n)
        (PMF.pure failure) (PMF.pure chosen.val) := by
    obtain ⟨history, running, _offered⟩ := site.property
    have prescription := prescribed n focal history.1 running
    rw [history.property] at prescription
    apply pmf_map_injective Subtype.val_injective
    rw [prescription, commitRecoveryNormalizedTrembledProfile,
      setup.commitRecoveryNoMissErasedProfile_raw]
    change (setup.commitRecoveryValueTremble focal query
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n) (values n focal query)).map Subtype.val = _
    rw [commitRecoveryValueTremble, queryNotCommit]
    simp only [Bool.false_eq_true, ↓reduceIte, mix_map, PMF.pure_map,
      PMF.map_comp, Function.comp_def]
    change mix (omission n) (omissionNonnegative n) (omissionBounded n)
      (PMF.pure (setup.commitRecoveryFailureChoice focal query true).val)
      ((values n focal query).map (fun choice => choice.val.val)) = _
    rw [domainRaw n]
    rfl
  refine ⟨chosen, (converges.strategy focal site).unique ?_⟩
  simpa only [actual] using pmfConvergesPointwise_mix_zero omission omissionNonnegative
    omissionBounded omissionVanishes (PMF.pure failure) (PMF.pure chosen.val)

open Classical in
/-- Every raw local lottery is unprofitable at any noncommitment decision
of the actual normalized limit. Withholding pays the global floor and the
unique continuing action is played surely. -/
theorem commitRecovery_normalized_noncommit_limit_localOptimal
    [Finite setup.commitRecoveryProtocol.History]
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (notCommit : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = false)
    (law : PMF (setup.commitRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  obtain ⟨chosen, retained⟩ := setup.commitRecovery_normalized_noncommit_limit_choice sequence limit
    converges omission bad omissionNonnegative omissionBounded badNonnegative badBounded values
    prescribed omissionVanishes focal site notCommit
  have continues : setup.CommitRecoveryContinues focal site.1 chosen.val.val := by
    intro move selected
    exact ⟨(chosen.property move selected).1, fun _ => (chosen.property move selected).2⟩
  have baseline : (limit.strategy focal).commit site.1 chosen.val = limit.strategy focal := by
    funext info
    by_cases same : info = site.1
    · subst info
      rw [InformationModel.BehavioralPolicy.commit_self, retained]
    · rw [InformationModel.BehavioralPolicy.commit_of_ne _ _ _ same]
  rw [limit.continuationContext_withLaw_eq_expect
    (setup.commitRecoveryModel.decisionRecall_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall).actsOnceWhereItMatters
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal) law]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro choice _supported
  by_cases keeps : setup.CommitRecoveryContinues focal site.1 choice.val
  · have same := setup.continuing_noncommit_unique focal site.1 notCommit choice chosen.val
      keeps continues
    rw [same, baseline]
  · rw [setup.commitRecovery_voluntaryFailure_context_value limit focal site choice keeps
      utility excludedPayoff]
    exact setup.commitRecovery_conditional_value_lower limit utility excludedPayoff below
      focal site (limit.strategy focal)

end Prescription
end Vegas.SourceProgram.Setup

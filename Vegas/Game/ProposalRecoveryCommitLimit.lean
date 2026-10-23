/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryRawLimit
import Vegas.Game.ProposalRecoveryVoluntaryFailurePayoff
import Vegas.Source.ProposalRecoveryOrdinaryCommit

/-! # Every legal commitment lottery at the common enriched source limit -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem proposalRecovery_domain_label_reconstruct (focal : Player)
    (information : setup.proposalRecoveryModel.InfoState focal)
    (choice : setup.proposalRecoveryModel.Choice focal information)
    (domain : ∀ move, choice.val.map (·.semantic) = some move → ¬ move.action.IsFailure) :
    setup.proposalRecoveryLabelChoice focal information false
      (setup.proposalRecoverySemanticChoice focal information choice) = choice := by
  apply Subtype.ext
  change (choice.val.map (·.semantic)).map
    (fun move => ProposalRecoveryMove.label move false) = choice.val
  have valid := ((setup.proposalRecoveryMenu_semantic focal information choice.val).mp
    choice.property).2
  cases selected : choice.val with
  | none => rfl
  | some move =>
      simp only [selected, Option.elim_some] at valid
      have absent : move.proposed = false := by
        apply Bool.eq_false_iff.mpr
        intro proposed
        obtain ⟨owner, name, revealing⟩ := valid proposed
        apply domain move.semantic (by simp only [selected, Option.map_some])
        rw [revealing]
        rfl
      simp only [Option.map_some, ProposalRecoveryMove.label_false]
      cases move with
      | mk semantic proposed => cases absent; rfl

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
/-- The actual accepted-failure comparison and weak floor extend ordinary
domain rationality to EVERY original enriched current-action lottery. -/
theorem proposalRecovery_normalized_limit_localOptimal_of_domain
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (domainOptimal : ∀ domain : PMF (setup.CommitRecoveryValueChoice focal
        (setup.proposalRecoveryEraseInfo focal site.1)),
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          ((limit.strategy focal).withLaw site.1 (domain.map (fun choice =>
            setup.proposalRecoveryLabelChoice focal site.1 false choice.val))) ≤
        (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
          (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value (limit.strategy focal))
    (law : PMF (setup.proposalRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let _ : Finite setup.proposalRecoveryProtocol.History :=
    setup.proposalRecovery_finite_history finite
  let _ := setup.proposalRecovery_finite_choice finite focal site.1
  rw [limit.continuationContext_withLaw_eq_expect
    (setup.proposalRecoveryModel.decisionRecall_of_perfectRecall
      setup.proposalRecoveryModel_perfectRecall).actsOnceWhereItMatters
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site (limit.strategy focal) law]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro choice _supported
  by_cases continues : setup.CommitRecoveryContinues focal
      (setup.proposalRecoveryEraseInfo focal site.1) (choice.val.map (·.semantic))
  · by_cases ordinary : ∀ move, choice.val.map (·.semantic) = some move →
        ¬ move.action.IsFailure
    · let domain : setup.CommitRecoveryValueChoice focal
          (setup.proposalRecoveryEraseInfo focal site.1) :=
        ⟨setup.proposalRecoverySemanticChoice focal site.1 choice,
          fun move selected => ⟨(continues move selected).1, ordinary move selected⟩⟩
      have optimal := domainOptimal (PMF.pure domain)
      have same := setup.proposalRecovery_domain_label_reconstruct focal site.1 choice ordinary
      simp only [PMF.pure_map, domain, same] at optimal
      convert optimal using 1
      rfl
    · push Not at ordinary
      obtain ⟨move, selected, failed⟩ := ordinary
      let domain := (setup.commitRecoveryValueChoice_nonempty focal
        (setup.proposalRecoveryEraseInfo focal site.1)).some
      let reference := PMF.pure
        (setup.proposalRecoveryLabelChoice focal site.1 false domain.val)
      have dominates := setup.proposalRecovery_normalized_limit_accepted_failure_le finite
        sequence limit converges omission bad delivery omissionNonnegative omissionBounded
        badNonnegative badBounded deliveryNonnegative deliveryBounded values prescribed
        utility excludedPayoff below focal site committing choice
        ⟨move, selected, failed, (continues move selected).1⟩ reference (by
          intro chosen member
          have same := (PMF.mem_support_pure_iff _ _).mp member
          subst chosen
          change CommitRecoveryMove.missed
            ((domain.val.val.map (fun move => ProposalRecoveryMove.label move false)).map
              (·.semantic)) = false
          simp only [Option.map_map, Function.comp_def, ProposalRecoveryMove.label_semantic]
          cases selected : domain.val.val with
          | none => rfl
          | some move =>
              simpa only [selected, Option.map_some, CommitRecoveryMove.missed,
                Option.elim_some] using
                (domain.property move selected).1)
      have optimal := domainOptimal (PMF.pure domain)
      have result := dominates.trans (by simpa only [PMF.pure_map] using optimal)
      convert result using 1
      rfl
  · rw [setup.proposalRecovery_voluntaryFailure_context_value limit focal site choice continues
      utility excludedPayoff]
    exact setup.proposalRecovery_conditional_value_lower limit utility excludedPayoff below
      focal site (limit.strategy focal)

end Vegas.SourceProgram.Setup

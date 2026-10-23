/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryRawLimit

/-! # Actual enriched action vectors at ordinary copies of the common limit -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

variable (finite : setup.program.FiniteBindingTypes)
  [Finite setup.proposalRecoveryProtocol.History]
  (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
  (limit : setup.proposalRecoveryModel.BehavioralAssessment)
  (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
  (mixed : ∀ n, (sequence n).IsFullyMixed)
  (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
    setup.proposalRecoveryModel (sequence n) setup.proposalRecoveryModel_decisionAntichain)
  (prescription : ℕ → (who : Player) → setup.ProposalRecoveryPrescription who)
  (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
    (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
    (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
      setup.proposalRecoveryPrescribedProfile (prescription n) who
        (setup.proposalRecoveryModel.infoOf who history.trace))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)

include finite converges mixed bayes prescribed

open Classical in
/-- Exact finite-stage Bayes action vectors pass to the SAME assessment
limit. The two replacement laws agree as literal raw actions; both actual
original beliefs and all later source choices remain in the comparison. -/
theorem proposalRecovery_normalized_limit_gain_eq
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1)
    (sourceLaw : PMF (setup.proposalRecoveryModel.Choice focal source.1))
    (targetLaw : PMF (setup.proposalRecoveryModel.Choice focal target.1))
    (raw : sourceLaw.map Subtype.val = targetLaw.map Subtype.val) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw source.1 sourceLaw) -
      (limit.continuationContext
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value (limit.strategy focal) =
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories target
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw target.1 targetLaw) -
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories target
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let _ := Fintype.ofFinite setup.proposalRecoveryProtocol.History
  have keys : setup.proposalRecoveryQuery focal target.1 =
      setup.proposalRecoveryQuery focal source.1 := by
    apply Prod.ext _ archive
    dsimp only [proposalRecoveryQuery]
    rw [setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased, semantic]
  let law := sourceLaw.map (setup.proposalRecoveryComponentChoice focal source.1)
  let changed := fun n => setup.proposalRecoveryPrescribedProfile
    (Profile.update (sig := setup.proposalRecoveryPrescriptionSignature) (prescription n) focal
      (setup.proposalRecoveryPrescriptionWithLaw focal (prescription n focal)
        (setup.proposalRecoveryQuery focal source.1) law))
  have sourceAt (n : ℕ) : changed n focal source.1 = sourceLaw := by
    apply pmf_map_injective Subtype.val_injective
    rw [setup.proposalRecoveryPrescribedProfile_raw, Profile.update_same,
      setup.proposalRecoveryPrescriptionWithLaw_self]
    dsimp only [law]
    rw [PMF.map_comp]
    rfl
  have targetAt (n : ℕ) : changed n focal target.1 = targetLaw := by
    apply pmf_map_injective Subtype.val_injective
    rw [setup.proposalRecoveryPrescribedProfile_raw, Profile.update_same, keys,
      setup.proposalRecoveryPrescriptionWithLaw_self]
    dsimp only [law]
    rw [PMF.map_comp]
    exact raw
  have equal (n : ℕ) := setup.proposalRecovery_conditional_gain_eq finite (sequence n)
    (mixed n) (bayes n) (prescription n) (prescribed n) utility excludedPayoff
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories focal target source
    semantic archive law
  dsimp only at equal
  have sourceEq (n : ℕ) := sourceAt n
  have targetEq (n : ℕ) := targetAt n
  dsimp only [changed] at sourceEq targetEq
  simp only [sourceEq, targetEq] at equal
  let payoff := setup.proposalRecoveryPayoff utility excludedPayoff focal
  let total := ∑ history : setup.proposalRecoveryProtocol.History, |payoff history|
  have totalBound (history : setup.proposalRecoveryProtocol.History) : |payoff history| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ history)
  have value (site : setup.proposalRecoveryModel.InformationSite focal)
      (replacement : ℕ → setup.proposalRecoveryModel.BehavioralPolicy focal)
      (policy : setup.proposalRecoveryModel.BehavioralPolicy focal)
      (policies : ∀ decision : setup.proposalRecoveryModel.InformationSite focal,
        PMFConvergesPointwise (fun n => replacement n decision.1) (policy decision.1)) :=
    setup.proposalRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal site (converges.belief focal site)
      policies payoff total
      ((abs_nonneg _).trans (totalBound setup.proposalRecoveryProtocol.initHistory))
      (fun final _ => totalBound final)
  have installed (site : setup.proposalRecoveryModel.InformationSite focal)
      (law : PMF (setup.proposalRecoveryModel.Choice focal site.1))
      (decision : setup.proposalRecoveryModel.InformationSite focal) :
      PMFConvergesPointwise
        (fun n => ((sequence n).strategy focal).withLaw site.1 law decision.1)
        (((limit.strategy focal).withLaw site.1 law) decision.1) := by
    by_cases same : decision.1 = site.1
    · have equal : decision = site := Subtype.ext same
      subst decision
      simpa only [InformationModel.BehavioralPolicy.withLaw_self] using
        pmfConvergesPointwise_const law
    · simpa only [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ same] using
        converges.strategy focal decision
  have left := (value source _ _ (installed source sourceLaw)).sub
    (value source _ _ (converges.strategy focal))
  have right := (value target _ _ (installed target targetLaw)).sub
    (value target _ _ (converges.strategy focal))
  exact tendsto_nhds_unique left (right.congr' (Eventually.of_forall fun n => (equal n).symm))

open Classical in
/-- A genuine selected-site optimum transports to every actual ordinary
copy with the same fixed controls and archive, including zero limiting reach. -/
theorem proposalRecovery_normalized_limit_localOptimal_of_erased_copy
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1)
    (sourceOptimal : ∀ law : PMF (setup.proposalRecoveryModel.Choice focal source.1),
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          ((limit.strategy focal).withLaw source.1 law) ≤
        (limit.continuationContext
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
          (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value (limit.strategy focal))
    (law : PMF (setup.proposalRecoveryModel.Choice focal target.1)) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories target
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw target.1 law) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories target
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  have menus : setup.commitRecoveryModel.menu focal
      (setup.proposalRecoveryEraseInfo focal target.1) = setup.commitRecoveryModel.menu focal
        (setup.proposalRecoveryEraseInfo focal source.1) := by
    rw [← setup.commitRecoveryErasedInformation_menu focal
      (setup.proposalRecoveryEraseInfo focal target.1), semantic,
      setup.commitRecoveryErasedInformation_menu]
  let toSource : setup.proposalRecoveryModel.Choice focal target.1 →
      setup.proposalRecoveryModel.Choice focal source.1 := fun choice => ⟨choice.val, by
    apply (setup.proposalRecoveryMenu_semantic focal source.1 choice.val).mpr
    have allowed := (setup.proposalRecoveryMenu_semantic focal target.1 choice.val).mp
      choice.property
    constructor
    · change (choice.val.map (·.semantic)) ∈ setup.commitRecoveryModel.menu focal
        (setup.proposalRecoveryEraseInfo focal source.1)
      rw [← menus]
      exact allowed.1
    · exact allowed.2⟩
  have raw : (law.map toSource).map Subtype.val = law.map Subtype.val := by
    rw [PMF.map_comp]
    rfl
  have gain := setup.proposalRecovery_normalized_limit_gain_eq finite sequence limit converges
    mixed bayes prescription prescribed utility excludedPayoff focal target source
    semantic archive (law.map toSource) law raw
  have optimal := sourceOptimal (law.map toSource)
  linarith

end Vegas.SourceProgram.Setup

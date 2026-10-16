/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryAncillaryGains
import Vegas.Game.CommitRecoveryPooledCompletion

/-! # Exact ordinary gains of the actual pooled source components

The component lotteries in the actual completion inequality are read at
one shared genuine query. Their assessed gains agree across ordinary erased
copies, and their entire ordinary-class sum is the cardinality times that
same original conditional gain. No zero-gain assertion for failed attachments
is used here.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
omit [Fintype Player] in
private theorem updated_at_query
    (profile alternate : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (first second : setup.commitRecoveryModel.InfoState focal)
    (same : setup.commitRecoveryErasedInformation focal first =
      setup.commitRecoveryErasedInformation focal second) :
    let query := setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal second)
    let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      profile focal ((profile focal).withLaw query (alternate focal query))
    setup.commitRecoveryNoMissErasedProfile updated focal first =
      setup.commitRecoveryNoMissErasedProfile alternate focal first := by
  classical
  dsimp only
  apply pmf_map_injective Subtype.val_injective
  rw [setup.commitRecoveryNoMissErasedProfile_raw, setup.commitRecoveryNoMissErasedProfile_raw]
  have keys : setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal first) =
    setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal second) := by
    rw [setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased, same]
  rw [Profile.update_same, keys, InformationModel.BehavioralPolicy.withLaw_self]

section Components

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  [Fintype setup.commitRecoveryProtocol.History]
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (mixed : assessment.IsFullyMixed)
  (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
    setup.commitRecoveryModel assessment setup.commitRecoveryModel_decisionAntichain)
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
  (pins : (pool : setup.CommitRecoveryValuePool finite) →
    Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
  (weights alternative : (pool : setup.CommitRecoveryValuePool finite) →
    PMF (setup.CommitRecoveryPoolPart finite pool))
  (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
    (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
    assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
      setup.commitRecoveryNormalizedTrembledProfile
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
          pins weights) who (setup.commitRecoveryModel.infoOf who history.trace))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)

include mixed bayes weights prescribed

open Classical in
/-- The actual alternative component lotteries have equal original assessed
conditional gains at ordinary erased copies. The profile prescription is the
actual completion output; the local law is its actual component bind. -/
theorem commitRecovery_pooled_component_gain_eq
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1) :
    let component := setup.commitRecoveryPoolComponent finite
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins
    let gain := fun site : setup.commitRecoveryModel.InformationSite focal =>
      (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw site.1
          ((alternative (setup.commitRecoveryAgentPool finite
            (setup.commitRecoveryModel.agentAt site))).bind
            (component (setup.commitRecoveryModel.agentAt site)))) -
      (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        (assessment.strategy focal)
    gain source = gain target := by
  classical
  dsimp only
  let profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who := fun who info =>
    setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded
      (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        pins weights who info)
  let alternate : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who := fun who info =>
    setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded
      (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        pins alternative who info)
  let query := setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal source.1)
  let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
    profile focal ((profile focal).withLaw query (alternate focal query))
  have original : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNoMissErasedProfile profile who
          (setup.commitRecoveryModel.infoOf who history.trace) := prescribed
  have shared := setup.commitRecovery_normalized_conditional_gain_eq assessment mixed bayes
    profile original utility excludedPayoff
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories
    focal target source same (alternate focal query)
  dsimp only at shared
  have sourceAt := setup.updated_at_query profile alternate focal source.1 source.1 rfl
  have targetAt := setup.updated_at_query profile alternate focal target.1 source.1 same
  change setup.commitRecoveryNoMissErasedProfile updated focal source.1 = _ at sourceAt
  change setup.commitRecoveryNoMissErasedProfile updated focal target.1 = _ at targetAt
  rw [sourceAt, targetAt] at shared
  rw [setup.commitRecoveryPoolComponent_bind finite
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded pins alternative,
    setup.commitRecoveryPoolComponent_bind finite
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded pins alternative]
  exact shared

open Classical in
/-- The entire ordinary erased class contributes its cardinality times one
actual conditional gain to the source completion objective. This is an exact
sum over original decision sites, without reach weights or source belief
identification premises. -/
theorem commitRecovery_pooled_ordinary_gain_sum
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal) :
    let _ := Fintype.ofFinite (setup.commitRecoveryModel.InformationSite focal)
    let component := setup.commitRecoveryPoolComponent finite
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins
    let gain := fun site : setup.commitRecoveryModel.InformationSite focal =>
      (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw site.1
          ((alternative (setup.commitRecoveryAgentPool finite
            (setup.commitRecoveryModel.agentAt site))).bind
            (component (setup.commitRecoveryModel.agentAt site)))) -
      (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        (assessment.strategy focal)
    let members := (Finset.univ : Finset (setup.commitRecoveryModel.InformationSite focal)).filter
      (fun site => setup.commitRecoveryErasedInformation focal site.1 =
        setup.commitRecoveryErasedInformation focal source.1)
    ∑ site ∈ members, gain site = (members.card : ℝ) * gain source := by
  classical
  let _ := Fintype.ofFinite (setup.commitRecoveryModel.InformationSite focal)
  dsimp only
  rw [Finset.sum_eq_card_nsmul]
  · rw [nsmul_eq_mul]
  · intro site member
    exact (setup.commitRecovery_pooled_component_gain_eq finite assessment mixed bayes
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins weights alternative prescribed utility excludedPayoff
      focal site source (Finset.mem_filter.mp member).2).symm

open Classical in
/-- Nonpositivity of the actual ordinary-class contribution is equivalent
to the individual actual conditional-gain inequality. The coefficient is the
positive number of original sites, and the source site supplies membership. -/
theorem commitRecovery_pooled_ordinary_gain_nonpos_iff
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal) :
    let _ := Fintype.ofFinite (setup.commitRecoveryModel.InformationSite focal)
    let component := setup.commitRecoveryPoolComponent finite
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins
    let gain := fun site : setup.commitRecoveryModel.InformationSite focal =>
      (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw site.1
          ((alternative (setup.commitRecoveryAgentPool finite
            (setup.commitRecoveryModel.agentAt site))).bind
            (component (setup.commitRecoveryModel.agentAt site)))) -
      (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        (assessment.strategy focal)
    let members := (Finset.univ : Finset (setup.commitRecoveryModel.InformationSite focal)).filter
      (fun site => setup.commitRecoveryErasedInformation focal site.1 =
        setup.commitRecoveryErasedInformation focal source.1)
    (∑ site ∈ members, gain site ≤ 0) ↔ gain source ≤ 0 := by
  classical
  let _ := Fintype.ofFinite (setup.commitRecoveryModel.InformationSite focal)
  dsimp only
  have summed := setup.commitRecovery_pooled_ordinary_gain_sum finite assessment mixed bayes
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded pins weights alternative prescribed utility excludedPayoff
    focal source
  dsimp only at summed
  rw [summed]
  let members := (Finset.univ : Finset (setup.commitRecoveryModel.InformationSite focal)).filter
    (fun site => setup.commitRecoveryErasedInformation focal site.1 =
      setup.commitRecoveryErasedInformation focal source.1)
  have positive : (0 : ℝ) < members.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨source, by simp only [members, Finset.mem_filter,
      Finset.mem_univ, and_self]⟩)
  constructor
  · intro bound
    by_contra notNonpos
    exact (not_lt_of_ge bound) (mul_pos positive (lt_of_not_ge notNonpos))
  · exact fun bound => mul_nonpos_of_nonneg_of_nonpos positive.le bound

end Components

end Vegas.SourceProgram.Setup

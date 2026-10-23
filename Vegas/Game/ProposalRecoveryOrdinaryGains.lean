/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryOrdinaryAgents
import Vegas.Game.ProposalRecoveryGains

/-! # Actual pooled gains on the ordinary enriched information class -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
omit [Fintype Player] in
private theorem updated_at_key
    (profile alternate : ∀ who, setup.ProposalRecoveryPrescription who)
    (focal : Player) (first second : setup.proposalRecoveryModel.InfoState focal)
    (same : setup.proposalRecoveryQuery focal first =
      setup.proposalRecoveryQuery focal second) :
    let key := setup.proposalRecoveryQuery focal second
    let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
      profile focal
        (setup.proposalRecoveryPrescriptionWithLaw focal (profile focal) key (alternate focal key))
    setup.proposalRecoveryPrescribedProfile updated focal first =
      setup.proposalRecoveryPrescribedProfile alternate focal first := by
  classical
  dsimp only
  apply pmf_map_injective Subtype.val_injective
  rw [setup.proposalRecoveryPrescribedProfile_raw,
    setup.proposalRecoveryPrescribedProfile_raw]
  change ((Profile.update (sig := setup.proposalRecoveryPrescriptionSignature) profile focal
      (setup.proposalRecoveryPrescriptionWithLaw focal (profile focal)
        (setup.proposalRecoveryQuery focal second)
        (alternate focal (setup.proposalRecoveryQuery focal second))) focal
          (setup.proposalRecoveryQuery focal first)).map Subtype.val) = _
  rw [Profile.update_same, same, setup.proposalRecoveryPrescriptionWithLaw_self]

section Components

variable (finite : setup.program.FiniteBindingTypes)
  [Fintype setup.proposalRecoveryProtocol.History]
  (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
  (mixed : assessment.IsFullyMixed)
  (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
    setup.proposalRecoveryModel assessment setup.proposalRecoveryModel_decisionAntichain)
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
  (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
  (pins : (pool : setup.ProposalRecoveryValuePool) →
    Option (PMF (setup.ProposalRecoveryPoolPart pool)))
  (weights alternative : (pool : setup.ProposalRecoveryValuePool) →
    PMF (setup.ProposalRecoveryPoolPart pool))
  (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
    (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
    assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
      setup.proposalRecoveryNormalizedTrembledProfile
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded
        (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
          pins weights) who (setup.proposalRecoveryModel.infoOf who history.trace))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)

open Classical in
/-- The literal gain appearing in the actual component-completion objective. -/
def proposalRecoveryPooledGain (focal : Player)
    (site : setup.proposalRecoveryModel.InformationSite focal) : ℝ :=
  let component := setup.proposalRecoveryPoolComponent finite
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded
    floor floorNonnegative floorBounded pins
  let context := assessment.continuationContext
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
    (setup.proposalRecoveryPayoff utility excludedPayoff focal)
  context.value ((assessment.strategy focal).withLaw site.1
    ((alternative (setup.proposalRecoveryAgentPool
      (setup.proposalRecoveryModel.agentAt site))).bind
        (component (setup.proposalRecoveryModel.agentAt site)))) -
    context.value (assessment.strategy focal)

include mixed bayes weights prescribed

open Classical in
/-- Every ordinary copy has the same gain under its ORIGINAL fully mixed
Bayes assessment. The local alternatives are actual pooled component laws. -/
theorem proposalRecovery_pooled_component_gain_eq
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1) :
    setup.proposalRecoveryPooledGain finite assessment
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded floor floorNonnegative floorBounded
        pins alternative utility excludedPayoff focal source =
      setup.proposalRecoveryPooledGain finite assessment
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded floor floorNonnegative floorBounded
        pins alternative utility excludedPayoff focal target := by
  classical
  let profile : ∀ who, setup.ProposalRecoveryPrescription who := fun who key =>
    setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        pins weights who key)
  let alternate : ∀ who, setup.ProposalRecoveryPrescription who := fun who key =>
    setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
        pins alternative who key)
  have keys : setup.proposalRecoveryQuery focal target.1 =
      setup.proposalRecoveryQuery focal source.1 := by
    apply Prod.ext
    · change setup.commitRecoveryErasedInformation focal
          (setup.commitRecoveryNoMissInformation focal
            (setup.proposalRecoveryEraseInfo focal target.1)) =
        setup.commitRecoveryErasedInformation focal
          (setup.commitRecoveryNoMissInformation focal
            (setup.proposalRecoveryEraseInfo focal source.1))
      rw [setup.commitRecoveryNoMissInformation_erased,
        setup.commitRecoveryNoMissInformation_erased, semantic]
    · exact archive
  let key := setup.proposalRecoveryQuery focal source.1
  let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
    profile focal
      (setup.proposalRecoveryPrescriptionWithLaw focal (profile focal) key (alternate focal key))
  have shared := setup.proposalRecovery_conditional_gain_eq finite assessment mixed bayes
    profile prescribed utility excludedPayoff
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
    focal target source semantic archive (alternate focal key)
  dsimp only at shared
  have sourceAt := setup.updated_at_key profile alternate focal source.1 source.1 rfl
  have targetAt := setup.updated_at_key profile alternate focal target.1 source.1 keys
  change setup.proposalRecoveryPrescribedProfile updated focal source.1 = _ at sourceAt
  change setup.proposalRecoveryPrescribedProfile updated focal target.1 = _ at targetAt
  rw [sourceAt, targetAt] at shared
  unfold proposalRecoveryPooledGain
  dsimp only
  rw [setup.proposalRecoveryPoolComponent_bind finite
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded floor floorNonnegative floorBounded
      pins alternative,
    setup.proposalRecoveryPoolComponent_bind finite
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded floor floorNonnegative floorBounded
      pins alternative]
  exact shared

end Components

end Vegas.SourceProgram.Setup

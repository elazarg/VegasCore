/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryOrdinaryGains
import Vegas.Game.ProposalRecoveryFailedContext

/-! # The full original component objective and its ordinary contribution -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

omit [Fintype Player] [Fintype setup.proposalRecoveryProtocol.History] in
private theorem current_private (who : Player) {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryModel.infoOf who trace).1.1.1 =
      setup.commitRecoveryPrivate who state := by
  exact congrArg Prod.fst (setup.proposalRecoveryEraseInfo_current who trace)

variable (finite : setup.program.FiniteBindingTypes)
  (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
  (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
  (pins : (pool : setup.ProposalRecoveryValuePool) →
    Option (PMF (setup.ProposalRecoveryPoolPart pool)))
  (alternative : (pool : setup.ProposalRecoveryValuePool) →
    PMF (setup.ProposalRecoveryPoolPart pool))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)

open Classical in
/-- The literal conditional-gain summand of the existing source completion,
including the zero branch for original inactive information agents. -/
def proposalRecoveryComponentGain
    (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation) : ℝ :=
  if decision : setup.proposalRecoveryModel.IsDecisionInfo agent.1 agent.2.val then
    (assessment.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      ⟨agent.2.val, decision⟩ (setup.proposalRecoveryPayoff utility excludedPayoff agent.1)).value
      ((assessment.strategy agent.1).withLaw agent.2.val
        ((alternative (setup.proposalRecoveryAgentPool agent)).bind
          (setup.proposalRecoveryPoolComponent finite
            omission omissionNonnegative omissionBounded bad badNonnegative badBounded
            delivery deliveryNonnegative deliveryBounded
            floor floorNonnegative floorBounded pins agent))) -
    (assessment.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      ⟨agent.2.val, decision⟩ (setup.proposalRecoveryPayoff utility excludedPayoff agent.1)).value
      (assessment.strategy agent.1)
  else 0

variable (mixed : assessment.IsFullyMixed)
  (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
    setup.proposalRecoveryModel assessment setup.proposalRecoveryModel_decisionAntichain)
  (weights : (pool : setup.ProposalRecoveryValuePool) →
    PMF (setup.ProposalRecoveryPoolPart pool))
  (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
    (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
    assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
      setup.proposalRecoveryNormalizedTrembledProfile
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded
        (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
          pins weights) who (setup.proposalRecoveryModel.infoOf who history.trace))

include mixed bayes weights prescribed

open Classical in
/-- The ACTUAL ordinary decision-agent contribution equals its positive
cardinality times the original focal conditional gain, with no reach weights. -/
theorem proposalRecovery_ordinary_agent_gain_sum
    (focal : Player) (source : setup.proposalRecoveryModel.InformationSite focal) :
    let gain := setup.proposalRecoveryComponentGain finite assessment
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    ∑ agent ∈ setup.proposalRecoveryOrdinaryAgents focal source, gain agent =
      ((setup.proposalRecoveryOrdinaryAgents focal source).card : ℝ) *
        gain (setup.proposalRecoveryModel.agentAt source) := by
  classical
  dsimp only
  rw [Finset.sum_eq_card_nsmul]
  · rw [nsmul_eq_mul]
  · intro agent member
    obtain ⟨site, selected, rfl⟩ := Finset.mem_image.mp member
    have shared := setup.proposalRecovery_pooled_component_gain_eq finite assessment mixed bayes
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      floor floorNonnegative floorBounded pins weights alternative prescribed utility excludedPayoff
      focal site source (Finset.mem_filter.mp selected).2.1
      (Finset.mem_filter.mp selected).2.2
    unfold proposalRecoveryPooledGain at shared
    dsimp only at shared
    simp only [proposalRecoveryComponentGain,
      show setup.proposalRecoveryModel.IsDecisionInfo focal site.1 from site.property,
      show setup.proposalRecoveryModel.IsDecisionInfo focal source.1 from source.property,
      dite_eq_left] at *
    exact shared.symm

open Classical in
/-- The original ordinary-agent subsum is nonpositive exactly when the
individual source component gain is nonpositive. No attachment gain premise
or quotient assessment is substituted. -/
theorem proposalRecovery_ordinary_agent_gain_nonpos_iff
    (focal : Player) (source : setup.proposalRecoveryModel.InformationSite focal) :
    let gain := setup.proposalRecoveryComponentGain finite assessment
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    (∑ agent ∈ setup.proposalRecoveryOrdinaryAgents focal source, gain agent ≤ 0) ↔
      gain (setup.proposalRecoveryModel.agentAt source) ≤ 0 := by
  classical
  dsimp only
  have summed := setup.proposalRecovery_ordinary_agent_gain_sum finite assessment
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded
    floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    mixed bayes weights prescribed focal source
  dsimp only at summed
  rw [summed]
  have positive : (0 : ℝ) < (setup.proposalRecoveryOrdinaryAgents focal source).card := by
    exact_mod_cast (Finset.card_pos.mpr
      ⟨_, setup.proposalRecovery_agentAt_mem_ordinary focal source⟩)
  constructor
  · intro bound
    by_contra notNonpos
    exact (not_lt_of_ge bound) (mul_pos positive (lt_of_not_ge notNonpos))
  · exact fun bound => mul_nonpos_of_nonneg_of_nonpos positive.le bound

omit mixed bayes [Fintype Player] in
open Classical in
/-- The actual alternative component and the actual assessed baseline have
identical omission marginals, derived from the fixed-rate normalized source
kernel rather than assumed from a coupling witness. -/
theorem proposalRecovery_component_missed_eq
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true) :
    ((alternative (setup.proposalRecoveryAgentPool
        (setup.proposalRecoveryModel.agentAt site))).bind
      (setup.proposalRecoveryPoolComponent finite
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded
        floor floorNonnegative floorBounded pins (setup.proposalRecoveryModel.agentAt site))).map
          (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic))) =
      (assessment.strategy focal site.1).map
        (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic))) := by
  classical
  rw [setup.proposalRecoveryPoolComponent_bind finite
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded
    floor floorNonnegative floorBounded pins alternative]
  obtain ⟨history, running, _offered⟩ := site.property
  have baseline := prescribed focal history.1 running
  rw [history.property] at baseline
  rw [baseline, setup.proposalRecoveryNormalizedTrembledProfile_missed_law
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded _ focal site.1
    committing, setup.proposalRecoveryNormalizedTrembledProfile_missed_law
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded _ focal site.1
    committing]

open Classical in
/-- The EXISTING actual pooled conditional bound implies the individual
ordinary component bound. The remainder histories are derived from original
normalization and their zero contribution follows from the ACTUAL failed
local-law theorem and fixed omission kernel; no zero-gain premise is supplied. -/
theorem proposalRecovery_pooled_ordinary_component_optimal
    (focal : Player) (source : setup.proposalRecoveryModel.InformationSite focal)
    (first : CommitRecoveryState setup.program)
    (firstTrace : setup.proposalRecoveryProtocol.Trace (some first))
    (sourceAt : setup.proposalRecoveryModel.infoOf focal firstTrace = source.1)
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (ordinary : first.excluded = first.entryExcluded)
    (pooled :
      ∑ agent ∈ Finset.univ.filter
          (fun agent => setup.proposalRecoveryAgentPool agent =
            setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt source)),
        setup.proposalRecoveryComponentGain finite assessment
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          delivery deliveryNonnegative deliveryBounded
          floor floorNonnegative floorBounded pins alternative utility excludedPayoff agent ≤ 0) :
    setup.proposalRecoveryComponentGain finite assessment
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      floor floorNonnegative floorBounded pins alternative utility excludedPayoff
        (setup.proposalRecoveryModel.agentAt source) ≤ 0 := by
  classical
  let gain := setup.proposalRecoveryComponentGain finite assessment
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded
    floor floorNonnegative floorBounded pins alternative utility excludedPayoff
  let members := Finset.univ.filter
    (fun agent => setup.proposalRecoveryAgentPool agent =
      setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt source))
  have included := setup.proposalRecoveryOrdinaryAgents_subset_pool focal source
  have remainder (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation) (member : agent ∈ members)
      (outside : agent ∉ setup.proposalRecoveryOrdinaryAgents focal source) : gain agent = 0 := by
    by_cases decision : setup.proposalRecoveryModel.IsDecisionInfo agent.1 agent.2.val
    · let site : setup.proposalRecoveryModel.InformationSite agent.1 := ⟨agent.2.val, decision⟩
      have failed := setup.proposalRecovery_pool_complement_known_failed focal source
        first firstTrace sourceAt committing ordinary agent
        (Finset.mem_filter.mp member).2 outside decision
      obtain ⟨history, _running, _offered⟩ := site.property
      obtain ⟨current, state, currentCommit, _newFailure⟩ := failed history
      rcases history with ⟨⟨historyState, trace⟩, observed⟩
      dsimp only at state observed
      subst historyState
      have siteCommit : site.1.1.1.1.elim false
          (ProtocolView.atCommit agent.1 setup.program) = true := by
        rw [← observed, setup.current_private]
        simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
          ProtocolState.atCommit_observe] using currentCommit
      have marginals := setup.proposalRecovery_component_missed_eq finite assessment
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded
        floor floorNonnegative floorBounded pins alternative weights prescribed
        agent.1 site siteCommit
      have equal := setup.proposalRecovery_normalized_failed_conditional_value_eq omission
        omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded
        (setup.proposalRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
          pins weights)
        assessment prescribed utility excludedPayoff
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories agent.1 site failed
        ((alternative (setup.proposalRecoveryAgentPool agent)).bind
          (setup.proposalRecoveryPoolComponent finite omission omissionNonnegative omissionBounded
            bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded
            floor floorNonnegative floorBounded pins agent))
        (assessment.strategy agent.1 site.1) marginals
      rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at equal
      simpa only [gain, proposalRecoveryComponentGain, dite_eq_left decision] using
        (sub_eq_zero.mpr equal)
    · simp only [gain, proposalRecoveryComponentGain, dite_eq_right decision]
  have sumEqual :
      ∑ agent ∈ setup.proposalRecoveryOrdinaryAgents focal source, gain agent =
        ∑ agent ∈ members, gain agent := Finset.sum_subset included remainder
  have ordinaryBound : ∑ agent ∈ setup.proposalRecoveryOrdinaryAgents focal source,
      gain agent ≤ 0 := sumEqual.le.trans pooled
  exact (setup.proposalRecovery_ordinary_agent_gain_nonpos_iff finite assessment
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded
    floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    mixed bayes weights prescribed focal source).mp ordinaryBound

end Vegas.SourceProgram.Setup

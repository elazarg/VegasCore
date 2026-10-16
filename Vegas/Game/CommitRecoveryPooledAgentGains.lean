/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPooledOrdinaryGains
import Vegas.Source.CommitRecoveryNoMissFixed
import Vegas.Game.CommitRecoveryFailedLocalLaw

/-! # The actual source information-agent sum and its ordinary contribution

The original completion objective includes every played information agent.
Its ordinary class is the finite image of genuine ordinary decision sites;
nondecision branches contribute zero. The runtime normalization theorem
identifies all remaining decision histories as having a new exclusion.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem current_signal (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1 =
      (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current who trace]

omit [Fintype Player] in
private theorem key_committing (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who info)).1.1.1.elim false
          (ProtocolView.atCommit who setup.program) =
      info.1.1.1.elim false (ProtocolView.atCommit who setup.program) := by
  have typed : (setup.commitRecoveryNoMissInformation who info).1.1.1 = info.1.1.1 := by
    unfold commitRecoveryNoMissInformation
    split
    · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ info).1
    · rfl
  change ((setup.commitRecoveryNoMissInformation who info).1.1.1.map
    (ProtocolView.eraseHistory who setup.program)).elim false
      (ProtocolView.atCommit who setup.program) = _
  rw [typed]
  cases info.1.1.1 with
  | none => rfl
  | some view => exact ProtocolView.atCommit_eraseHistory who setup.program view

section Agents

variable [setup.FiniteInitialLaw] [Fintype setup.commitRecoveryProtocol.History]

open Classical in
/-- The actual decision-agent image of one ordinary erased-information class. -/
def commitRecoveryOrdinaryAgents (focal : Player)
    (source : setup.commitRecoveryModel.InformationSite focal) :
    Finset (setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation) :=
  let _ := Fintype.ofFinite (setup.commitRecoveryModel.InformationSite focal)
  ((Finset.univ : Finset (setup.commitRecoveryModel.InformationSite focal)).filter
    (fun site => setup.commitRecoveryErasedInformation focal site.1 =
      setup.commitRecoveryErasedInformation focal source.1)).image
        setup.commitRecoveryModel.agentAt

open Classical in
/-- Every ordinary decision agent lies in the same ACTUAL normalized pool. -/
theorem commitRecoveryOrdinaryAgents_subset_pool (finite : setup.program.FiniteBindingTypes)
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal) :
    setup.commitRecoveryOrdinaryAgents focal source ⊆ Finset.univ.filter
      (fun agent => setup.commitRecoveryAgentPool finite agent =
        setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source)) := by
  intro agent member
  obtain ⟨site, selected, rfl⟩ := Finset.mem_image.mp member
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply congrArg (Sigma.mk focal)
  apply Subtype.ext
  change setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal site.1) =
    setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal source.1)
  rw [setup.commitRecoveryNoMissInformation_erased,
    setup.commitRecoveryNoMissInformation_erased, (Finset.mem_filter.mp selected).2]

open Classical in
omit [Fintype Player] [setup.FiniteInitialLaw] in
/-- The original focal decision itself is in the ordinary agent class. -/
theorem commitRecovery_agentAt_mem_ordinary (focal : Player)
    (source : setup.commitRecoveryModel.InformationSite focal) :
    setup.commitRecoveryModel.agentAt source ∈ setup.commitRecoveryOrdinaryAgents focal source := by
  let _ := Fintype.ofFinite (setup.commitRecoveryModel.InformationSite focal)
  exact Finset.mem_image.mpr ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

open Classical in
/-- Every original history in a decision-agent remainder of an ordinary
normalized pool has an actual current foreign-failure event. The original
site and its genuine history supply the ordinary member internally. -/
theorem commitRecovery_pool_complement_known_failed (finite : setup.program.FiniteBindingTypes)
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal)
    (committing : source.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (ordinary : source.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal source.1)
    (agent : setup.commitRecoveryModel.InformationAgent setup.commitRecoveryModel.playedInformation)
    (samePool : setup.commitRecoveryAgentPool finite agent =
      setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source))
    (outside : agent ∉ setup.commitRecoveryOrdinaryAgents focal source)
    (decision : setup.commitRecoveryModel.IsDecisionInfo agent.1 agent.2.val) :
    ∀ history : setup.commitRecoveryModel.InformationHistory agent.1 agent.2.val,
      ∃ current : CommitRecoveryState setup.program,
        history.1.state = some current ∧
        ProtocolState.atCommit setup.program current.point = true ∧ current.NewFailure := by
  classical
  let _ := Fintype.ofFinite (setup.commitRecoveryModel.InformationSite focal)
  rcases agent with ⟨owner, info⟩
  have ownerEq := congrArg Sigma.fst samePool
  change owner = focal at ownerEq
  subst owner
  let target : setup.commitRecoveryModel.InformationSite focal := ⟨info.val, decision⟩
  have agentEq : (⟨focal, info⟩ : setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation) = setup.commitRecoveryModel.agentAt target := rfl
  rw [agentEq] at samePool outside
  have keys : setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal target.1) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal source.1) :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp samePool).2)
  obtain ⟨⟨⟨firstState, firstTrace⟩, sourceObserved⟩, _running, _offered⟩ := source.property
  have activeSource := InformationModel.InformationSite.active setup.commitRecoveryModel
    source ⟨⟨firstState, firstTrace⟩, sourceObserved⟩
  cases firstState with
  | none =>
      change False at activeSource
      exact activeSource.elim
  | some first =>
      have firstCommitting : ProtocolState.atCommit setup.program first.point = true := by
        have observed := committing
        rw [← sourceObserved, setup.current_signal] at observed
        simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
          ProtocolState.atCommit_observe] using observed
      obtain ⟨prior, retained, rank⟩ := setup.commitRecovery_attempt_entry first firstTrace
        firstCommitting
      have entryRead := setup.commitRecoverySavedExclusions_of_entry
        focal first firstTrace prior retained rank
      have unchanged : first.excluded = first.entryExcluded := by
        have observed := ordinary
        rw [← sourceObserved, setup.current_signal, entryRead] at observed
        exact observed
      intro history
      rcases history with ⟨⟨lastState, lastTrace⟩, targetObserved⟩
      have activeTarget := InformationModel.InformationSite.active setup.commitRecoveryModel
        target ⟨⟨lastState, lastTrace⟩, targetObserved⟩
      cases lastState with
      | none =>
          change False at activeTarget
          exact activeTarget.elim
      | some last =>
          have lastCommitting : ProtocolState.atCommit setup.program last.point = true := by
            have shape := congrArg (fun query => query.1.1.1.elim false
              (ProtocolView.atCommit focal setup.program)) keys
            rw [setup.key_committing, setup.key_committing] at shape
            have observed := shape.trans committing
            rw [← targetObserved, setup.current_signal] at observed
            simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
              ProtocolState.atCommit_observe] using observed
          have same := keys.symm
          rw [← sourceObserved, ← targetObserved] at same
          rcases setup.commitRecovery_query_fiber_cases focal first last firstTrace lastTrace
              unchanged same with erased | newFailure
          · have equal : setup.commitRecoveryErasedInformation focal target.1 =
                setup.commitRecoveryErasedInformation focal source.1 := by
              rw [← sourceObserved, ← targetObserved]
              exact erased.symm
            apply (outside (Finset.mem_image.mpr ⟨target,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, equal⟩, rfl⟩)).elim
          · exact ⟨last, rfl, lastCommitting, newFailure⟩

variable (finite : setup.program.FiniteBindingTypes)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
  (pins : (pool : setup.CommitRecoveryValuePool finite) →
    Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
  (alternative : (pool : setup.CommitRecoveryValuePool finite) →
    PMF (setup.CommitRecoveryPoolPart finite pool))
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)

open Classical in
/-- The literal conditional-gain summand of the existing source completion,
including the zero branch for original inactive information agents. -/
def commitRecoveryComponentGain
    (agent : setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation) : ℝ :=
  if decision : setup.commitRecoveryModel.IsDecisionInfo agent.1 agent.2.val then
    (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      ⟨agent.2.val, decision⟩ (setup.commitRecoveryPayoff utility excludedPayoff agent.1)).value
      ((assessment.strategy agent.1).withLaw agent.2.val
        ((alternative (setup.commitRecoveryAgentPool finite agent)).bind
          (setup.commitRecoveryPoolComponent finite
            omission omissionNonnegative omissionBounded bad badNonnegative badBounded
            floor floorNonnegative floorBounded pins agent))) -
    (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      ⟨agent.2.val, decision⟩ (setup.commitRecoveryPayoff utility excludedPayoff agent.1)).value
      (assessment.strategy agent.1)
  else 0

variable (mixed : assessment.IsFullyMixed)
  (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
    setup.commitRecoveryModel assessment setup.commitRecoveryModel_decisionAntichain)
  (weights : (pool : setup.CommitRecoveryValuePool finite) →
    PMF (setup.CommitRecoveryPoolPart finite pool))
  (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
    (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
    assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
      setup.commitRecoveryNormalizedTrembledProfile
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
          pins weights) who (setup.commitRecoveryModel.infoOf who history.trace))

include mixed bayes weights prescribed

open Classical in
/-- The ACTUAL ordinary decision-agent contribution equals its positive
cardinality times the original focal conditional gain, with no reach weights. -/
theorem commitRecovery_ordinary_agent_gain_sum
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal) :
    let gain := setup.commitRecoveryComponentGain finite assessment
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    ∑ agent ∈ setup.commitRecoveryOrdinaryAgents focal source, gain agent =
      ((setup.commitRecoveryOrdinaryAgents focal source).card : ℝ) *
        gain (setup.commitRecoveryModel.agentAt source) := by
  classical
  dsimp only
  rw [Finset.sum_eq_card_nsmul]
  · rw [nsmul_eq_mul]
  · intro agent member
    obtain ⟨site, selected, rfl⟩ := Finset.mem_image.mp member
    have shared := setup.commitRecovery_pooled_component_gain_eq finite assessment mixed bayes
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins weights alternative prescribed utility excludedPayoff
      focal site source (Finset.mem_filter.mp selected).2
    dsimp only at shared
    simp only [commitRecoveryComponentGain,
      show setup.commitRecoveryModel.IsDecisionInfo focal site.1 from site.property,
      show setup.commitRecoveryModel.IsDecisionInfo focal source.1 from source.property,
      dite_eq_left] at *
    exact shared.symm

open Classical in
/-- The original ordinary-agent subsum is nonpositive exactly when the
individual source component gain is nonpositive. No attachment gain premise
or quotient assessment is substituted. -/
theorem commitRecovery_ordinary_agent_gain_nonpos_iff
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal) :
    let gain := setup.commitRecoveryComponentGain finite assessment
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    (∑ agent ∈ setup.commitRecoveryOrdinaryAgents focal source, gain agent ≤ 0) ↔
      gain (setup.commitRecoveryModel.agentAt source) ≤ 0 := by
  classical
  dsimp only
  have summed := setup.commitRecovery_ordinary_agent_gain_sum finite assessment
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    mixed bayes weights prescribed focal source
  dsimp only at summed
  rw [summed]
  have positive : (0 : ℝ) < (setup.commitRecoveryOrdinaryAgents focal source).card := by
    exact_mod_cast (Finset.card_pos.mpr
      ⟨_, setup.commitRecovery_agentAt_mem_ordinary focal source⟩)
  constructor
  · intro bound
    by_contra notNonpos
    exact (not_lt_of_ge bound) (mul_pos positive (lt_of_not_ge notNonpos))
  · exact fun bound => mul_nonpos_of_nonneg_of_nonpos positive.le bound

omit mixed bayes in
open Classical in
/-- The actual alternative component and the actual assessed baseline have
identical omission marginals, derived from the fixed-rate normalized source
kernel rather than assumed from a coupling witness. -/
theorem commitRecovery_component_missed_eq
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true) :
    ((alternative (setup.commitRecoveryAgentPool finite
        (setup.commitRecoveryModel.agentAt site))).bind
      (setup.commitRecoveryPoolComponent finite
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        floor floorNonnegative floorBounded pins (setup.commitRecoveryModel.agentAt site))).map
          (fun choice => CommitRecoveryMove.missed choice.val) =
      (assessment.strategy focal site.1).map
        (fun choice => CommitRecoveryMove.missed choice.val) := by
  classical
  rw [setup.commitRecoveryPoolComponent_bind finite
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded pins alternative]
  obtain ⟨history, running, _offered⟩ := site.property
  have baseline := prescribed focal history.1 running
  rw [history.property] at baseline
  rw [baseline, setup.commitRecoveryNormalizedTrembledProfile_missed_law
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded _ focal site.1
    committing, setup.commitRecoveryNormalizedTrembledProfile_missed_law
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded _ focal site.1
    committing]

open Classical in
/-- The EXISTING actual pooled conditional bound implies the individual
ordinary component bound. The remainder histories are derived from original
normalization and their zero contribution follows from the ACTUAL failed
local-law theorem and fixed omission kernel; no zero-gain premise is supplied. -/
theorem commitRecovery_pooled_ordinary_component_optimal
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal)
    (committing : source.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (ordinary : source.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal source.1)
    (pooled :
      ∑ agent ∈ Finset.univ.filter
          (fun agent => setup.commitRecoveryAgentPool finite agent =
            setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source)),
        setup.commitRecoveryComponentGain finite assessment
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          floor floorNonnegative floorBounded pins alternative utility excludedPayoff agent ≤ 0) :
    setup.commitRecoveryComponentGain finite assessment
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      floor floorNonnegative floorBounded pins alternative utility excludedPayoff
        (setup.commitRecoveryModel.agentAt source) ≤ 0 := by
  classical
  let gain := setup.commitRecoveryComponentGain finite assessment
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded pins alternative utility excludedPayoff
  let members := Finset.univ.filter
    (fun agent => setup.commitRecoveryAgentPool finite agent =
      setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source))
  have included := setup.commitRecoveryOrdinaryAgents_subset_pool finite focal source
  have remainder (agent : setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation) (member : agent ∈ members)
      (outside : agent ∉ setup.commitRecoveryOrdinaryAgents focal source) : gain agent = 0 := by
    by_cases decision : setup.commitRecoveryModel.IsDecisionInfo agent.1 agent.2.val
    · let site : setup.commitRecoveryModel.InformationSite agent.1 := ⟨agent.2.val, decision⟩
      have failed := setup.commitRecovery_pool_complement_known_failed finite focal source
        committing ordinary agent (Finset.mem_filter.mp member).2 outside decision
      obtain ⟨history, _running, _offered⟩ := site.property
      obtain ⟨current, state, currentCommit, _newFailure⟩ := failed history
      rcases history with ⟨⟨historyState, trace⟩, observed⟩
      dsimp only at state observed
      subst historyState
      have siteCommit : site.1.1.1.1.elim false
          (ProtocolView.atCommit agent.1 setup.program) = true := by
        rw [← observed, setup.current_signal]
        simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
          ProtocolState.atCommit_observe] using currentCommit
      have marginals := setup.commitRecovery_component_missed_eq finite assessment
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        floor floorNonnegative floorBounded pins alternative weights prescribed
        agent.1 site siteCommit
      have equal := setup.commitRecovery_normalized_failed_conditional_value_eq omission
        omissionNonnegative omissionBounded bad badNonnegative badBounded
        (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded
          pins weights)
        assessment prescribed utility excludedPayoff
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories agent.1 site failed
        ((alternative (setup.commitRecoveryAgentPool finite agent)).bind
          (setup.commitRecoveryPoolComponent finite omission omissionNonnegative omissionBounded
            bad badNonnegative badBounded floor floorNonnegative floorBounded pins agent))
        (assessment.strategy agent.1 site.1) marginals
      rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at equal
      simpa only [gain, commitRecoveryComponentGain, dite_eq_left decision] using
        (sub_eq_zero.mpr equal)
    · simp only [gain, commitRecoveryComponentGain, dite_eq_right decision]
  have sumEqual :
      ∑ agent ∈ setup.commitRecoveryOrdinaryAgents focal source, gain agent =
        ∑ agent ∈ members, gain agent := Finset.sum_subset included remainder
  have ordinaryBound : ∑ agent ∈ setup.commitRecoveryOrdinaryAgents focal source,
      gain agent ≤ 0 := sumEqual.le.trans pooled
  exact (setup.commitRecovery_ordinary_agent_gain_nonpos_iff finite assessment
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    floor floorNonnegative floorBounded pins alternative utility excludedPayoff
    mixed bayes weights prescribed focal source).mp ordinaryBound

end Agents

end Vegas.SourceProgram.Setup

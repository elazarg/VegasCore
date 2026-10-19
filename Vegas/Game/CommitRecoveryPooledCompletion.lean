/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNormalizedFlagPlan
import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion

/-! # Consistent source assessments with shared normalized domain laws

The original full-information agents share weights at their genuine normalized
queries. Omission, accepted failure and domain floors are fixed before those
weights are selected. Optional pins belong to the shared query, so every member
uses the same pin. Individual incentive bounds require the separate source
ancillary-likelihood and reset arguments.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Owner-indexed genuine reduced queries, including every supported retry. -/
abbrev CommitRecoveryValuePool (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] :=
  (owner : Player) × setup.commitRecoveryDomainSites finite owner

/-- The common ordinary menu of a genuine reduced query. -/
abbrev CommitRecoveryPoolPart (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (pool : setup.CommitRecoveryValuePool finite) :=
  setup.CommitRecoveryValueChoice pool.1 pool.2.val

/-- A domain reference is fixed independently of any optimized pool weights. -/
def commitRecoveryValueReference (finite : setup.program.FiniteBindingTypes)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    PMF (setup.CommitRecoveryValueChoice who info) := by
  let _ := setup.commitRecoveryValueChoice_finite finite who info
  let _ := Fintype.ofFinite (setup.CommitRecoveryValueChoice who info)
  let _ := setup.commitRecoveryValueChoice_nonempty who info
  exact PMF.uniformOfFintype _

omit [Fintype Player] in
theorem commitRecoveryValueReference_fullSupport (finite : setup.program.FiniteBindingTypes)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    FullSupport (setup.commitRecoveryValueReference finite who info) := by
  let _ := setup.commitRecoveryValueChoice_finite finite who info
  let _ := Fintype.ofFinite (setup.CommitRecoveryValueChoice who info)
  let _ := setup.commitRecoveryValueChoice_nonempty who info
  exact fun _ => PMF.mem_support_uniformOfFintype _

section Played

variable [setup.FiniteInitialLaw] [Fintype setup.commitRecoveryProtocol.History]

open Classical in
/-- Each original information agent reads the same genuine normalized label
as the initialized source sampler. -/
abbrev commitRecoveryAgentPool (finite : setup.program.FiniteBindingTypes)
    (agent : setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation) : setup.CommitRecoveryValuePool finite := by
  refine ⟨agent.1, ⟨setup.commitRecoveryErasedInformation agent.1
    (setup.commitRecoveryNoMissInformation agent.1 agent.2.val), ?_⟩⟩
  have played := agent.2.property
  unfold GameTheory.Protocol.InformationModel.playedInformation at played
  obtain ⟨history, member, same⟩ := Finset.mem_image.mp played
  obtain ⟨replay, observed, running⟩ :=
    setup.commitRecoveryNoMissInformation_genuine_history agent.1 history
  have current := setup.commitRecoveryDomainSites_current finite agent.1 replay
    (running (Finset.mem_filter.mp member).2)
  rw [setup.commitRecoveryErasedModel_infoOf, observed, same] at current
  exact current

end Played

open Classical in
/-- Resolve shared domain weights, with a query-level optional pin, and then
add the independently chosen full-support domain floor. -/
def commitRecoveryPooledDomainLaw (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (pins : (pool : setup.CommitRecoveryValuePool finite) →
      Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    PMF (setup.CommitRecoveryValueChoice who info) :=
  mix floor nonnegative bounded (setup.commitRecoveryValueReference finite who info)
    (if present : info ∈ setup.commitRecoveryDomainSites finite who then
      (pins ⟨who, ⟨info, present⟩⟩).getD (weights ⟨who, ⟨info, present⟩⟩)
    else setup.commitRecoveryValueReference finite who info)

theorem commitRecoveryPooledDomainLaw_fullSupport
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (floor : ℝ) (positive : 0 < floor) (bounded : floor ≤ 1)
    (pins : (pool : setup.CommitRecoveryValuePool finite) →
      Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool)) (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    FullSupport (setup.commitRecoveryPooledDomainLaw finite floor positive.le bounded
      pins weights who info) := by
  intro value
  exact mem_support_mix_left floor positive.le bounded positive
    (setup.commitRecoveryValueReference_fullSupport finite who info value)

omit [Fintype Player] in
theorem commitRecoveryValueTremble_bind (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    {Part : Type} (weights : PMF Part)
    (values : Part → PMF (setup.CommitRecoveryValueChoice who info)) :
    weights.bind (fun part => setup.commitRecoveryValueTremble who info
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded (values part)) =
      setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded (weights.bind values) := by
  simp only [← setup.commitRecoveryFlagLaw_choice, PMF.map_bind]
  exact PMF.bind_comm _ _ _

section Played

variable [setup.FiniteInitialLaw] [Fintype setup.commitRecoveryProtocol.History]

open Classical in
/-- A pure pool part gives an actual fully supported original source choice;
the optional pin replaces its domain part before the prescribed floor. -/
def commitRecoveryPoolComponent (finite : setup.program.FiniteBindingTypes)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (pins : (pool : setup.CommitRecoveryValuePool finite) →
      Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
    (agent : setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation)
    (part : setup.CommitRecoveryPoolPart finite (setup.commitRecoveryAgentPool finite agent)) :
    PMF (setup.commitRecoveryModel.Choice agent.1 agent.2.val) :=
  (setup.commitRecoveryValueTremble agent.1
    (setup.commitRecoveryAgentPool finite agent).2.val
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    (mix floor floorNonnegative floorBounded
      (setup.commitRecoveryValueReference finite agent.1
        (setup.commitRecoveryAgentPool finite agent).2.val)
      ((pins (setup.commitRecoveryAgentPool finite agent)).getD (PMF.pure part)))).map
        (setup.commitRecoveryNoMissErasedChoice agent.1 agent.2.val).symm

open Classical in
theorem commitRecoveryPoolComponent_fullSupport (finite : setup.program.FiniteBindingTypes)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (floor : ℝ) (floorPositive : 0 < floor) (floorSmall : floor < 1)
    (pins : (pool : setup.CommitRecoveryValuePool finite) →
      Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
    (agent : setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation)
    (part : setup.CommitRecoveryPoolPart finite (setup.commitRecoveryAgentPool finite agent)) :
    FullSupport (setup.commitRecoveryPoolComponent finite
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
      floor floorPositive.le floorSmall.le pins agent part) := by
  intro choice
  refine (PMF.mem_support_map_iff _ _ _).mpr
    ⟨(setup.commitRecoveryNoMissErasedChoice agent.1 agent.2.val) choice, ?_, ?_⟩
  · apply setup.commitRecoveryValueTremble_fullSupport _ _ omission omissionPositive
      omissionSmall bad badPositive badSmall
    intro value
    exact mem_support_mix_left floor floorPositive.le floorSmall.le floorPositive
      (setup.commitRecoveryValueReference_fullSupport finite _ _ value)
  · exact (setup.commitRecoveryNoMissErasedChoice agent.1 agent.2.val).symm_apply_apply choice

open Classical in
theorem commitRecoveryPoolComponent_bind (finite : setup.program.FiniteBindingTypes)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (pins : (pool : setup.CommitRecoveryValuePool finite) →
      Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
    (weights : (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (agent : setup.commitRecoveryModel.InformationAgent
      setup.commitRecoveryModel.playedInformation) :
    (weights (setup.commitRecoveryAgentPool finite agent)).bind
        (setup.commitRecoveryPoolComponent finite omission omissionNonnegative omissionBounded
          bad badNonnegative badBounded floor floorNonnegative floorBounded pins agent) =
      setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded
        (setup.commitRecoveryPooledDomainLaw finite
          floor floorNonnegative floorBounded pins weights)
        agent.1 agent.2.val := by
  have pointwise : setup.commitRecoveryNormalizedTrembledProfile
      omission omissionNonnegative
      omissionBounded bad badNonnegative badBounded
      (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded pins weights)
      agent.1 agent.2.val =
      (setup.commitRecoveryValueTremble agent.1
        (setup.commitRecoveryAgentPool finite agent).2.val
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        (setup.commitRecoveryPooledDomainLaw finite floor floorNonnegative floorBounded pins weights
          agent.1 (setup.commitRecoveryAgentPool finite agent).2.val)).map
            (setup.commitRecoveryNoMissErasedChoice agent.1 agent.2.val).symm := by
    unfold commitRecoveryNormalizedTrembledProfile
    apply pmf_map_injective Subtype.val_injective
    rw [setup.commitRecoveryNoMissErasedProfile_raw, PMF.map_comp]
    rfl
  rw [pointwise]
  unfold commitRecoveryPoolComponent
  rw [← PMF.map_bind, setup.commitRecoveryValueTremble_bind]
  apply congrArg (fun law => (setup.commitRecoveryValueTremble agent.1
    (setup.commitRecoveryAgentPool finite agent).2.val
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded law).map
      (setup.commitRecoveryNoMissErasedChoice agent.1 agent.2.val).symm)
  unfold commitRecoveryPooledDomainLaw
  rw [dite_eq_left (setup.commitRecoveryAgentPool finite agent).2.property]
  cases pinned : pins (setup.commitRecoveryAgentPool finite agent) with
  | none =>
      simp only [Option.getD_none]
      exact bind_mix_pure _ _ _ _ _
  | some law =>
      simp only [Option.getD_some, PMF.bind_const]

open Classical in
/-- Shared weights select actual full-information source assessments with
Bayes beliefs and pooled conditional gains, and the SAME initialized sampler
realizes their entire source runner. Individual source rationality and honest
pin preservation remain separate conclusions. -/
theorem exists_consistent_commitRecovery_normalized_pool
    (finite : setup.program.FiniteBindingTypes)
    (omission bad floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badPositive : ∀ n, 0 < bad n) (badSmall : ∀ n, bad n < 1)
    (floorPositive : ∀ n, 0 < floor n) (floorSmall : ∀ n, floor n < 1)
    (pins : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
    (fallback : (who : Player) → setup.commitRecoveryModel.Policy who)
    (payoff : Player → setup.commitRecoveryProtocol.History → ℝ) :
    let component := fun n => setup.commitRecoveryPoolComponent finite
      (omission n) (omissionPositive n).le (omissionSmall n).le
      (bad n) (badPositive n).le (badSmall n).le
      (floor n) (floorPositive n).le (floorSmall n).le (pins n)
    ∃ (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
        PMF (setup.CommitRecoveryPoolPart finite pool))
      (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
      (limit : setup.commitRecoveryModel.BehavioralAssessment) (index : ℕ → ℕ),
      (∀ n agent, (sequence n).strategy agent.1 agent.2.val =
        (weights n (setup.commitRecoveryAgentPool finite agent)).bind (component n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        setup.commitRecoveryModel (sequence n) setup.commitRecoveryModel_decisionAntichain) ∧
      StrictMono index ∧
      InformationModel.BehavioralAssessmentConvergesPointwise
        (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent setup.commitRecoveryModel_decisionAntichain ∧
      (∀ n (alternative : (pool : setup.CommitRecoveryValuePool finite) →
          PMF (setup.CommitRecoveryPoolPart finite pool)) pool,
        ∑ agent ∈ Finset.univ.filter
            (fun agent => setup.commitRecoveryAgentPool finite agent = pool),
          (if decision : setup.commitRecoveryModel.IsDecisionInfo agent.1 agent.2.val then
            ((sequence n).continuationContext
                setup.commitRecoveryProtocol_bounded.wellFoundedHistories
                ⟨agent.2.val, decision⟩ (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.val
                  ((alternative (setup.commitRecoveryAgentPool finite agent)).bind
                    (component n agent))) -
              ((sequence n).continuationContext
                setup.commitRecoveryProtocol_bounded.wellFoundedHistories
                ⟨agent.2.val, decision⟩ (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) ∧
      (∀ n who (history : setup.commitRecoveryProtocol.History)
          (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
        (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
          setup.commitRecoveryNormalizedTrembledProfile
            (omission n) (omissionPositive n).le (omissionSmall n).le
            (bad n) (badPositive n).le (badSmall n).le
            (setup.commitRecoveryPooledDomainLaw finite
              (floor n) (floorPositive n).le (floorSmall n).le (pins n) (weights n))
            who (setup.commitRecoveryModel.infoOf who history.trace)) ∧
      ∀ n fuel,
        setup.commitRecoveryModel.runMixed
            (fun who => (setup.commitRecoveryFlagPlan finite who
              (omission n) (omissionPositive n).le (omissionSmall n).le
              (bad n) (badPositive n).le (badSmall n).le
              (setup.commitRecoveryPooledDomainLaw finite
                (floor n) (floorPositive n).le (floorSmall n).le (pins n) (weights n) who)).map
                  (setup.commitRecoveryNormalizedFlagPolicy finite who)) fuel =
          setup.commitRecoveryModel.runBehavioral (sequence n).strategy fuel := by
  classical
  dsimp only
  have : Finite (setup.CommitRecoveryValuePool finite) := inferInstance
  let _ (pool : setup.CommitRecoveryValuePool finite) :
      Finite (setup.CommitRecoveryPoolPart finite pool) :=
    setup.commitRecoveryValueChoice_finite finite pool.1 pool.2.val
  let _ (pool : setup.CommitRecoveryValuePool finite) :
      Nonempty (setup.CommitRecoveryPoolPart finite pool) :=
    setup.commitRecoveryValueChoice_nonempty pool.1 pool.2.val
  let component := fun n => setup.commitRecoveryPoolComponent finite
    (omission n) (omissionPositive n).le (omissionSmall n).le
    (bad n) (badPositive n).le (badSmall n).le
    (floor n) (floorPositive n).le (floorSmall n).le (pins n)
  have decisionRecall := setup.commitRecoveryModel.decisionRecall_of_perfectRecall
    setup.commitRecoveryModel_perfectRecall
  obtain ⟨weights, sequence, limit, index, assembled, full, bayes, increasing,
      converges, consistent, gains, -⟩ :=
    setup.commitRecoveryModel.exists_consistent_pooled_completion decisionRecall fallback
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories payoff
      (setup.commitRecoveryAgentPool finite) component (fun n agent part =>
        setup.commitRecoveryPoolComponent_fullSupport finite
          (omission n) (omissionPositive n) (omissionSmall n)
          (bad n) (badPositive n) (badSmall n)
          (floor n) (floorPositive n) (floorSmall n) (pins n) agent part)
  have agentLaw n agent : (sequence n).strategy agent.1 agent.2.val =
      (weights n (setup.commitRecoveryAgentPool finite agent)).bind (component n agent) := by
    rw [assembled n, InformationModel.agentBehavior_at]
  have actual n who (history : setup.commitRecoveryProtocol.History)
      (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
      (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badPositive n).le (badSmall n).le
          (setup.commitRecoveryPooledDomainLaw finite
            (floor n) (floorPositive n).le (floorSmall n).le (pins n) (weights n))
          who (setup.commitRecoveryModel.infoOf who history.trace) := by
    let agent : setup.commitRecoveryModel.InformationAgent
        setup.commitRecoveryModel.playedInformation :=
      ⟨who, ⟨_, setup.commitRecoveryModel.mem_playedInformation running⟩⟩
    exact (agentLaw n agent).trans (setup.commitRecoveryPoolComponent_bind finite
      (omission n) (omissionPositive n).le (omissionSmall n).le
      (bad n) (badPositive n).le (badSmall n).le
      (floor n) (floorPositive n).le (floorSmall n).le (pins n) (weights n) agent)
  refine ⟨weights, sequence, limit, index, agentLaw, full, bayes, increasing,
    converges, consistent, gains, actual, ?_⟩
  intro n fuel
  rw [setup.commitRecoveryNormalizedFlagPlan_run finite
    (omission n) (omissionPositive n) (omissionSmall n)
    (bad n) (badPositive n) (badSmall n) _
    (setup.commitRecoveryPooledDomainLaw_fullSupport finite
      (floor n) (floorPositive n) (floorSmall n).le (pins n) (weights n))]
  apply setup.commitRecoveryModel.runBehavioralFrom_congr fuel
  intro history _ running who
  exact (actual n who history running).symm

end Played

end Vegas.SourceProgram.Setup

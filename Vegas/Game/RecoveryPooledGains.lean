/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryOnePacketCompletion
import Vegas.Game.RecoveryOwingOptimality
import GameTheoryExtensions.Analysis.Protocol.AffineKeyedPools

/-! # Actual pooled recovery gains from common affine component values -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)
  [Fintype ((Recovery.onePacketMenu runtime leaks bounds).protocol
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).History]
  [∀ who, DecidableEq ((model setup runtime leaks bounds
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).InfoState who)]

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "menu" => Recovery.onePacketMenu runtime leaks bounds
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler

omit [Fintype (RP).History] in
/-- The actual finite local gain is the continuation-value difference in the
same recovery assessment, with the bounded runtime's own certificate. -/
theorem localGain_eq_continuation_value_sub
    {Outcome : Type*} (observe : (RP).History → Outcome)
    (utility : Outcome → Player → ℝ) (assessment : (R).BehavioralAssessment)
    {who : Player} (site : (R).InformationSite who) (law : PMF ((R).Choice who site.1)) :
    localGain (2 * horizon + 1) observe utility assessment site law =
      (assessment.continuationContext
        ((menu).bounded Initial horizon scheduler).wellFoundedHistories
        site (fun final => utility (observe final) who)).value
          ((assessment.strategy who).withLaw site.1 law) -
        (assessment.continuationContext
          ((menu).bounded Initial horizon scheduler).wellFoundedHistories
          site (fun final => utility (observe final) who)).value (assessment.strategy who) := by
  rw [localGain_eq_sub,
    localValue_eq_continuationContext (2 * horizon + 1) observe utility assessment site
      ((menu).bounded Initial horizon scheduler),
    localValue_eq_continuationContext (2 * horizon + 1) observe utility assessment site
      ((menu).bounded Initial horizon scheduler), BehavioralPolicy.withLaw_eq_self]

open Classical in
/-- The original completion's pooled continuation-value witness supplies the
finite local-gain inequality with unchanged pools, weights and assessments. -/
theorem pooledLocalGain_nonpos_of_continuation {Outcome : Type*}
    (observe : (RP).History → Outcome) (utility : Outcome → Player → ℝ)
    (assessment : (R).BehavioralAssessment) (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (pooled : ∀ (alternative : ∀ p,
        PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => pool setup runtime leaks bounds Initial horizon scheduler agent = p),
        (if decision : (R).IsDecisionInfo agent.1 agent.2.1 then
          (assessment.continuationContext
              ((menu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩ (fun final => utility (observe final) agent.1)).value
              ((assessment.strategy agent.1).withLaw agent.2.1
                ((alternative (pool setup runtime leaks bounds Initial horizon scheduler
                  agent)).bind
                  (component setup runtime leaks bounds Initial horizon scheduler source scale
                    nonnegative le_one agent))) -
            (assessment.continuationContext
              ((menu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩ (fun final => utility (observe final) agent.1)).value
                (assessment.strategy agent.1)
        else 0) ≤ 0) :
    ∀ (alternative : ∀ p,
        PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => pool setup runtime leaks bounds Initial horizon scheduler agent = p),
        (if decision : (R).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) observe utility assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            ((alternative (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
              (component setup runtime leaks bounds Initial horizon scheduler source scale
                nonnegative
                le_one agent)) else 0) ≤ 0 := by
  intro alternative p
  simp_rw [localGain_eq_continuation_value_sub]
  exact pooled alternative p

open Classical in
/-- A free recovery agent is alone in its original pool, so the same pooled
optimality witness makes each component-mixture gain nonpositive. -/
theorem freeAgent_componentGain_nonpos {Outcome : Type*}
    (observe : (RP).History → Outcome) (utility : Outcome → Player → ℝ)
    (assessment : (R).BehavioralAssessment) (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (pooled : ∀ (alternative : ∀ p,
        PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => pool setup runtime leaks bounds Initial horizon scheduler agent = p),
        (if decision : (R).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) observe utility assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            ((alternative (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
              (component setup runtime leaks bounds Initial horizon scheduler source scale
                nonnegative
                le_one agent)) else 0) ≤ 0)
    {who : Player} (site : (R).InformationSite who)
    (free : FreeAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site))
    (alternative : PMF (Part setup runtime leaks bounds Initial horizon scheduler slots
      (pool setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site)))) :
    localGain (2 * horizon + 1) observe utility assessment site
      (alternative.bind (component setup runtime leaks bounds Initial horizon scheduler source scale
        nonnegative le_one ((R).agentAt site))) ≤ 0 := by
  classical
  rcases site with ⟨info, decision⟩
  let site : (R).InformationSite who := ⟨info, decision⟩
  have singleton : Finset.univ.filter (fun agent =>
      pool setup runtime leaks bounds Initial horizon scheduler agent =
        pool setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site)) =
      {(R).agentAt site} := by
    ext agent
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro same
      dsimp only [pool] at same
      rw [freeKeyedPool_of_free free] at same
      exact eq_of_freeKeyedPool_eq_inl same
    · rintro rfl
      rfl
  have bound := pooled
    (Function.update weights
      (pool setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site)) alternative)
    (pool setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site))
  rw [singleton, Finset.sum_singleton, dite_eq_left site.2] at bound
  simpa only [Function.update_self] using bound

/-- At a nonfree nonkeyed recovery site all pool parts prescribe the same law;
every mixture agrees with the original assembled law and has zero gain. -/
theorem nonkeyed_componentGain_eq_zero {Outcome : Type*}
    (observe : (RP).History → Outcome) (utility : Outcome → Player → ℝ)
    (assessment : (R).BehavioralAssessment) (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (fallback : ∀ who, (R).Policy who)
    (assembled : assessment.strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler source scale nonnegative
          le_one agent)))
    {who : Player} (site : (R).InformationSite who)
    (notFree : ¬ FreeAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site))
    (nonkeyed : ¬ KeyedAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt
      site))
    (alternative : PMF (Part setup runtime leaks bounds Initial horizon scheduler slots
      (pool setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site)))) :
    localGain (2 * horizon + 1) observe utility assessment site
      (alternative.bind (component setup runtime leaks bounds Initial horizon scheduler source scale
        nonnegative le_one ((R).agentAt site))) = 0 := by
  classical
  let agent := (R).agentAt site
  let prescribed := prescribedComponent setup runtime leaks bounds Initial horizon scheduler source
    scale nonnegative le_one
  let keyed := keyedComponent setup runtime leaks bounds Initial horizon scheduler source
    (slots := slots) scale nonnegative le_one
  obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free
    (key := agentKey setup runtime leaks bounds Initial horizon scheduler)
    (keyed := KeyedAgent setup runtime leaks bounds Initial horizon scheduler)
    (freeLaw setup runtime leaks bounds Initial horizon scheduler scale nonnegative le_one)
    prescribed keyed notFree
  have constant : component setup runtime leaks bounds Initial horizon scheduler source (slots :=
    slots)
      scale nonnegative le_one agent = fun _ => prescribed agent := by
    funext part
    exact (same part).trans
      (keyedComponent_of_not_keyed prescribed keyed (fun owned => nonkeyed owned.1) (identify part))
  have actual := (R).agentBehavior_at (R).playedInformation fallback
    (fun agent => (weights (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
      (component setup runtime leaks bounds Initial horizon scheduler source scale nonnegative
        le_one
        agent)) agent
  rw [← assembled, constant, PMF.bind_const] at actual
  rw [constant, PMF.bind_const, ← actual]
  exact localGain_self _ _ _ _ _

open Classical in
/-- The original pooled recovery witness bounds every member mixture once its
actual keyed component payoffs have a common affine score. Owing agents use
actual recovery completion; the other pools use their exact algebraic laws. -/
theorem componentGain_le_of_common_values {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    (assessment : (R).BehavioralAssessment) (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (fallback : ∀ who, (R).Policy who)
    (assembled : assessment.strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler source scale nonnegative
          le_one agent)))
    (pooled : ∀ (alternative : ∀ p,
        PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => pool setup runtime leaks bounds Initial horizon scheduler agent = p),
        (if decision : (R).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) (fun final => final.state)
            (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff)
              assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            ((alternative (pool setup runtime leaks bounds Initial horizon scheduler agent)).bind
              (component setup runtime leaks bounds Initial horizon scheduler source scale
                nonnegative
                le_one agent)) else 0) ≤ 0)
    (continuation : (R).InformationAgent (R).playedInformation → ℝ)
    (score : Option (LateKey setup runtime leaks) → LateOption slots → ℝ) (error : ℝ)
    (values : ∀ agent : (R).InformationAgent (R).playedInformation,
      ownedKeyed (FreeAgent setup runtime leaks bounds Initial horizon scheduler)
        (KeyedAgent setup runtime leaks bounds Initial horizon scheduler) agent →
      ¬ OwingAgent setup runtime leaks bounds Initial horizon scheduler agent →
      ∀ decision : (R).IsDecisionInfo agent.1 agent.2.1,
        excludedPayoff agent.1 ≤ continuation agent ∧ ∀ option,
        |localValue (2 * horizon + 1) (fun final => final.state)
            (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff)
              assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            (keyedComponent setup runtime leaks bounds Initial horizon scheduler source scale
              nonnegative
              le_one agent option) -
          (excludedPayoff agent.1 + score
            (agentKey setup runtime leaks bounds Initial horizon scheduler agent) option *
              (continuation agent - excludedPayoff agent.1))| ≤ error) :
    ∀ who (site : (R).InformationSite who)
      (alternative : PMF (Part setup runtime leaks bounds Initial horizon scheduler slots
        (pool setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site)))),
      localGain (2 * horizon + 1) (fun final => final.state)
        (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff) assessment
          site
        (alternative.bind (component setup runtime leaks bounds Initial horizon scheduler source
          scale
          nonnegative le_one ((R).agentAt site))) ≤
        Fintype.card ((R).InformationAgent (R).playedInformation) * (2 * max error 0) := by
  classical
  have pooledLocal := pooled
  have boundNonneg : 0 ≤
      (Fintype.card ((R).InformationAgent (R).playedInformation) : ℝ) * (2 * max error 0) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (le_max_right _ _))
  intro who site alternative
  by_cases free : FreeAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site)
  · exact (freeAgent_componentGain_nonpos setup runtime leaks bounds horizon scheduler _ _
      assessment
      source scale nonnegative le_one weights pooledLocal site free alternative).trans boundNonneg
  by_cases owing : OwingAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt
    site)
  · rw [owingAgent_localGain_eq_zero setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff completes assessment site owing]
    exact boundNonneg
  by_cases keyed : KeyedAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt
    site)
  · have assembledGeneric := assembled
    dsimp only [component] at assembledGeneric
    exact freeKeyed_memberGain_le_of_common_values (T := (RP)) (N := (R))
      (Key := Option (LateKey setup runtime leaks)) (Opt := LateOption slots)
      (2 * horizon + 1)
      ((menu).bounded Initial horizon scheduler) ((menu).decisionRecall Initial horizon scheduler)
      (fun final => final.state) (recoveryExclusionBase (runtime := runtime) parameter utility
        excludedPayoff) fallback
      (FreeAgent setup runtime leaks bounds Initial horizon scheduler)
      (KeyedAgent setup runtime leaks bounds Initial horizon scheduler)
      (agentKey setup runtime leaks bounds Initial horizon scheduler)
      (OwingAgent setup runtime leaks bounds Initial horizon scheduler)
      (freeLaw setup runtime leaks bounds Initial horizon scheduler scale nonnegative le_one)
      (prescribedComponent setup runtime leaks bounds Initial horizon scheduler source scale
        nonnegative
        le_one)
      (keyedComponent setup runtime leaks bounds Initial horizon scheduler source (slots := slots)
        scale nonnegative le_one)
      weights assessment assembledGeneric
      (fun alternative p => by
        apply le_trans ?_ (pooled alternative p)
        apply le_of_eq
        apply Finset.sum_congr
        · ext agent
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        · intro agent _member
          split_ifs
          · rfl
          · rfl)
      excludedPayoff
      (fun _ site debt law => owingAgent_localGain_eq_zero setup runtime leaks bounds horizon
        scheduler
        parameter utility excludedPayoff completes assessment site debt law)
      continuation score error values who site ⟨keyed, free⟩ alternative
  · rw [nonkeyed_componentGain_eq_zero setup runtime leaks bounds horizon scheduler _ _ assessment
      source
      scale nonnegative le_one weights fallback assembled site free keyed alternative]
    exact boundNonneg

end Vegas.RecoveryOnePacket

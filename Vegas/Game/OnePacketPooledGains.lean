/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCommonCompletion
import Vegas.Game.OnePacketOwingOptimality
import GameTheoryExtensions.Analysis.Protocol.AffineKeyedPools

/-! # Native pooled gains from common affine component values -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
    horizon scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup)
    horizon scheduler).InfoState who)]

local notation "Initial" => initialLaw setup
local notation "onePacketN" => onePacketModel setup timeouts leaks bounds Initial horizon scheduler
local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) Initial horizon scheduler

omit [Fintype (NP).History] in
/-- The native finite local gain is the continuation-value difference in the
same native assessment, with the bounded runtime's own certificate. -/
private theorem localGain_eq_continuation_value_sub
    {Outcome : Type*} (observe : (NP).History → Outcome)
    (utility : Outcome → Player → ℝ) (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who
      site.1)) :
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
    (observe : (NP).History → Outcome) (utility : Outcome → Player → ℝ)
    (assessment : (onePacketN).BehavioralAssessment) (source :
      setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (pooled : ∀ (alternative : ∀ p,
        PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => onePacketPool setup timeouts leaks bounds Initial horizon scheduler agent =
            p),
        (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
          (assessment.continuationContext
              ((menu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩ (fun final => utility (observe final) agent.1)).value
              ((assessment.strategy agent.1).withLaw agent.2.1
                ((alternative (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
                  agent)).bind
                  (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source
                    scale
                    nonnegative le_one agent))) -
            (assessment.continuationContext
              ((menu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩ (fun final => utility (observe final) agent.1)).value
                (assessment.strategy agent.1)
        else 0) ≤ 0) :
    ∀ (alternative : ∀ p,
        PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => onePacketPool setup timeouts leaks bounds Initial horizon scheduler agent =
            p),
        (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) observe utility assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            ((alternative (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
              agent)).bind
              (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source scale
                nonnegative
                le_one agent)) else 0) ≤ 0 := by
  intro alternative p
  simp_rw [localGain_eq_continuation_value_sub]
  exact pooled alternative p

open Classical in
/-- A free native agent is alone in its original pool, so the same pooled
optimality witness makes each component-mixture gain nonpositive. -/
private theorem freeAgent_componentGain_nonpos {Outcome : Type*}
    (observe : (NP).History → Outcome) (utility : Outcome → Player → ℝ)
    (assessment : (onePacketN).BehavioralAssessment) (source :
      setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots
      p))
    (pooled : ∀ (alternative : ∀ p,
        PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => onePacketPool setup timeouts leaks bounds Initial horizon scheduler agent =
            p),
        (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) observe utility assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            ((alternative (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
              agent)).bind
              (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source scale
                nonnegative
                le_one agent)) else 0) ≤ 0)
    {who : Player} (site : (onePacketN).InformationSite who)
    (free : FreeAgent setup timeouts leaks bounds Initial horizon scheduler ((onePacketN).agentAt
      site))
    (alternative : PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots
      (onePacketPool setup timeouts leaks bounds Initial horizon scheduler ((onePacketN).agentAt
        site)))) :
    localGain (2 * horizon + 1) observe utility assessment site
      (alternative.bind (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler
        source scale
        nonnegative le_one ((onePacketN).agentAt site))) ≤ 0 := by
  classical
  rcases site with ⟨info, decision⟩
  let site : (onePacketN).InformationSite who := ⟨info, decision⟩
  have singleton : Finset.univ.filter (fun agent =>
      onePacketPool setup timeouts leaks bounds Initial horizon scheduler agent =
        onePacketPool setup timeouts leaks bounds Initial horizon scheduler ((onePacketN).agentAt
          site)) =
      {(onePacketN).agentAt site} := by
    ext agent
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro same
      dsimp only [onePacketPool] at same
      rw [freeKeyedPool_of_free free] at same
      exact eq_of_freeKeyedPool_eq_inl same
    · rintro rfl
      rfl
  have bound := pooled
    (Function.update weights
      (onePacketPool setup timeouts leaks bounds Initial horizon scheduler ((onePacketN).agentAt
        site))
        alternative)
    (onePacketPool setup timeouts leaks bounds Initial horizon scheduler ((onePacketN).agentAt
      site))
  rw [singleton, Finset.sum_singleton, dite_eq_left site.2] at bound
  simpa only [Function.update_self] using bound

/-- At a nonfree nonkeyed native site all pool parts prescribe the same law;
every mixture agrees with the original assembled law and has zero gain. -/
private theorem nonkeyed_componentGain_eq_zero {Outcome : Type*}
    (observe : (NP).History → Outcome) (utility : Outcome → Player → ℝ)
    (assessment : (onePacketN).BehavioralAssessment) (source :
      setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots
      p))
    (fallback : ∀ who, (onePacketN).Policy who)
    (assembled : assessment.strategy = (onePacketN).agentBehavior (onePacketN).playedInformation
      fallback
      (fun agent => (weights (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
        agent)).bind
        (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source scale
          nonnegative
          le_one agent)))
    {who : Player} (site : (onePacketN).InformationSite who)
    (notFree : ¬ FreeAgent setup timeouts leaks bounds Initial horizon scheduler
      ((onePacketN).agentAt site))
    (nonkeyed : ¬ LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler
      ((onePacketN).agentAt
      site))
    (alternative : PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots
      (onePacketPool setup timeouts leaks bounds Initial horizon scheduler ((onePacketN).agentAt
        site)))) :
    localGain (2 * horizon + 1) observe utility assessment site
      (alternative.bind (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler
        source scale
        nonnegative le_one ((onePacketN).agentAt site))) = 0 := by
  classical
  let agent := (onePacketN).agentAt site
  let prescribed := fun agent : (onePacketN).InformationAgent (onePacketN).playedInformation =>
    slotPrescribedComponent setup timeouts leaks bounds Initial horizon scheduler source
      scale nonnegative le_one agent.1 agent.2.1
  let keyed := fun (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
      (option : LateOption slots) =>
    lateComponent setup timeouts leaks bounds Initial horizon scheduler source
      scale nonnegative le_one agent.1 agent.2.1 option
  obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free
    (key := agentLateKey setup timeouts leaks bounds Initial horizon scheduler)
    (keyed := LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler)
    (unforcedLaw setup timeouts leaks bounds Initial horizon scheduler scale nonnegative le_one)
    prescribed keyed notFree
  have constant : onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source
    (slots := slots)
      scale nonnegative le_one agent = fun _ => prescribed agent := by
    funext part
    exact (same part).trans
      (keyedComponent_of_not_keyed prescribed keyed (fun owned => nonkeyed owned.1) (identify part))
  have actual := (onePacketN).agentBehavior_at (onePacketN).playedInformation fallback
    (fun agent => (weights (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
      agent)).bind
      (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source scale
        nonnegative
        le_one
        agent)) agent
  rw [← assembled, constant, PMF.bind_const] at actual
  rw [constant, PMF.bind_const, ← actual]
  exact localGain_self _ _ _ _ _

open Classical in
/-- The original pooled native witness bounds every member mixture once its
actual keyed component payoffs have a common affine score. Owing agents use
actual native completion; the other pools use their exact algebraic laws. -/
theorem componentGain_le_of_common_values {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (completes : CompletesPlay timeouts leaks Initial horizon scheduler)
    (assessment : (onePacketN).BehavioralAssessment) (source :
      setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots
      p))
    (fallback : ∀ who, (onePacketN).Policy who)
    (assembled : assessment.strategy = (onePacketN).agentBehavior (onePacketN).playedInformation
      fallback
      (fun agent => (weights (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
        agent)).bind
        (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source scale
          nonnegative
          le_one agent)))
    (pooled : ∀ (alternative : ∀ p,
        PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => onePacketPool setup timeouts leaks bounds Initial horizon scheduler agent =
            p),
        (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) (fun final => final.state)
            (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
              assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            ((alternative (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
              agent)).bind
              (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source scale
                nonnegative
                le_one agent)) else 0) ≤ 0)
    (continuation : (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
    (score : Option (LateKey setup timeouts leaks) → LateOption slots → ℝ) (error : ℝ)
    (values : ∀ agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      ownedKeyed (FreeAgent setup timeouts leaks bounds Initial horizon scheduler)
        (LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler) agent →
      ¬ OwingAgent setup timeouts leaks bounds Initial horizon scheduler agent →
      ∀ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        excludedPayoff agent.1 ≤ continuation agent ∧ ∀ option,
        |localValue (2 * horizon + 1) (fun final => final.state)
            (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
              assessment (who := agent.1)
            ⟨agent.2.1, decision⟩
            (lateComponent setup timeouts leaks bounds Initial horizon scheduler source scale
              nonnegative le_one agent.1 agent.2.1 option) -
          (excludedPayoff agent.1 + score
            (agentLateKey setup timeouts leaks bounds Initial horizon scheduler agent) option *
              (continuation agent - excludedPayoff agent.1))| ≤ error) :
    ∀ who (site : (onePacketN).InformationSite who)
      (alternative : PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler slots
        (onePacketPool setup timeouts leaks bounds Initial horizon scheduler ((onePacketN).agentAt
          site)))),
      localGain (2 * horizon + 1) (fun final => final.state)
        (exclusionBase setup timeouts parameter utility excludedPayoff leaks) assessment
          site
        (alternative.bind (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler
          source
          scale
          nonnegative le_one ((onePacketN).agentAt site))) ≤
        Fintype.card ((onePacketN).InformationAgent (onePacketN).playedInformation) * (2 * max
          error 0) := by
  classical
  have pooledLocal := pooled
  have boundNonneg : 0 ≤
      (Fintype.card ((onePacketN).InformationAgent (onePacketN).playedInformation) : ℝ) * (2 * max
        error 0) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (le_max_right _ _))
  intro who site alternative
  by_cases free : FreeAgent setup timeouts leaks bounds Initial horizon scheduler
    ((onePacketN).agentAt site)
  · exact (freeAgent_componentGain_nonpos setup timeouts leaks bounds horizon scheduler _ _
      assessment
      source scale nonnegative le_one weights pooledLocal site free alternative).trans boundNonneg
  by_cases owing : OwingAgent setup timeouts leaks bounds Initial horizon scheduler
    ((onePacketN).agentAt
    site)
  · rw [owingAgent_localGain_eq_zero setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff completes assessment site owing]
    exact boundNonneg
  by_cases keyed : LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler
    ((onePacketN).agentAt
    site)
  · have assembledGeneric := assembled
    dsimp only [onePacketComponent] at assembledGeneric
    exact freeKeyed_memberGain_le_of_common_values (T := (NP)) (N := (onePacketN))
      (Key := Option (LateKey setup timeouts leaks)) (Opt := LateOption slots)
      (2 * horizon + 1)
      ((menu).bounded Initial horizon scheduler) ((menu).decisionRecall Initial horizon scheduler)
      (fun final => final.state) (exclusionBase setup timeouts parameter utility excludedPayoff
        leaks) fallback
      (FreeAgent setup timeouts leaks bounds Initial horizon scheduler)
      (LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler)
      (agentLateKey setup timeouts leaks bounds Initial horizon scheduler)
      (OwingAgent setup timeouts leaks bounds Initial horizon scheduler)
      (unforcedLaw setup timeouts leaks bounds Initial horizon scheduler scale nonnegative le_one)
      (fun agent => slotPrescribedComponent setup timeouts leaks bounds Initial horizon scheduler
        source
        scale nonnegative le_one agent.1 agent.2.1)
      (fun agent option => lateComponent setup timeouts leaks bounds Initial horizon scheduler
        source
        scale nonnegative le_one agent.1 agent.2.1 (option : LateOption slots))
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
      (fun _ site debt law => owingAgent_localGain_eq_zero setup timeouts leaks bounds horizon
        scheduler
        parameter utility excludedPayoff completes assessment site debt law)
      continuation score error values who site ⟨keyed, free⟩ alternative
  · rw [nonkeyed_componentGain_eq_zero setup timeouts leaks bounds horizon scheduler _ _ assessment
      source
      scale nonnegative le_one weights fallback assembled site free keyed alternative]
    exact boundNonneg

end Vegas

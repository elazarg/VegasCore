/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerKeyedLate
import Vegas.Game.OnePacketLateUniform

/-! # Record laws at late deliveries with a common key

At two late deliveries of `who` with the same late-delivery key, neither free
nor owing, the beliefs' laws of operational records give every unit payoff of
the record expectations within four times the irregular ratios plus four times
the factorization error over one less it: the reach of a regular history is its
factored weight, the owner mass of the site's recall times a base weight, the
base laws of the two sites agree by the owner's hidden swap, and the irregular
histories carry little reach (`Vegas.keyedRecord_near`). So, with independent
hidden initial cells, the law of records at
a fixed late delivery of each key serves every late delivery with that key, up to
a vanishing drift (`Vegas.OnePacketBaseInputs.lateRecords_of_keyed`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter Finset

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

variable {setup leaks bounds horizon scheduler} in
open Classical in
/-- At a site with honest counterparts, the irregular reach at a stage is at
most the irregular ratio times the regular reach. -/
theorem OnePacketCounterpartInputs.irregular_reach_le
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment} {who : Player}
    {site : (onePacketN).InformationSite who}
    [Fintype ((onePacketN).InformationHistory who site.1)]
    (inputs : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
      targetSequence site) (n : ℕ) :
    ∑ history : (onePacketN).InformationHistory who site.1 with
        ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace,
      ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
      (Fintype.card ((onePacketN).InformationHistory who site.1) *
        (inputs.slack * inputs.scale n / inputs.floors n ^ inputs.depth)) *
      ∑ history : (onePacketN).InformationHistory who site.1 with
          ¬ ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace,
        ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal :=
  sum_reach_le_of_counterpart (targetSequence n).strategy
    (fun history : (onePacketN).InformationHistory who site.1 =>
      ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace)
    (inputs.counterpart n)
    (div_nonneg (mul_nonneg inputs.slack_nonneg (inputs.scale_nonneg n))
      (pow_nonneg (inputs.floors_pos n).le _))
    (fun history irregular => not_not.mpr (inputs.counterpart_regular n history irregular))
    fun history irregular => le_mul_of_tremble_counterpart (inputs.scale_nonneg n)
      (inputs.floors_pos n) (inputs.irregular_le n history irregular)
      (inputs.counterpart_ge n history irregular)

variable {setup leaks bounds horizon scheduler} in
open Classical in
/-- **Record laws at two late deliveries with one key.** At two late deliveries
of `who` with the same late-delivery key at which `who` owes no failure, under a
fully mixed Bayes assessment at stage `n` with operational steps and honest
counterparts at both sites, and a factorization error below one, the beliefs'
laws of operational records give every unit payoff of the record expectations
within four times the sum of the sites' irregular ratios plus four times the
factorization error over one less it. -/
theorem keyedRecord_near
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (coversInputs : bounds.CoversInputValues)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment} (n : ℕ)
    (mixed : (targetSequence n).IsFullyMixed)
    {antichain : (onePacketN).DecisionInformationAntichain}
    (bayes : BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n) antichain)
    {who : Player}
    {site₁ site₂ : (onePacketN).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup leaks who site₁.1 = lateKey setup leaks who site₂.1)
    (firstDebtFree : SiteDebtFree setup leaks bounds horizon scheduler site₁)
    (secondDebtFree : SiteDebtFree setup leaks bounds horizon scheduler site₂)
    (firstLate : LateDelivery setup leaks who site₁.1)
    (secondLate : LateDelivery setup leaks who site₂.1)
    (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      (fun n => (targetSequence n).strategy) who)
    (first : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
      targetSequence site₁)
    (second : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
      targetSequence site₂)
    (small : (1 + steps.error n) ^ (2 * horizon + 1) - 1 < 1)
    (payoff : List (Option (OperationalState setup leaks)) → ℝ)
    (unit : ∀ record, 0 ≤ payoff record ∧ payoff record ≤ 1) :
    |expect (((targetSequence n).belief who site₁).map fun history =>
        operationalRecord setup leaks bounds horizon scheduler history.1.trace) payoff -
      expect (((targetSequence n).belief who site₂).map fun history =>
        operationalRecord setup leaks bounds horizon scheduler history.1.trace) payoff| ≤
      4 * (Nat.card ((onePacketN).InformationHistory who site₁.1) *
          (first.slack * first.scale n / first.floors n ^ first.depth) +
        Nat.card ((onePacketN).InformationHistory who site₂.1) *
          (second.slack * second.scale n / second.floors n ^ second.depth)) +
      4 * ((1 + steps.error n) ^ (2 * horizon + 1) - 1) /
        (1 - ((1 + steps.error n) ^ (2 * horizon + 1) - 1)) := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let ε := (1 + steps.error n) ^ (2 * horizon + 1) - 1
  have εNonneg : 0 ≤ ε := by
    have := one_le_pow₀ (n := 2 * horizon + 1)
      (show (1 : ℝ) ≤ 1 + steps.error n by linarith [steps.error_nonneg n])
    simp only [ε]
    linarith
  let reach := fun history : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    ((onePacketN).historyReachWeight (targetSequence n).strategy history).toReal
  let base := fun history : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who history.trace *
      operationalWeight setup leaks who (steps.mass n)
        (operationalRecord setup leaks bounds horizon scheduler history.trace)
  let regular := fun history : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.trace
  have baseNonneg : ∀ history, 0 ≤ base history := fun history =>
    mul_nonneg (othersSourceWeight_nonneg _ _ history.trace)
      (operationalWeight_nonneg setup leaks (steps.mass_nonneg n) _)
  let scaleOf := fun past : List (application setup leaks).PlayerEntry =>
    ownerMass setup leaks bounds horizon scheduler ((targetSequence n).strategy who) past
  have scaleNonneg : ∀ past, 0 ≤ scaleOf past := fun past =>
    ownerMassFrom_nonneg setup leaks bounds horizon scheduler _ _ _
  -- The reach of a regular history is its factored weight.
  have closeAt : ∀ (site : (onePacketN).InformationSite who)
      {past : List (application setup leaks).PlayerEntry}
      {view : (application setup leaks).PlayerView}, site.1 = some (past, view) →
      ∀ history : (onePacketN).InformationHistory who site.1, regular history.1 →
      |reach history.1 - scaleOf past * base history.1| ≤ ε * (scaleOf past * base history.1) := by
    intro site past view atSite history isRegular
    have recalled : ownerRecall setup leaks who history.1.state = past := by
      apply ownerRecall_eq_of_infoOf setup leaks (view := view)
      rw [← onePacket_infoOf who history.1.trace, history.2, atSite]
    have factored := (onePacketReachFactorization steps).2 n history.1.trace isRegular
    have weightEq : factoredWeight sequence (fun n => (targetSequence n).strategy) steps n
        history.1.trace = scaleOf past * base history.1 := by
      unfold factoredWeight
      rw [recalled]
      simp only [scaleOf, base]
      ring
    rw [weightEq] at factored
    exact factored
  -- Each site has positive mass, carried by its regular histories.
  have positiveAt : ∀ site : (onePacketN).InformationSite who,
      0 < (onePacketN).informationMass (targetSequence n).strategy who site := fun site =>
    InformationModel.informationMass_pos_of_fullSupport _ _ mixed who site
  have bayesAt : ∀ (site : (onePacketN).InformationSite who)
      (history : (onePacketN).InformationHistory who site.1), site = site₁ ∨ site = site₂ →
      ((targetSequence n).belief who site history).toReal = reach history.1 /
        ∑' other : (onePacketN).InformationHistory who site.1, reach other.1 := by
    intro site history _
    let := Fintype.ofFinite ((onePacketN).InformationHistory who site.1)
    rw [belief_toReal_eq_div bayes (positiveAt site) history,
      informationMass_toReal_eq_sum, tsum_fintype]
  -- The irregular reach is small against the regular reach.
  have irregularAt : ∀ (site : (onePacketN).InformationSite who)
      (inputs : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
        targetSequence site),
      ∑' history : (onePacketN).InformationHistory who site.1,
          (if regular history.1 then 0 else reach history.1) ≤
        (Nat.card ((onePacketN).InformationHistory who site.1) *
          (inputs.slack * inputs.scale n / inputs.floors n ^ inputs.depth)) *
        ∑' history : (onePacketN).InformationHistory who site.1,
          if regular history.1 then reach history.1 else 0 := by
    intro site inputs
    let := Fintype.ofFinite ((onePacketN).InformationHistory who site.1)
    have bound := inputs.irregular_reach_le n
    rw [Nat.card_eq_fintype_card, tsum_fintype, tsum_fintype]
    simp only [not_not, sum_filter] at bound
    refine le_of_eq_of_le (sum_congr rfl fun history _ => (ite_not _ _ _).symm)
      (bound.trans_eq ?_)
    exact congrArg _ (sum_congr rfl fun history _ => rfl)
  -- Hence the regular base weights have positive total.
  have positiveBase : ∀ (site : (onePacketN).InformationSite who)
      {past : List (application setup leaks).PlayerEntry}
      {view : (application setup leaks).PlayerView}, site.1 = some (past, view) →
      (inputs : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
        targetSequence site) →
      0 < scaleOf past ∧ 0 < ∑' history : (onePacketN).InformationHistory who site.1,
        (if regular history.1 then base history.1 else 0) := by
    intro site past view atSite inputs
    let := Fintype.ofFinite ((onePacketN).InformationHistory who site.1)
    have irregular := irregularAt site inputs
    rw [tsum_fintype, tsum_fintype] at irregular
    rw [tsum_fintype]
    set ratio := (Nat.card ((onePacketN).InformationHistory who site.1) : ℝ) *
      (inputs.slack * inputs.scale n / inputs.floors n ^ inputs.depth)
    have ratioNonneg : 0 ≤ ratio :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg inputs.slack_nonneg
        (inputs.scale_nonneg n)) (pow_nonneg (inputs.floors_pos n).le _))
    have mass := positiveAt site
    have massPos : 0 < ∑ history : (onePacketN).InformationHistory who site.1,
        reach history.1 := by
      rw [← informationMass_toReal_eq_sum]
      exact ENNReal.toReal_pos mass.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
        ((onePacketN).informationMass_le_one _ who site (antichain who site)))
    have split : ∑ history : (onePacketN).InformationHistory who site.1, reach history.1 =
        (∑ history : (onePacketN).InformationHistory who site.1,
            if regular history.1 then reach history.1 else 0) +
          ∑ history : (onePacketN).InformationHistory who site.1,
            if regular history.1 then 0 else reach history.1 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun history _ => by split_ifs <;> simp
    have regularPos : 0 < ∑ history : (onePacketN).InformationHistory who site.1,
        if regular history.1 then reach history.1 else 0 := by
      by_contra notPos
      have regularNonneg : 0 ≤ ∑ history : (onePacketN).InformationHistory who site.1,
          if regular history.1 then reach history.1 else 0 :=
        sum_nonneg fun history _ => by split_ifs <;> simp [reach]
      have zero : ∑ history : (onePacketN).InformationHistory who site.1,
          (if regular history.1 then reach history.1 else 0) = 0 := by linarith
      rw [zero, mul_zero] at irregular
      have irregularNonneg : 0 ≤ ∑ history : (onePacketN).InformationHistory who site.1,
          if regular history.1 then 0 else reach history.1 :=
        sum_nonneg fun history _ => by split_ifs <;> simp [reach]
      linarith
    have regularLe : ∑ history : (onePacketN).InformationHistory who site.1,
        (if regular history.1 then reach history.1 else 0) ≤
        (1 + ε) * (scaleOf past * ∑ history : (onePacketN).InformationHistory who site.1,
          if regular history.1 then base history.1 else 0) := by
      rw [mul_sum, mul_sum]
      refine sum_le_sum fun history _ => ?_
      split_ifs with isRegular
      · have := closeAt site atSite history isRegular
        rw [abs_le] at this
        nlinarith [this.2]
      · simp
    have product : 0 < scaleOf past * ∑ history : (onePacketN).InformationHistory who site.1,
        if regular history.1 then base history.1 else 0 := by
      have : 0 < (1 + ε) * (scaleOf past * ∑ history : (onePacketN).InformationHistory who
          site.1, if regular history.1 then base history.1 else 0) :=
        lt_of_lt_of_le regularPos regularLe
      exact pos_of_mul_pos_right this (by linarith)
    have baseSumNonneg : 0 ≤ ∑ history : (onePacketN).InformationHistory who site.1,
        if regular history.1 then base history.1 else 0 :=
      sum_nonneg fun history _ => by split_ifs <;> simp [baseNonneg]
    exact ⟨pos_of_mul_pos_left product baseSumNonneg, pos_of_mul_pos_right product
      (scaleNonneg past)⟩
  obtain ⟨scale₁Pos, base₁Pos⟩ := positiveBase site₁ firstSite first
  obtain ⟨scale₂Pos, base₂Pos⟩ := positiveBase site₂ secondSite second
  set ρ₁ := (Nat.card ((onePacketN).InformationHistory who site₁.1) : ℝ) *
    (first.slack * first.scale n / first.floors n ^ first.depth)
  set ρ₂ := (Nat.card ((onePacketN).InformationHistory who site₂.1) : ℝ) *
    (second.slack * second.scale n / second.floors n ^ second.depth)
  have ρ₁Nonneg : 0 ≤ ρ₁ :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg first.slack_nonneg
      (first.scale_nonneg n)) (pow_nonneg (first.floors_pos n).le _))
  have ρ₂Nonneg : 0 ≤ ρ₂ :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg second.slack_nonneg
      (second.scale_nonneg n)) (pow_nonneg (second.floors_pos n).le _))
  have widen : ∀ (site : (onePacketN).InformationSite who) (ratio : ℝ), ratio ≤ ρ₁ + ρ₂ →
      ∑' history : (onePacketN).InformationHistory who site.1,
          (if regular history.1 then 0 else reach history.1) ≤
        ratio * ∑' history : (onePacketN).InformationHistory who site.1,
          (if regular history.1 then reach history.1 else 0) →
      ∑' history : (onePacketN).InformationHistory who site.1,
          (if regular history.1 then 0 else reach history.1) ≤
        (ρ₁ + ρ₂) * ∑' history : (onePacketN).InformationHistory who site.1,
          (if regular history.1 then reach history.1 else 0) := by
    intro site ratio le bound
    refine bound.trans (mul_le_mul_of_nonneg_right le ?_)
    exact tsum_nonneg fun history => by split_ifs <;> simp [reach]
  have agree := ownerSwap_baseLawAgrees_late wellFormed independent coversInputs (sequence n)
    (operationalWeight setup leaks who (steps.mass n)) firstSite secondSite
    sameKey firstDebtFree secondDebtFree firstLate secondLate payoff
  exact recordLaw_near_of_baseLaw (targetSequence n) site₁ site₂ reach base regular
    (fun _ => ENNReal.toReal_nonneg) (fun history _ => baseNonneg history) bayesAt
    (scaleOf past₁) (scaleOf past₂) ε (ρ₁ + ρ₂) scale₁Pos scale₂Pos small
    (closeAt site₁ firstSite) (closeAt site₂ secondSite)
    (widen site₁ ρ₁ (by linarith) (irregularAt site₁ first))
    (widen site₂ ρ₂ (by linarith) (irregularAt site₂ second)) payoff unit base₁Pos base₂Pos agree

variable [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

open Classical in
/-- **Late records.** For a well-formed setup with independent hidden initial
cells, along every fully mixed Bayes
sequence of assembled profiles, at late deliveries of agents that are neither
free nor owing, the beliefs' laws of operational records give the certificate's
lumped failure within a vanishing drift of its expectation under one record law
at each late-delivery key: the law at a fixed site with that key
(`Vegas.keyedRecord_near`). -/
theorem OnePacketBaseInputs.lateRecords_of_keyed
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ beliefDrift : ℕ → ℝ, Tendsto beliefDrift atTop (nhds 0) ∧
      ∀ n who, ∃ recordLaw : LateKey setup leaks →
          PMF (List (Option (OperationalState setup leaks))),
        ∀ (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
          |expect (((targetSequence n).belief who site).map fun history =>
              operationalRecord setup leaks bounds horizon scheduler history.1.trace)
              (lumpedFailure setup leaks bounds horizon scheduler
                (certificateLumping setup leaks bounds horizon scheduler sequence inputs.scale
                  inputs.scale_pos inputs.scale_le_one inputs.covers
                  (inputs.one_le_candidateCount setup leaks bounds horizon scheduler who)
                  inputs.slotsLe weights targetSequence assembled n who)
                (2 * horizon + 1) key option) -
            expect (recordLaw key)
              (lumpedFailure setup leaks bounds horizon scheduler
                (certificateLumping setup leaks bounds horizon scheduler sequence inputs.scale
                  inputs.scale_pos inputs.scale_le_one inputs.covers
                  (inputs.one_le_candidateCount setup leaks bounds horizon scheduler who)
                  inputs.slotsLe weights targetSequence assembled n who)
                (2 * horizon + 1) key option)| ≤ beliefDrift n := by
  let LateSite := fun {who : Player} (site : (onePacketN).InformationSite who) =>
    ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site)
  -- One site of each key.
  let recordLaw := fun (n : ℕ) (who : Player) (key : LateKey setup leaks) =>
    if found : ∃ site : (onePacketN).InformationSite who, LateSite site ∧
        lateKey setup leaks who site.1 = some key then
      ((targetSequence n).belief who found.choose).map fun history =>
        operationalRecord setup leaks bounds horizon scheduler history.1.trace
    else PMF.pure []
  let lumping := fun n who => certificateLumping setup leaks bounds horizon scheduler sequence
    inputs.scale inputs.scale_pos inputs.scale_le_one inputs.covers
    (inputs.one_le_candidateCount setup leaks bounds horizon scheduler who)
    inputs.slotsLe weights targetSequence assembled n who
  have lumpedUnit : ∀ n who key option record, 0 ≤ lumpedFailure setup leaks bounds horizon
      scheduler (lumping n who) (2 * horizon + 1) key option record ∧ lumpedFailure setup leaks
        bounds horizon scheduler (lumping n who) (2 * horizon + 1) key option record ≤ 1 := by
    intro n who key option record
    unfold lumpedFailure
    exact ⟨expect_nonneg _ _ fun image _ => ((lumping n who).failure_unit key image).1,
      expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) fun image => by
          have := (lumping n who).failure_unit key image
          rw [abs_le]
          constructor <;> linarith) 1
        fun image _ => ((lumping n who).failure_unit key image).2⟩
  have unitExpect : ∀ n who key option (law : PMF (List (Option (OperationalState setup leaks)))),
      0 ≤ expect law (lumpedFailure setup leaks bounds horizon scheduler (lumping n who)
        (2 * horizon + 1) key option) ∧ expect law (lumpedFailure setup leaks bounds horizon
          scheduler (lumping n who) (2 * horizon + 1) key option) ≤ 1 := by
    intro n who key option law
    exact ⟨expect_nonneg _ _ fun record _ => (lumpedUnit n who key option record).1,
      expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) fun record => by
          have := lumpedUnit n who key option record
          rw [abs_le]
          constructor <;> linarith) 1
        fun record _ => (lumpedUnit n who key option record).2⟩
  obtain ⟨beliefDrift, limit, holds⟩ := exists_uniform_of_sites setup leaks bounds horizon
    scheduler
    (fun n who site error => ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
      |expect (((targetSequence n).belief who site).map fun history =>
          operationalRecord setup leaks bounds horizon scheduler history.1.trace)
          (lumpedFailure setup leaks bounds horizon scheduler (lumping n who)
            (2 * horizon + 1) key option) -
        expect (recordLaw n who key) (lumpedFailure setup leaks bounds horizon scheduler
          (lumping n who) (2 * horizon + 1) key option)| ≤ error)
    (fun _ _ _ _ _ le bound key siteKey option => (bound key siteKey option).trans le)
    (fun who site => LateSite site)
    (fun who site late => by
      obtain ⟨notFree, notOwing, keyed⟩ := late
      obtain ⟨⟨past, view⟩, atSite, event, turn⟩ := lateDelivery_input setup leaks keyed.1
      have forced := forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
      have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
      let own := inputs.ownInputs weights targetSequence assembled mixed bayes who site notFree
        notOwing atSite turn decision
      let first := inputs.counterpartInputs weights targetSequence assembled mixed bayes who
        site notFree notOwing atSite turn
      obtain ⟨key, siteKey⟩ : ∃ key, lateKey setup leaks who site.1 = some key :=
        ⟨_, by rw [atSite]; rfl⟩
      have found : ∃ site' : (onePacketN).InformationSite who, LateSite site' ∧
          lateKey setup leaks who site'.1 = some key := ⟨site, ⟨notFree, notOwing, keyed⟩, siteKey⟩
      obtain ⟨⟨notFree', notOwing', keyed'⟩, foundKey⟩ := found.choose_spec
      obtain ⟨⟨past', view'⟩, atSite', event', turn'⟩ := lateDelivery_input setup leaks keyed'.1
      let second := inputs.counterpartInputs weights targetSequence assembled mixed bayes who
        found.choose notFree' notOwing' atSite' turn'
      let ε := fun n => (1 + own.steps.error n) ^ (2 * horizon + 1) - 1
      let ρ := fun n => (Nat.card ((onePacketN).InformationHistory who site.1) : ℝ) *
          (first.slack * first.scale n / first.floors n ^ first.depth) +
        (Nat.card ((onePacketN).InformationHistory who found.choose.1) : ℝ) *
          (second.slack * second.scale n / second.floors n ^ second.depth)
      let formula := fun n => 4 * ρ n + 4 * ε n / (1 - ε n)
      have εLimit : Tendsto ε atTop (nhds 0) := (onePacketReachFactorization own.steps).1
      have ρLimit : Tendsto ρ atTop (nhds 0) := by
        simpa using (tendsto_irregularRatio first.negligible _).add
          (tendsto_irregularRatio second.negligible _)
      have formulaLimit : Tendsto formula atTop (nhds 0) := by
        have quotient := (εLimit.const_mul 4).div (tendsto_const_nhds.sub εLimit)
          (by norm_num : (1 : ℝ) - 0 ≠ 0)
        simpa using (ρLimit.const_mul 4).add quotient
      have small : ∀ᶠ n in atTop, ε n < 1 :=
        εLimit.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      refine ⟨fun n => if ε n < 1 then formula n else 1, ?_, fun n key' siteKey' option => ?_⟩
      · refine formulaLimit.congr' ?_
        filter_upwards [small] with n smallAt
        simp only [smallAt, ↓reduceIte]
      · rw [siteKey, Option.some.injEq] at siteKey'
        subst siteKey'
        have lawEq : recordLaw n who key = ((targetSequence n).belief who found.choose).map
            fun history => operationalRecord setup leaks bounds horizon scheduler
              history.1.trace := by
          simp only [recordLaw, found, ↓reduceDIte]
        rw [lawEq]
        by_cases smallAt : ε n < 1
        · simp only [smallAt, ↓reduceIte]
          exact keyedRecord_near wellFormed independent inputs.coversInputs n (mixed n)
            (bayes n) atSite atSite' (siteKey.trans foundKey.symm) debtFree
            (siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing') keyed.1
            keyed'.1 own.steps first second smallAt _ (lumpedUnit n who key option)
        · simp only [smallAt, ↓reduceIte]
          have := unitExpect n who key option (((targetSequence n).belief who site).map
            fun history => operationalRecord setup leaks bounds horizon scheduler
              history.1.trace)
          have := unitExpect n who key option (((targetSequence n).belief who
            found.choose).map fun history => operationalRecord setup leaks bounds horizon
              scheduler history.1.trace)
          rw [abs_le]
          constructor <;> linarith)
  exact ⟨beliefDrift, limit, fun n who => ⟨recordLaw n who, fun site notFree notOwing keyed =>
    holds n who site ⟨notFree, notOwing, keyed⟩⟩⟩

end Vegas

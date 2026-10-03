/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceCounterfactualBeliefs

/-! # Foreign private risk in source-compatible information fibers

The focal owner's actual full recalled input is common throughout its native
information fiber. At source-compatible information its persistent flag is
therefore clear, and every owner's public miss is clear. Hidden escape is
exactly another owner's private recalled submission or opportunity risk.
The resulting finite union bound concerns actual counterfactual reach mass;
it does not assume or prove that this mass is negligible relative to clean reach.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.riskMenu (runtime service.setup) service.leaks
  service.bound
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound)
  (initialLaw service.setup) service.horizon service.scheduler

/-- The actual focal input, including earlier silent actions and their
before-views, excludes its own risk at every hidden compatible history. -/
theorem sourceCompatibleInfo_history_focal_clear (who : Player)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (history : (model).InformationHistory who site.1)
    (control : (app).Control) (current : history.1.state = some control) :
    (runtime service.setup).serviceRisk service.leaks service.bound who
      (control.execution.recall who) (control.execution.observe (app) who) = false := by
  obtain ⟨past, view, seen, _identity, clear⟩ :=
    service.sourceCompatibleInfo_clear who site.1 compatible
  have atState : (model).infoOf who history.1.trace = (app).observe who history.1.state :=
    (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.1.trace
  have observed : (app).observe who (some control) = some (past, view) :=
    (congrArg ((app).observe who) current).symm.trans
      (atState.symm.trans (history.2.trans seen))
  have actor : control.actor = some who := by
    by_contra inactive
    simp only [ReactiveApplication.observe, inactive, ↓reduceIte] at observed
    contradiction
  have input : (control.execution.recall who, control.execution.observe (app) who) =
      (past, view) := by
    apply Option.some.inj
    simpa only [ReactiveApplication.observe, actor, ↓reduceIte] using observed
  exact (congrArg (fun input => (runtime service.setup).serviceRisk service.leaks service.bound
    who input.1 input.2) input).trans clear

/-- An owner's hidden private risk, without conflating it with a public miss. -/
def privateRiskInformationHistories (who : Player) (site : (model).InformationSite who)
    (player : Player) : Set ((model).InformationHistory who site.1) :=
  {history | ∃ control, history.1.state = some control ∧
    ((runtime service.setup).recalledSubmissionRisk service.leaks service.bound player
      (control.execution.recall player) = true ∨
    (runtime service.setup).recalledOpportunityRisk service.leaks service.bound player
      (control.execution.recall player) = true)}

/-- Every escaped hidden history at compatible information has a foreign
private risk witness. Conversely, such a witness is an actual escaped history. -/
theorem sourceCompatibleInfo_escaped_iff_foreign_private_risk (who : Player)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (history : (model).InformationHistory who site.1) :
    history ∈ (service.cleanInformationHistories who site)ᶜ ↔
      ∃ player, player ≠ who ∧ history ∈ service.privateRiskInformationHistories who site player :=
    by
  change ¬ (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound
    history.1.state ↔ _
  cases current : history.1.state with
  | none =>
      constructor
      · intro escaped
        exact False.elim (escaped (by intro control same; cases same))
      · rintro ⟨player, _foreign, control, same, _privateRisk⟩
        rw [current] at same
        contradiction
  | some control =>
      have focal := ((runtime service.setup).serviceRisk_clear_iff service.leaks service.bound
        who _ _).mp (service.sourceCompatibleInfo_history_focal_clear who site compatible history
          control current) |>.1
      constructor
      · intro escaped
        have risky : ∃ player, (runtime service.setup).persistentServiceRisk service.leaks
            service.bound player (control.execution.recall player)
              (control.execution.observe (app) player) = true := by
          by_contra none
          apply escaped
          intro other same player
          cases Option.some.inj same
          exact Bool.eq_false_of_not_eq_true (fun risk => none ⟨player, risk⟩)
        obtain ⟨player, risky⟩ := risky
        have foreign : player ≠ who := by
          intro same
          subst player
          rw [focal] at risky
          contradiction
        refine ⟨player, foreign, control, current, ?_⟩
        have publicClear := service.sourceCompatibleInfo_history_no_public_miss who site compatible
          history player control current
        rcases ((runtime service.setup).persistentServiceRisk_iff service.leaks service.bound
          player _ _).mp risky with (missed | submitted) | opportunity
        · change control.execution.application.publicView.missedDecisionBy player = true at missed
          rw [publicClear] at missed
          contradiction
        · exact Or.inl submitted
        · exact Or.inr opportunity
      · rintro ⟨player, _foreign, other, same, privateRisk⟩ clear
        cases Option.some.inj (current.symm.trans same)
        have notRisky := clear control rfl player
        rcases privateRisk with submitted | opportunity
        · have risky := (runtime service.setup).persistentServiceRisk_of_recalled service.leaks
            service.bound player _ (control.execution.observe (app) player) submitted
          rw [notRisky] at risky
          contradiction
        · have risky := (runtime service.setup).persistentServiceRisk_of_opportunityRecall
            service.leaks service.bound player _ (control.execution.observe (app) player)
            opportunity
          rw [notRisky] at risky
          contradiction

/-- Actual escaped counterfactual mass is bounded by the finite sum of
foreign private-risk masses. Focal waiting likelihood is already canceled by
the counterfactual definition; foreign waiting likelihood remains in each term. -/
theorem counterfactualInformationMass_escaped_le_foreign_private_risk
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1) :
    service.counterfactualInformationMass profile who site
        (service.cleanInformationHistories who site)ᶜ ≤
      ∑ player ∈ Finset.univ.erase who, service.counterfactualInformationMass profile who site
        (service.privateRiskInformationHistories who site player) := by
  classical
  unfold counterfactualInformationMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro history _
  by_cases escaped : history ∈ (service.cleanInformationHistories who site)ᶜ
  · rw [Set.indicator_of_mem escaped]
    obtain ⟨player, foreign, risky⟩ :=
      (service.sourceCompatibleInfo_escaped_iff_foreign_private_risk who site compatible history).mp
        escaped
    calc
      _ = (service.privateRiskInformationHistories who site player).indicator
          (fun current => (model).counterfactualReachProbability profile who current.1.trace)
          history := (Set.indicator_of_mem risky _).symm
      _ ≤ _ := Finset.single_le_sum (fun other _ => Set.indicator_nonneg
        (fun current _ => (model).counterfactualReachProbability_nonneg profile who current.1.trace)
        history) (Finset.mem_erase.mpr ⟨foreign, Finset.mem_univ player⟩)
  · rw [Set.indicator_of_notMem escaped]
    apply Finset.sum_nonneg
    intro player _
    exact Set.indicator_nonneg
      (fun current _ => (model).counterfactualReachProbability_nonneg profile who current.1.trace)
      history

/-- The classifier supplies a genuinely legal clean witness. Full mixing
makes that actual witness's counterfactual weight positive, hence the clean
denominator is positive even when its limiting reach probability vanishes. -/
theorem counterfactualInformationMass_clean_pos_of_fullSupport
    (profile : ∀ who, (model).BehavioralPolicy who)
    (full : ∀ player (site : (model).InformationSite player) choice,
      choice ∈ (profile player site.1).support)
    (who : Player) (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1) :
    0 < service.counterfactualInformationMass profile who site
      (service.cleanInformationHistories who site) := by
  classical
  obtain ⟨_sourceProfile, _turns, _timing, _admitted, _effective, history, remaining, execution,
    current, observed, _supported, allClear, _clear⟩ := compatible
  let witness : (model).InformationHistory who site.1 := ⟨history, observed⟩
  have member : witness ∈ service.cleanInformationHistories who site := by
    intro control same player
    have controlEq : (⟨remaining, some who, execution⟩ : (app).Control) = control :=
      Option.some.inj (current.symm.trans same)
    cases controlEq
    exact allClear player
  have positive := (model).historyReachWeight_pos_of_fullSupport profile full history
  have finite : (model).historyReachWeight profile history ≠ ⊤ := by
    unfold InformationModel.historyReachWeight
    exact PMF.apply_ne_top _ _
  have reachPositive := ENNReal.toReal_pos positive.ne' finite
  rw [(model).historyReachProbability_eq_player_mul_counterfactual profile who history.trace]
    at reachPositive
  have counterfactualPositive : 0 <
      (model).counterfactualReachProbability profile who history.trace :=
    pos_of_mul_pos_right reachPositive ((model).playerReachProbability_nonneg profile who
      history.trace)
  unfold counterfactualInformationMass
  apply Finset.sum_pos'
  · intro hidden _
    exact Set.indicator_nonneg
      (fun current _ => (model).counterfactualReachProbability_nonneg profile who current.1.trace)
      hidden
  · refine ⟨witness, Finset.mem_univ witness, ?_⟩
    rw [Set.indicator_of_mem member]
    exact counterfactualPositive

/-- Conditional escaped mass is bounded by actual foreign private-risk
counterfactual mass divided by the actual positive clean denominator. No rate
bound is supplied: asymptotic control still requires this ratio to vanish. -/
theorem bayesBelief_escaped_le_foreign_private_risk
    (profile : ∀ who, (model).BehavioralPolicy who)
    (full : ∀ player (site : (model).InformationSite player) choice,
      choice ∈ (profile player site.1).support)
    (who : Player) (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1) :
    let belief := (model).bayesBelief profile who site
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler who site)
      ((model).informationMass_pos_of_fullSupport profile full who site)
    (belief.toOuterMeasure (service.cleanInformationHistories who site)ᶜ).toReal ≤
      (∑ player ∈ Finset.univ.erase who, service.counterfactualInformationMass profile who site
        (service.privateRiskInformationHistories who site player)) /
      service.counterfactualInformationMass profile who site
        (service.cleanInformationHistories who site) := by
  classical
  intro belief
  have positive := (model).informationMass_pos_of_fullSupport profile full who site
  have cleanPositive := service.counterfactualInformationMass_clean_pos_of_fullSupport profile
    full who site compatible
  have escapedNonnegative := service.counterfactualInformationMass_nonnegative profile who site
    (service.cleanInformationHistories who site)ᶜ
  have numeratorNonnegative : 0 ≤ ∑ player ∈ Finset.univ.erase who,
      service.counterfactualInformationMass profile who site
        (service.privateRiskInformationHistories who site player) :=
    Finset.sum_nonneg fun player _ => service.counterfactualInformationMass_nonnegative profile
      who site (service.privateRiskInformationHistories who site player)
  obtain ⟨totalPositive, _cleanRatio, escapedRatio⟩ :=
    service.bayesBelief_clean_escaped_ratio profile who site positive
  rw [escapedRatio]
  exact (div_le_div_of_nonneg_right
    (service.counterfactualInformationMass_escaped_le_foreign_private_risk profile who site
      compatible) totalPositive.le).trans
    (div_le_div_of_nonneg_left numeratorNonnegative cleanPositive (by linarith))

end Vegas.AsyncServiceSpec

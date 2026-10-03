/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSourceSites
import Vegas.Pending.ReactiveCleanPrefixProbability
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveOwnPlay
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Counterfactual clean and escaped mass at native information

The actual recalled responses and their before-views determine the owner's
complete action likelihood, including earlier silent deferrals. It is common
to every hidden history at the current decision information. At supported
information its positive factor cancels from Bayes normalization. Clean and
escaped probabilities are therefore ratios of opponent-and-nature reach
masses, without a first-turn restriction or a source posterior premise.

These laws use the actual response menu, including a larger menu than the
source-compatible witness. Source-information transport and relative escape
estimates are separate obligations.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
variable (responseMenu : (application service.setup service.leaks).ResponseMenu)

local notation "menu" => responseMenu
local notation "model" => ReactiveApplication.ResponseMenu.information responseMenu
  (initialLaw service.setup) service.horizon service.scheduler

/-- Likelihood of every recorded own response at its actual preceding input.
Silence is an action in this record, so deferral probabilities are included. -/
def recalledOwnReach (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who) : ℝ :=
  (model).ownPlayReachProbability (profile who)
    ((app).recallOwnPlay (site.1.elim [] Prod.fst))

omit [Fintype Player] in
/-- Actual own recall supplies the common player-reach factor throughout a
native information fiber, including histories reached after silent deferrals. -/
theorem playerReach_eq_recalledOwnReach
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who) (history : (model).InformationHistory who site.1) :
    (model).playerReachProbability profile who history.1.trace =
      service.recalledOwnReach responseMenu profile who site := by
  rcases site with ⟨observed, decision⟩
  cases observed with
  | none =>
      obtain ⟨_, _, response, member⟩ := decision
      change some response = none at member
      contradiction
  | some input =>
      rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
        (menu).ownPlay_of_info_some (initialLaw service.setup) service.horizon service.scheduler
          who history.1 input.1 input.2 history.2]
      rfl

/-- A supported information site cannot have zero recorded own likelihood. -/
theorem recalledOwnReach_pos
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who)
    (positive : 0 < (model).informationMass profile who site) :
    0 < service.recalledOwnReach responseMenu profile who site :=
  (model).commonPlayerReach_pos _
    (service.playerReach_eq_recalledOwnReach responseMenu profile who site) positive

/-- Opponent and nature reach mass of an event in the actual information
fiber. Focal own-response likelihood is absent from this finite sum. -/
def counterfactualInformationMass
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who)
    (event : Set ((model).InformationHistory who site.1)) : ℝ :=
  ∑ history : (model).InformationHistory who site.1,
    event.indicator (fun current =>
      (model).counterfactualReachProbability profile who current.1.trace) history

theorem counterfactualInformationMass_nonnegative
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who) (event : Set ((model).InformationHistory who site.1)) :
    0 ≤ service.counterfactualInformationMass responseMenu profile who site event := by
  classical
  apply Finset.sum_nonneg
  intro history _
  exact Set.indicator_nonneg (fun current _ =>
    (model).counterfactualReachProbability_nonneg profile who current.1.trace) history

/-- The full native information mass factors through the actual complete
recorded own likelihood; no common-reach hypothesis is supplied by callers. -/
theorem informationMass_eq_recalled_mul_counterfactual
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who) :
    ((model).informationMass profile who site).toReal =
      service.recalledOwnReach responseMenu profile who site *
        service.counterfactualInformationMass responseMenu profile who site Set.univ := by
  classical
  unfold InformationModel.informationMass
  rw [ENNReal.tsum_toReal_eq
    (f := fun history : (model).InformationHistory who site.1 =>
      (model).historyReachWeight profile history.1) (fun history => PMF.apply_ne_top _ _),
    tsum_fintype]
  unfold counterfactualInformationMass
  simp only [Set.indicator_univ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro history _
  rw [(model).historyReachProbability_eq_player_mul_counterfactual profile who history.1.trace,
    service.playerReach_eq_recalledOwnReach responseMenu profile who site history]

theorem counterfactualInformationMass_pos
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who)
    (positive : 0 < (model).informationMass profile who site) :
    0 < service.counterfactualInformationMass responseMenu profile who site Set.univ := by
  have massPositive := ENNReal.toReal_pos positive.ne'
    (ne_of_lt (((model).informationMass_le_one profile who site
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler who site)).trans_lt ENNReal.one_lt_top))
  rw [service.informationMass_eq_recalled_mul_counterfactual responseMenu profile who site]
    at massPositive
  exact pos_of_mul_pos_right massPositive
    (service.recalledOwnReach_pos responseMenu profile who site positive).le

/-- Every native history's conditional weight is exactly its counterfactual
reach divided by the total counterfactual mass at that information. -/
theorem bayesBelief_apply_counterfactual
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who) (positive : 0 < (model).informationMass profile who site)
    (history : (model).InformationHistory who site.1) :
    ((model).bayesBelief profile who site
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler who site) positive history).toReal =
      (model).counterfactualReachProbability profile who history.1.trace /
        service.counterfactualInformationMass responseMenu profile who site Set.univ := by
  rw [(model).bayesBelief_apply, ENNReal.toReal_div,
    (model).historyReachProbability_eq_player_mul_counterfactual profile who history.1.trace,
    service.playerReach_eq_recalledOwnReach responseMenu profile who site history,
    service.informationMass_eq_recalled_mul_counterfactual responseMenu profile who site]
  exact mul_div_mul_left _ _
    (service.recalledOwnReach_pos responseMenu profile who site positive).ne'

/-- The same cancellation applies to any clean or escaped event, retaining
the actual hidden native histories and all pending traffic uncertainty. -/
theorem bayesBelief_event_counterfactual
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who) (positive : 0 < (model).informationMass profile who site)
    (event : Set ((model).InformationHistory who site.1)) :
    (((model).bayesBelief profile who site
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler who site) positive).toOuterMeasure event).toReal =
      service.counterfactualInformationMass responseMenu profile who site event /
        service.counterfactualInformationMass responseMenu profile who site Set.univ := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq (fun history => by
    by_cases member : history ∈ event
    · rw [Set.indicator_of_mem member]
      exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem member]
      exact ENNReal.zero_ne_top), tsum_fintype]
  unfold counterfactualInformationMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro history _
  by_cases member : history ∈ event
  · rw [Set.indicator_of_mem member, Set.indicator_of_mem member]
    exact service.bayesBelief_apply_counterfactual responseMenu profile who site positive history
  · simp only [Set.indicator_of_notMem member, ENNReal.toReal_zero, zero_div]

/-- An actual hidden history at compatible native information cannot contain
any owner's public miss. Only private recalled risk can escape unseen. -/
theorem sourceCompatibleInfo_history_no_public_miss (who : Player)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (history : (model).InformationHistory who site.1) (player : Player)
    (control : (app).Control) (current : history.1.state = some control) :
    control.execution.application.publicView.missedDecisionBy player = false := by
  obtain ⟨past, view, seen, _identity, _clear⟩ :=
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
  have input : site.1 = some (control.execution.recall who,
      control.execution.observe (app) who) := by
    rw [seen]
    simpa only [ReactiveApplication.observe, actor, ↓reduceIte] using observed.symm
  exact service.sourceCompatibleInfo_no_public_miss who _ _ (input ▸ compatible) player

/-- At compatible information the counterfactual public-miss event has
exactly zero mass, without a probability estimate or first-turn restriction. -/
theorem counterfactualInformationMass_public_miss_zero
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1) (player : Player) :
    service.counterfactualInformationMass responseMenu profile who site
      {history | ∃ control, history.1.state = some control ∧
        control.execution.application.publicView.missedDecisionBy player = true} = 0 := by
  classical
  unfold counterfactualInformationMass
  apply Finset.sum_eq_zero
  intro history _
  apply Set.indicator_of_notMem
  rintro ⟨control, current, missed⟩
  have clear := service.sourceCompatibleInfo_history_no_public_miss responseMenu who site
    compatible history player control current
  rw [clear] at missed
  contradiction

/-- The information histories whose actual endpoint has no persistent risk
for any owner. Current transient opportunities are not removed from the event. -/
def cleanInformationHistories (who : Player) (site : (model).InformationSite who) :
    Set ((model).InformationHistory who site.1) :=
  {history | (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound
    history.1.state}

/-- Clean and escaped native mass form an exact partition after the owner's
entire recalled-action likelihood cancels, even at a late current opportunity. -/
theorem bayesBelief_clean_escaped_ratio
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who)
    (positive : 0 < (model).informationMass profile who site) :
    let clean := service.cleanInformationHistories responseMenu who site
    let cleanMass := service.counterfactualInformationMass responseMenu profile who site clean
    let escapedMass := service.counterfactualInformationMass responseMenu profile who site cleanᶜ
    let belief := (model).bayesBelief profile who site
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler who site) positive
    0 < cleanMass + escapedMass ∧
      (belief.toOuterMeasure clean).toReal = cleanMass / (cleanMass + escapedMass) ∧
      (belief.toOuterMeasure cleanᶜ).toReal = escapedMass / (cleanMass + escapedMass) := by
  classical
  intro clean cleanMass escapedMass belief
  have partition : service.counterfactualInformationMass responseMenu profile who site Set.univ =
      cleanMass + escapedMass := by
    dsimp only [cleanMass, escapedMass]
    unfold counterfactualInformationMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro history _
    by_cases member : history ∈ clean <;>
      simp only [Set.indicator, member, Set.mem_compl_iff, Set.mem_univ,
        not_true_eq_false, not_false_eq_true, ↓reduceIte, add_zero, zero_add]
  refine ⟨partition ▸ service.counterfactualInformationMass_pos responseMenu profile who site
    positive, ?_, ?_⟩
  · exact (service.bayesBelief_event_counterfactual responseMenu profile who site positive
      clean).trans
      (congrArg (fun total => cleanMass / total) partition)
  · exact (service.bayesBelief_event_counterfactual responseMenu profile who site positive
      cleanᶜ).trans
      (congrArg (fun total => escapedMass / total) partition)

end Vegas.AsyncServiceSpec

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceCompatibleRecall
import GameTheory.Analysis.Protocol.SequentialOneShot

/-! # Whole continuation rationality at free native information

A source-compatible owner input remembers only source-compatible preceding
inputs. A free input therefore has only free own decision descendants, in any
actual response menu. Consistency converts single-site comparisons at those
free sites into whole-policy optimality, without a payoff or audit restriction.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks

private abbrev freeModel
    (responseMenu : (application service.setup service.leaks).ResponseMenu) :=
  responseMenu.information (initialLaw service.setup) service.horizon service.scheduler

private theorem compatible_recorded_input
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (who : Player) (site : (freeModel service responseMenu).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (input : (app).Info)
    (remembered : input ∈ ((freeModel service responseMenu).recordAt who site.1).map Prod.fst) :
    service.sourceCompatibleInfo who input := by
  obtain ⟨past, view, observed, _identity, _clear⟩ :=
    service.sourceCompatibleInfo_clear who site.1 compatible
  obtain ⟨history, _running, _action, _member⟩ := site.2
  have recorded := (responseMenu.decisionRecall (initialLaw service.setup) service.horizon
    service.scheduler).recordAt_eq_ownPlay who site history
  rw [recorded, responseMenu.ownPlay_of_info_some (initialLaw service.setup) service.horizon
    service.scheduler who history.1 past view (history.2.trans observed)] at remembered
  obtain ⟨pair, member, rfl⟩ := List.mem_map.mp remembered
  exact service.sourceCompatibleInfo_ownPlay who past view (observed ▸ compatible)
    pair.1 pair.2 member

open Classical in
/-- A whole alternative preserving the assessment's laws at every compatible
own decision cannot improve from any site. Only genuine free-site comparisons
are needed; no rationality at an unfinished prescribed decision is assumed. -/
theorem sourceCompatibleInfo_agree_continuation_le
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (assessment : (freeModel service responseMenu).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (responseMenu.decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler))
    (certificate : (responseMenu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).WellFoundedHistories)
    (payoff : Player → (responseMenu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).History → ℝ)
    (freeOptimal : ∀ who (site : (freeModel service responseMenu).InformationSite who),
      ¬ service.sourceCompatibleInfo who site.1 →
      ∀ law : PMF ((freeModel service responseMenu).Choice who site.1),
        (assessment.continuationContext certificate site (payoff who)).value
          ((assessment.strategy who).withLaw site.1 law) ≤
        (assessment.continuationContext certificate site (payoff who)).value
          (assessment.strategy who))
    (who : Player) (site : (freeModel service responseMenu).InformationSite who)
    (alternative : (freeModel service responseMenu).BehavioralPolicy who)
    (agrees : ∀ current : (freeModel service responseMenu).InformationSite who,
      service.sourceCompatibleInfo who current.1 →
        alternative current.1 = assessment.strategy who current.1) :
    (assessment.continuationContext certificate site (payoff who)).value alternative ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (assessment.strategy who) := by
  apply consistent.continuation_value_le_of_locallyOptimal
    (freeModel service responseMenu)
    (responseMenu.decisionRecall (initialLaw service.setup) service.horizon service.scheduler)
    (fun player info law => law =
      (Profile.update (sig := (freeModel service responseMenu).behavioralSignature)
        assessment.strategy who alternative) player info)
    payoff certificate _ who site alternative (by
      intro later
      simp only [Profile.update_same])
  intro player current law allowed
  by_cases same : player = who
  · subst player
    simp only [Profile.update_same] at allowed
    subst law
    by_cases compatible : service.sourceCompatibleInfo who current.1
    · rw [agrees current compatible, InformationModel.BehavioralPolicy.withLaw_eq_self]
    · exact freeOptimal who current compatible _
  · rw [Profile.update_of_ne _ _ same] at allowed
    rw [allowed, InformationModel.BehavioralPolicy.withLaw_eq_self]

open Classical in
/-- The actual assessment's single-site free comparisons already imply
whole-policy optimality at every free site. Only the owner's future free sites
can be changed by a splice at that site; compatible sites remain unchanged. -/
theorem sourceCompatibleInfo_free_optimal
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (assessment : (freeModel service responseMenu).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (responseMenu.decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler))
    (certificate : (responseMenu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).WellFoundedHistories)
    (payoff : Player → (responseMenu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).History → ℝ)
    (freeOptimal : ∀ who (site : (freeModel service responseMenu).InformationSite who),
      ¬ service.sourceCompatibleInfo who site.1 →
      ∀ law : PMF ((freeModel service responseMenu).Choice who site.1),
        (assessment.continuationContext certificate site (payoff who)).value
          ((assessment.strategy who).withLaw site.1 law) ≤
        (assessment.continuationContext certificate site (payoff who)).value
          (assessment.strategy who))
    (who : Player) (site : (freeModel service responseMenu).InformationSite who)
    (incompatible : ¬ service.sourceCompatibleInfo who site.1) :
    (assessment.continuationContext certificate site (payoff who)).IsLocallyOptimal
      Set.univ (assessment.strategy who) := by
  classical
  have integrable (alternative : (freeModel service responseMenu).BehavioralPolicy who) :
      (assessment.continuationContext certificate site (payoff who)).IntegrableAt alternative :=
    payoffIntegrable_of_finite _ _
  apply Context.isLocallyOptimal_iff_of_integrable (integrable (assessment.strategy who))
    (fun alternative _ => integrable alternative) |>.mpr
  intro alternative _
  let replacement := (assessment.strategy who).spliceAfter (freeModel service responseMenu)
    alternative site.1
  have preserved (current : (freeModel service responseMenu).InformationSite who)
      (compatible : service.sourceCompatibleInfo who current.1) :
      replacement current.1 = assessment.strategy who current.1 := by
    have different : current.1 ≠ site.1 := fun same => incompatible (same ▸ compatible)
    have unremembered : site.1 ∉
        ((freeModel service responseMenu).recordAt who current.1).map Prod.fst :=
      fun remembered => incompatible (service.compatible_recorded_input responseMenu who current
        compatible site.1 remembered)
    simp only [replacement, InformationModel.BehavioralPolicy.spliceAfter,
      different, unremembered, false_or, ↓reduceIte]
  have comparison := service.sourceCompatibleInfo_agree_continuation_le responseMenu assessment
    consistent certificate payoff freeOptimal who site replacement preserved
  have sameValue :
      (assessment.continuationContext certificate site (payoff who)).value replacement =
        (assessment.continuationContext certificate site (payoff who)).value alternative := by
    have contexts := assessment.continuationContext_eq_truncated_of_bounded certificate
      (responseMenu.bounded (initialLaw service.setup) service.horizon service.scheduler)
      site (payoff who)
    rw [contexts]
    have truncatedIntegrable (policy : (freeModel service responseMenu).BehavioralPolicy who) :
        (assessment.truncatedContinuationContext site (payoff who)
          (2 * service.horizon + 1)).IntegrableAt policy := payoffIntegrable_of_finite _ _
    have firstTower := assessment.continuationContextWith_value_tower
      ((freeModel service responseMenu).truncatedRunner (2 * service.horizon + 1)) site
      (payoff who) replacement (truncatedIntegrable replacement)
    have secondTower := assessment.continuationContextWith_value_tower
      ((freeModel service responseMenu).truncatedRunner (2 * service.horizon + 1)) site
      (payoff who) alternative (truncatedIntegrable alternative)
    refine firstTower.trans ((congrArg (expect (assessment.belief who site)) ?_).trans
      secondTower.symm)
    funext history
    exact congrArg (fun law => expect law (payoff who))
      ((freeModel service responseMenu).runBehavioralFrom_spliceAfter_eq
        (responseMenu.decisionRecall (initialLaw service.setup) service.horizon service.scheduler)
        assessment.strategy who site alternative history (2 * service.horizon + 1))
  rw [sameValue] at comparison
  exact comparison

end Vegas.AsyncServiceSpec

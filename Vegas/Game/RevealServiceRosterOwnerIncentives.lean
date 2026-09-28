/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterOwnerValue
import Vegas.Game.RevealServiceRosterOwnerHazard
import Vegas.Game.RevealSourcePayoffBounds

/-! # Owner deviations compare to the original source assessment

An unopened owner's local native lottery induces a lawful binary source
lottery. Only the prescribed value changes under conditioning on earlier
waiting, and its error is bounded by the passed timing mass times the source
continuation range. The alternative is an actual source behavioral deviation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

section

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)
  (reveals : setup.program.RevealOnly)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (admission : CommitmentInterface setup.program)
  (source : (setup.informationModel admission).BehavioralAssessment)
  (mixed : source.IsFullyMixed)
  (timing : TimingLaw setup rosters)
  (timingFull : ∀ event who owned, (timing event who owned).FullSupport)

open Classical in
include reveals openable mixed timingFull in
theorem roster_owner_comparison_of_posterior
    (assessment : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : assessment.strategy = rosterPerturbedProfile setup leaks bounds rosters network
      admission source timing)
    (who : Player)
    (site : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (observed : site.1 = some (past, view))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (grant : view.application.publicView.serviceGrant = some event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks who event view = some (candidate, raw))
    (fresh : rosterFresh? setup leaks rosters who past view =
      some ((runtime setup).windowOpening leaks event candidate raw))
    (unopened : ¬ ∃ entry ∈ past.drop (rosterOffset setup rosters who event),
      entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (inside : past.length - rosterOffset setup rosters who event < (rosters event).count who)
    (sourceSite : (setup.informationModel admission).InformationSite who)
    (choiceLaw : sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission
      source.strategy) who view =
        (source.strategy who sourceSite.1).map (fun choice => OwnAction.disclosure choice.1))
    (posterior : (assessment.stateBelief who site).map (fun state => state.bind fun current =>
      sourcePrefix? setup event.val current.execution.application.config) =
        source.stateBelief who sourceSite)
    (law : FinDist (((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).Choice who site.1))
    (utility : State L setup.program.terminalCtx → ℝ)
    (range weight : ℝ) (rangeNonnegative : 0 ≤ range)
    (timingBound : (timing event who owned).timingPrefix
      (past.length - rosterOffset setup rosters who event) ≤ weight)
    (valueRange :
      let value := fun disclose => (source.stateBelief who sourceSite).expect (fun state =>
        ((setup.protocolStep state (fun _ => some (.reveal who 0 disclose))).bind
          (setup.continuationLaw (setup.decodeBehavioralProfile admission source.strategy))).expect
            utility)
      |value true - value false| ≤ range) :
    let model := (rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let comparison := model.assessmentComparison
      (fun final => sourceReadout setup leaks final.state)
        (2 * (rosterPlan setup rosters).length + 1) assessment who
        (site, (assessment.strategy who).withLaw site.1 law)
    ∃ deviation : (setup.informationModel admission).AssessmentDeviation who,
      let original := (setup.informationModel admission).assessmentComparison
        (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
          source who deviation
      comparison.alternative.expect (fun value => value.elim 0 utility) -
          comparison.prescribed.expect (fun value => value.elim 0 utility) ≤
        original.alternative.expect (fun value => value.elim 0 utility) -
          original.prescribed.expect (fun value => value.elim 0 utility) + weight * range := by
  intro model comparison
  let joint : Bool → Player → Option (OwnAction Player L) :=
    fun disclose _ => some (.reveal who 0 disclose)
  let values := fun disclose => (source.stateBelief who sourceSite).expect (fun state =>
    ((setup.protocolStep state (joint disclose)).bind
      (setup.continuationLaw (setup.decodeBehavioralProfile admission source.strategy))).expect
        utility)
  let choice := sourceChoiceLaw setup leaks
    (setup.decodeBehavioralProfile admission source.strategy) who view
  let q := choice.prob true
  let count := past.length - rosterOffset setup rosters who event
  let remaining := FinDist.deferredRemaining q (timing event who owned) (count + 1)
  let predicate := {option : model.Choice who site.1 | option.1.getD ⟨none⟩ =
    (runtime setup).windowOpening leaks event candidate raw}
  let immediate := law.probOf predicate
  have aNonnegative : 0 ≤ immediate := ENNReal.toReal_nonneg
  have aBounded : immediate ≤ 1 := by
    change law.probOf predicate ≤ 1
    rw [← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_const law (1 : ℝ)]
    apply FinDist.expect_mono
    intro option _
    split <;> norm_num
  have full : choice.FullSupport := by
    dsimp only [choice]
    rw [choiceLaw]
    exact setup.reveal_choice_fullSupport reveals admission source mixed who sourceSite
  have qSmall : q < 1 := by
    have total := choice.sum_prob
    simp only [Fintype.sum_bool] at total
    have positive := FinDist.prob_pos_iff.mpr (full false)
    dsimp only [q]
    linarith
  have scalar := FinDist.deferredRemaining_local_comparison q (choice.prob_nonneg true) qSmall
    (timing event who owned) count immediate aNonnegative aBounded (values true) (values false)
  let replacement := immediate + (1 - immediate) * remaining
  have lower : 0 ≤ replacement := scalar.1
  have upper : replacement ≤ 1 := scalar.2.1
  have representatives (disclose : Bool) :
      ∃ action : (setup.informationModel admission).Choice who sourceSite.1,
        OwnAction.disclosure action.1 = disclose := by
    have fullSource := setup.reveal_choice_fullSupport reveals admission source mixed who sourceSite
    obtain ⟨action, _, same⟩ := FinDist.support_map .. ▸ fullSource disclose
    exact ⟨action, same⟩
  let representative := fun disclose => (representatives disclose).choose
  have represents (disclose : Bool) : OwnAction.disclosure (representative disclose).1 = disclose :=
    (representatives disclose).choose_spec
  let sourceLaw := FinDist.mix replacement lower upper
    (FinDist.pure (representative true)) (FinDist.pure (representative false))
  have sourceProbability :
      (sourceLaw.map (fun action => OwnAction.disclosure action.1)).prob true = replacement := by
    simp only [sourceLaw, FinDist.map_mix, FinDist.map_pure, represents, FinDist.prob_mix]
    norm_num [FinDist.prob_pure_eq_ite]
  let sourceContext := source.continuationContext sourceSite
    (fun final => (setup.protocolReadout final.state).elim 0 utility)
    (instructionCount setup.program + 1)
  have sourceAlternative := setup.reveal_local_value_binary admission reveals source who sourceSite
    sourceLaw joint (fun _ => rfl) utility
  change sourceContext.value ((source.strategy who).withLaw sourceSite.1 sourceLaw) = _
    at sourceAlternative
  dsimp only at sourceAlternative
  rw [sourceProbability] at sourceAlternative
  change sourceContext.value ((source.strategy who).withLaw sourceSite.1 sourceLaw) =
    replacement * values true + (1 - replacement) * values false at sourceAlternative
  have sourcePrescribed := setup.reveal_local_value_binary admission reveals source who sourceSite
    (source.strategy who sourceSite.1) joint (fun _ => rfl) utility
  simp only [InformationModel.BehavioralPolicy.withLaw_eq_self] at sourcePrescribed
  rw [← choiceLaw] at sourcePrescribed
  change sourceContext.value (source.strategy who) =
    q * values true + (1 - q) * values false at sourcePrescribed
  let targetContext := assessment.continuationContext site
    (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
    (2 * (rosterPlan setup rosters).length + 1)
  have targetAlternative := roster_owner_context_value setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull assessment strategy who event owned site
    past view observed grant candidate raw opening unopened law joint (fun _ => rfl) utility
  dsimp only at targetAlternative
  rw [posterior] at targetAlternative
  change targetContext.value ((assessment.strategy who).withLaw site.1 law) =
    immediate * values true + (1 - immediate) *
      (remaining * values true + (1 - remaining) * values false) at targetAlternative
  have targetPrescribed := roster_owner_context_value setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull assessment strategy who event owned site
    past view observed grant candidate raw opening unopened (assessment.strategy who site.1)
    joint (fun _ => rfl) utility
  simp only [InformationModel.BehavioralPolicy.withLaw_eq_self] at targetPrescribed
  rw [posterior] at targetPrescribed
  have hazard := roster_owner_opening_probability setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull who site past view observed event owned grant
    ((runtime setup).windowOpening leaks event candidate raw) fresh
  rw [← strategy] at hazard
  rw [hazard] at targetPrescribed
  change targetContext.value (assessment.strategy who) =
    FinDist.deferredHazard q (timing event who owned) count * values true +
      (1 - FinDist.deferredHazard q (timing event who owned) count) *
        (remaining * values true + (1 - remaining) * values false) at targetPrescribed
  rw [FinDist.deferredRemaining_hazard_value q (choice.prob_nonneg true) qSmall
    (timing event who owned) ⟨count, inside⟩] at targetPrescribed
  have errorBound : (timing event who owned).timingPrefix count *
      |values true - values false| ≤ weight * range :=
    (mul_le_mul_of_nonneg_left valueRange (FinDist.timingPrefix_nonnegative _ _)).trans
      (mul_le_mul_of_nonneg_right timingBound rangeNonnegative)
  refine ⟨⟨sourceSite, (source.strategy who).withLaw sourceSite.1 sourceLaw⟩, ?_⟩
  simp only [comparison, InformationModel.assessmentComparison, FinDist.expect_map]
  change targetContext.value ((assessment.strategy who).withLaw site.1 law) -
    targetContext.value (assessment.strategy who) ≤
      sourceContext.value ((source.strategy who).withLaw sourceSite.1 sourceLaw) -
        sourceContext.value (source.strategy who) + weight * range
  rw [targetAlternative, targetPrescribed, sourceAlternative, sourcePrescribed]
  exact scalar.2.2.trans (by dsimp only [replacement, remaining]; linarith)

end

end Vegas

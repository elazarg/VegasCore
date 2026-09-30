/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterOwnerValue
import Vegas.Game.RevealServiceRosterOwnerHazard
import Vegas.Game.RevealSourcePayoffBounds
import GameTheoryExtensions.Math.Probability.Support

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
  (timingFull : ∀ event who owned, FullSupport (timing event who owned))

open Classical in
include reveals openable mixed timingFull in
theorem roster_owner_comparison_of_posterior
    [setup.FiniteInitialLaw] [leaks.FiniteSupport] [network.FiniteSupport]
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
    (serving : view.application.publicView.ownTurn? who = some event)
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
    (law : PMF (((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).Choice who site.1))
    (utility : State L setup.program.terminalCtx → ℝ)
    (range weight : ℝ) (rangeNonnegative : 0 ≤ range)
    (timingBound : (timing event who owned).timingPrefix
      (past.length - rosterOffset setup rosters who event) ≤ weight)
    (valueRange :
      let value := fun disclose => expect (source.stateBelief who sourceSite) (fun state =>
        expect ((setup.protocolStep state (fun _ => some (.reveal who 0 disclose))).bind
          (setup.continuationLaw (setup.decodeBehavioralProfile admission source.strategy)))
            utility)
      |value true - value false| ≤ range) :
    let model := (rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let comparison := model.assessmentComparisonWith (model.truncatedRunner (2 * (rosterPlan setup
        rosters).length + 1)) (fun final => sourceReadout setup leaks final.state) assessment who
        (site, (assessment.strategy who).withLaw site.1 law)
    ∃ deviation : (setup.informationModel admission).AssessmentDeviation who,
      let original := (setup.informationModel
          admission).assessmentComparisonWith ((setup.informationModel
              admission).truncatedRunner (instructionCount setup.program + 1)) (fun final =>
                  setup.protocolReadout final.state)
          source who deviation
      expect comparison.alternative (fun value => value.elim 0 utility) -
          expect comparison.prescribed (fun value => value.elim 0 utility) ≤
        expect original.alternative (fun value => value.elim 0 utility) -
          expect original.prescribed (fun value => value.elim 0 utility) + weight * range := by
  intro model comparison
  have := setup.reveal_finite_history reveals admission
  let joint : Bool → Player → Option (OwnAction Player L) :=
    fun disclose _ => some (.reveal who 0 disclose)
  let values := fun disclose => expect (source.stateBelief who sourceSite) (fun state =>
    expect ((setup.protocolStep state (joint disclose)).bind
      (setup.continuationLaw (setup.decodeBehavioralProfile admission source.strategy)))
        utility)
  let choice := sourceChoiceLaw setup leaks
    (setup.decodeBehavioralProfile admission source.strategy) who view
  let q := (choice true).toReal
  let count := past.length - rosterOffset setup rosters who event
  let remaining := PMF.deferredRemaining q (timing event who owned) (count + 1)
  let predicate := {option : model.Choice who site.1 | option.1.getD ⟨none⟩ =
    (runtime setup).windowOpening leaks event candidate raw}
  let immediate := (law.toOuterMeasure predicate).toReal
  have aNonnegative : 0 ≤ immediate := ENNReal.toReal_nonneg
  have aBounded : immediate ≤ 1 := by
    change (law.toOuterMeasure predicate).toReal ≤ 1
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (ENNReal.ofReal_one ▸ outerMeasure_le_one law predicate)
  have full : FullSupport choice := by
    dsimp only [choice]
    rw [choiceLaw]
    exact setup.reveal_choice_fullSupport reveals admission source mixed who sourceSite
  have qSmall : q < 1 := by
    have total := pmf_sum_toReal_eq_one choice
    simp only [Fintype.sum_bool] at total
    have positive := pmf_toReal_pos_iff.mpr (full false)
    dsimp only [q]
    linarith
  have scalar := PMF.deferredRemaining_local_comparison q (ENNReal.toReal_nonneg) qSmall
    (timing event who owned) count immediate aNonnegative aBounded (values true) (values false)
  let replacement := immediate + (1 - immediate) * remaining
  have lower : 0 ≤ replacement := scalar.1
  have upper : replacement ≤ 1 := scalar.2.1
  have representatives (disclose : Bool) :
      ∃ action : (setup.informationModel admission).Choice who sourceSite.1,
        OwnAction.disclosure action.1 = disclose := by
    have fullSource := setup.reveal_choice_fullSupport reveals admission source mixed who sourceSite
    obtain ⟨action, _, same⟩ := PMF.support_map .. ▸ fullSource disclose
    exact ⟨action, same⟩
  let representative := fun disclose => (representatives disclose).choose
  have represents (disclose : Bool) : OwnAction.disclosure (representative disclose).1 = disclose :=
    (representatives disclose).choose_spec
  let sourceLaw := mix replacement lower upper
    (PMF.pure (representative true)) (PMF.pure (representative false))
  have sourceProbability :
      ((sourceLaw.map (fun action => OwnAction.disclosure action.1)) true).toReal =
          replacement := by
    simp only [sourceLaw, mix_map, PMF.pure_map, represents, mix_apply_toReal]
    norm_num [toReal_pure_apply]
  let sourceContext := source.truncatedContinuationContext sourceSite
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
  let targetContext := assessment.truncatedContinuationContext site
    (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
    (2 * (rosterPlan setup rosters).length + 1)
  have targetAlternative := roster_owner_context_value setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull assessment strategy who event owned site
    past view observed serving candidate raw opening unopened law joint (fun _ => rfl) utility
  dsimp only at targetAlternative
  rw [posterior] at targetAlternative
  change targetContext.value ((assessment.strategy who).withLaw site.1 law) =
    immediate * values true + (1 - immediate) *
      (remaining * values true + (1 - remaining) * values false) at targetAlternative
  have targetPrescribed := roster_owner_context_value setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull assessment strategy who event owned site
    past view observed serving candidate raw opening unopened (assessment.strategy who site.1)
    joint (fun _ => rfl) utility
  simp only [InformationModel.BehavioralPolicy.withLaw_eq_self] at targetPrescribed
  rw [posterior] at targetPrescribed
  have hazard := roster_owner_opening_probability setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull who site past view observed event owned
    serving
    ((runtime setup).windowOpening leaks event candidate raw) fresh
  rw [← strategy] at hazard
  rw [hazard] at targetPrescribed
  change targetContext.value (assessment.strategy who) =
    PMF.deferredHazard q (timing event who owned) count * values true +
      (1 - PMF.deferredHazard q (timing event who owned) count) *
        (remaining * values true + (1 - remaining) * values false) at targetPrescribed
  rw [PMF.deferredRemaining_hazard_value q (ENNReal.toReal_nonneg) qSmall
    (timing event who owned) ⟨count, inside⟩] at targetPrescribed
  have errorBound : (timing event who owned).timingPrefix count *
      |values true - values false| ≤ weight * range :=
    (mul_le_mul_of_nonneg_left valueRange (PMF.timingPrefix_nonnegative _ _)).trans
      (mul_le_mul_of_nonneg_right timingBound rangeNonnegative)
  refine ⟨⟨sourceSite, (source.strategy who).withLaw sourceSite.1 sourceLaw⟩, ?_⟩
  simp only [comparison, InformationModel.assessmentComparisonWith, expect_map]
  change targetContext.value ((assessment.strategy who).withLaw site.1 law) -
    targetContext.value (assessment.strategy who) ≤
      sourceContext.value ((source.strategy who).withLaw sourceSite.1 sourceLaw) -
        sourceContext.value (source.strategy who) + weight * range
  rw [targetAlternative, targetPrescribed, sourceAlternative, sourcePrescribed]
  exact scalar.2.2.trans (by dsimp only [replacement, remaining]; linarith)

end

end Vegas

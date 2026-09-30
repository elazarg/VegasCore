/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterOwnerHistoryValue
import Vegas.Game.RevealSourceContinuation

/-! # Conditional owner values at a complete native information site

Every local physical response lottery has a binary source continuation value.
Its coefficients depend only on the actual native information, so averaging
over hidden histories preserves the original source-state posterior exactly.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
private theorem expect_binary {α : Type*} (law : PMF α) (predicate : Set α)
    (first second : ℝ) :
    expect law (fun value => if value ∈ predicate then first else second) =
      (law.toOuterMeasure predicate).toReal * first +
          (1 - (law.toOuterMeasure predicate).toReal) * second := by
  classical
  have point (value : α) : (if value ∈ predicate then first else second) =
      (if value ∈ predicate then 1 else 0) * (first - second) + second := by
    split <;> ring
  have scaled : PayoffIntegrable law
      (fun value => (if value ∈ predicate then (1 : ℝ) else 0) * (first - second)) :=
    payoffIntegrable_of_bounded _ _ (C := |first - second|) fun value => by split <;> simp
  simp only [point]
  rw [expect_add scaled (payoffIntegrable_constant _ _), expect_mul_const, expect_indicator,
    expect_constant]
  ring

section

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)
  [setup.FiniteInitialLaw] [leaks.FiniteSupport] [network.FiniteSupport]
  (reveals : setup.program.RevealOnly)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (admission : CommitmentInterface setup.program)
  (source : (setup.informationModel admission).BehavioralAssessment)
  (mixed : source.IsFullyMixed)
  (timing : TimingLaw setup rosters)
  (timingFull : ∀ event who owned, FullSupport (timing event who owned))

open Classical in
include reveals openable mixed timingFull in
theorem roster_owner_context_value
    (assessment : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : assessment.strategy = rosterPerturbedProfile setup leaks bounds rosters network
      admission source timing)
    (who : Player) (event : (graph setup).EventId)
    (ownedEvent : (graph setup).actor? event = some who)
    (site : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (observed : site.1 = some (past, view))
    (grantView : view.application.publicView.serviceGrant = some event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (openingView : rosterOpening? setup leaks who event view = some (candidate, raw))
    (unopened : ¬ ∃ entry ∈ past.drop (rosterOffset setup rosters who event),
      entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (law : PMF (((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).Choice who site.1))
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose)
    (utility : State L setup.program.terminalCtx → ℝ) :
    let stateLaw := (assessment.stateBelief who site).map (fun state => state.bind fun current =>
      sourcePrefix? setup event.val current.execution.application.config)
    let values := fun disclose => expect stateLaw (fun state =>
      expect ((setup.protocolStep state (joint disclose)).bind (setup.continuationLaw
        (setup.decodeBehavioralProfile admission source.strategy))) utility)
    let residual := PMF.deferredRemaining
      (((sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission source.strategy)
        who view) true).toReal) (timing event who ownedEvent)
      (past.length - rosterOffset setup rosters who event + 1)
    let opens := (law.toOuterMeasure {choice | choice.1.getD ⟨none⟩ =
      (runtime setup).windowOpening leaks event candidate raw}).toReal
    (assessment.truncatedContinuationContext site
      (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
      (2 * (rosterPlan setup rosters).length + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      opens * values true + (1 - opens) *
        (residual * values true + (1 - residual) * values false) := by
  intro stateLaw values residual opens
  let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
  let model := menu.information (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network)
  let app := application setup leaks
  let valueAt := fun state disclose =>
    expect ((setup.protocolStep state (joint disclose)).bind (setup.continuationLaw
      (setup.decodeBehavioralProfile admission source.strategy))) utility
  have averaged : (assessment.truncatedContinuationContext site
      (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
      (2 * (rosterPlan setup rosters).length + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      expect (assessment.belief who site) (fun history =>
        let decoded := history.1.state.bind fun current =>
          sourcePrefix? setup event.val current.execution.application.config
        expect law (fun choice =>
          if choice.1.getD ⟨none⟩ = (runtime setup).windowOpening leaks event candidate raw
          then valueAt decoded true
          else residual * valueAt decoded true + (1 - residual) * valueAt decoded false)) := by
    rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
        expect_bind_of_finite]
    apply expect_congr_on_support
    intro history _supported
    have active := InformationModel.InformationSite.active model site history
    obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
      cases state : history.1.state with
      | none => rw [state] at active; cases active
      | some control => exact ⟨control, rfl⟩
    have actor : control.actor = some who := by rw [current] at active; exact active
    obtain ⟨remaining, actorValue, execution⟩ := control
    change actorValue = some who at actor
    subst actorValue
    rcases site with ⟨info, legal⟩
    dsimp only at observed
    subst info
    have value := roster_owner_history_local_value setup leaks bounds rosters network reveals
      openable admission source mixed timing timingFull who event ownedEvent past view grantView
      candidate raw openingView unopened joint chosen utility history.1 remaining execution
      current history.2 law
    rw [strategy]
    simpa only [current, Option.bind_some, valueAt, residual] using value
  rw [averaged]
  trans (expect (assessment.belief who site)) (fun history =>
    let decoded := history.1.state.bind fun current =>
      sourcePrefix? setup event.val current.execution.application.config
    opens * valueAt decoded true + (1 - opens) *
      (residual * valueAt decoded true + (1 - residual) * valueAt decoded false))
  · apply expect_congr_on_support
    intro history _
    exact expect_binary law {choice | choice.1.getD ⟨none⟩ =
      (runtime setup).windowOpening leaks event candidate raw} _ _
  simp only [expect_add_of_finite, expect_const_mul]
  simp only [values, stateLaw, InformationModel.BehavioralAssessment.stateBelief,
    expect_map, Function.comp_def, valueAt]

end

end Vegas

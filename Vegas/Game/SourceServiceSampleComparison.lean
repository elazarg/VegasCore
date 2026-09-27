/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceHarmlessContinuation
import Vegas.Game.RevealServiceRosterLocalEvaluation

/-! # Zero gain at public sampling opportunities

Every legal local lottery at a sample-phase information site has the same
terminal source law. This is an equality in the standard native assessment,
for arbitrary beliefs over its actual history fiber.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

section

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
  (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
  (rosters : (graph setup).EventId → List Player)
  (opportunities : ∀ event owner payload,
    (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
  (timing : ∀ event who, (graph setup).actor? event = some who →
    FinDist (Fin ((rosters event).count who)))
  (network : (runtime setup).NetworkPolicy leaks)
  (profile : BehavioralProfile setup.program)
  (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
    (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who
    (sourceServiceTimedPolicy setup leaks rosters timing profile who))
  (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
    (Revelations.initial setup.context))
  (assessment : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
    (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
  (strategy : assessment.strategy = fun who =>
    (sourceServiceMenu setup leaks bounds rosters).restrictPolicy (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
        (sourceServiceTimedPolicy setup leaks rosters timing profile who))
  (mixed : assessment.IsFullyMixed)

include values capacity opportunities covered effective strategy mixed in
theorem sourceService_sample_history_laws
    (who : Player)
    (history : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (event : (graph setup).EventId) (chance : (graph setup).actor? event = none)
    (granted : execution.application.serviceGrant = some event)
    {info : (application setup leaks).Info}
    (observed : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).infoOf who history.trace = info)
    (first second : FinDist (((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).Choice who info)) :
    let model := (sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    (model.runBehavioralFrom (Profile.update assessment.strategy who
      ((assessment.strategy who).withLaw info first))
        (2 * (rosterPlan setup rosters).length + 1) history).map
          (fun final => sourceReadout setup leaks final.state) =
      (model.runBehavioralFrom (Profile.update assessment.strategy who
        ((assessment.strategy who).withLaw info second))
          (2 * (rosterPlan setup rosters).length + 1) history).map
            (fun final => sourceReadout setup leaks final.state) := by
  classical
  subst info
  intro model
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  let players := sourceServiceTimedPolicy setup leaks rosters timing profile
  have traced : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  obtain ⟨selectedEvent, slot, initial, selected, _, Γ, names, residual, residualProfile,
      source, refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint,
      grant, reached, activated, sampled, configEq, publicEq, _, position⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network profile who ⟨remaining, some who, execution⟩ traced rfl
  have eventEq : selectedEvent = event := Option.some.inj
    (((congrArg PublicView.serviceGrant publicEq).trans grant).symm.trans granted)
  subst selectedEvent
  let visited := (rosters event).take slot
  let visits := (rosters event).drop (slot + 1)
  let before := rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
    visited.map ServiceInstruction.player
  let phaseTail := visits.map ServiceInstruction.player ++
    (.sample event :: List.replicate (event.val + 1) .tick ++ [.expire event])
  let later := ((List.finRange (graph setup).order.eventCount).drop (event.val + 1)).flatMap
    (rosterBlock setup rosters)
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have roster : rosters event = visited ++ who :: visits := by
    have drop := List.drop_eq_getElem_cons inside
    rw [(List.getElem?_eq_some_iff.mp selected).2] at drop
    simpa only [visited, visits, drop] using ((rosters event).take_append_drop slot).symm
  have prefixSplit : rosterPlanPrefix setup rosters (event.val + 1) =
      before ++ .player who :: phaseTail := by
    rw [rosterPlanPrefix_succ]
    simp only [before, phaseTail, rosterBlock, roster, chance, List.map_append, List.map_cons,
      List.append_assoc, List.singleton_append, List.cons_append]
  have positionBefore : execution.environmentRecall.length = before.length + 1 := by
    simp only [before, visited, List.length_append, List.length_singleton, List.length_map,
      List.length_take_of_le inside.le]
    exact position
  have splitPlan : rosterPlan setup rosters =
      (before ++ [.player who]) ++ (phaseTail ++ later) := by
    have split := congrArg (List.flatMap (rosterBlock setup rosters))
      ((List.finRange (graph setup).order.eventCount).take_append_drop (event.val + 1))
    rw [List.flatMap_append] at split
    change rosterPlanPrefix setup rosters (event.val + 1) ++ later = _ at split
    rw [prefixSplit] at split
    simpa only [List.append_assoc, List.singleton_append] using split.symm
  have infoAt : model.infoOf who history.trace =
      some (execution.recall who, execution.observe app who) := by
    change (menu.signals (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).infoOf who history.trace = _
    rw [menu.info, current]
    simp only [ReactiveApplication.observe, ↓reduceIte]
    rfl
  have choiceAllowed (choice : model.Choice who (model.infoOf who history.trace)) :
      choice.1.getD ⟨none⟩ ∈ menu.actions who (execution.recall who)
        (execution.observe app who) := by
    have allowed := Eq.mp (congrArg (fun input => choice.1 ∈ model.menu who input) infoAt)
      choice.2
    obtain ⟨response, allowed, same⟩ := allowed
    simpa only [same, Option.getD_some] using allowed
  let reference := first.support_nonempty.choose
  let outcome := ((runtime setup).runInteractionPlan leaks players network (phaseTail ++ later)
    (execution.respond app who (reference.val.getD ⟨none⟩))).map
      (fun final => sourceReadout setup leaks (app.finished final))
  have constant (law : FinDist (model.Choice who (model.infoOf who history.trace))) :
      (model.runBehavioralFrom (Profile.update assessment.strategy who
        ((assessment.strategy who).withLaw (model.infoOf who history.trace) law))
        (2 * (rosterPlan setup rosters).length + 1) history).map
          (fun final => sourceReadout setup leaks final.state) = outcome := by
    have physical := roster_local_law_complete_state setup leaks rosters network menu players
      covered history who remaining execution current (before ++ [.player who])
      (phaseTail ++ later) splitPlan
      (by simpa only [List.length_append, List.length_singleton] using positionBefore) rfl law
    rw [← strategy] at physical
    have mapped := congrArg (FinDist.map (sourceReadout setup leaks)) physical
    simp only [FinDist.map_comp, Function.comp_def, FinDist.map_bind, FinDist.bind_map] at mapped
    refine mapped.trans ?_
    calc
      _ = law.bind (fun _ => outcome) := by
        apply FinDist.bind_congr
        intro choice _
        exact sourceService_sample_response_source_law setup leaks bounds values capacity rosters
          opportunities timing network profile covered effective assessment strategy mixed
          who remaining execution traced event chance granted before visits prefixSplit
          positionBefore (choice.val.getD ⟨none⟩) (reference.val.getD ⟨none⟩)
          (choiceAllowed choice) (choiceAllowed reference)
      _ = _ := FinDist.bind_const _ _
  exact (constant first).trans (constant second).symm

include values capacity opportunities covered effective strategy mixed in
/-- Public-sample choices have identical prescribed and deviating laws under
the standard assessment, for every posterior over the actual information site. -/
theorem sourceService_sample_comparison_law
    (who : Player)
    (site : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (observed : site.1 = some (past, view))
    (event : (graph setup).EventId) (chance : (graph setup).actor? event = none)
    (granted : view.application.publicView.serviceGrant = some event)
    (law : FinDist (((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).Choice who site.1)) :
    let model := (sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let comparison := model.assessmentComparison
      (fun final => sourceReadout setup leaks final.state)
      (2 * (rosterPlan setup rosters).length + 1) assessment who
        (site, (assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  intro model comparison
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  simp only [comparison, InformationModel.assessmentComparison,
    InformationModel.BehavioralAssessment.continuationContext, FinDist.map_bind]
  apply FinDist.bind_congr
  intro history _
  have active := InformationModel.InformationSite.active model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have actor : control.actor = some who := by rw [current] at active; exact active
  obtain ⟨remaining, actorValue, execution⟩ := control
  change actorValue = some who at actor
  subst actorValue
  have input : model.infoOf who history.1.trace =
      some (execution.recall who, execution.observe app who) := by
    change (menu.signals (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).infoOf who history.1.trace = _
    rw [menu.info, current]
    simp only [ReactiveApplication.observe, ↓reduceIte]
    rfl
  have same := Option.some.inj (input.symm.trans (history.2.trans observed))
  have grant : execution.application.serviceGrant = some event :=
    (congrArg (fun pair : List app.PlayerEntry × app.PlayerView =>
      pair.2.application.publicView.serviceGrant) same).trans granted
  have laws := sourceService_sample_history_laws setup leaks bounds values capacity rosters
    opportunities timing network profile covered effective assessment strategy mixed who
    history.1 remaining execution current event chance grant history.2 law
    (assessment.strategy who site.1)
  simpa only [InformationModel.BehavioralPolicy.withLaw_eq_self] using laws

include values capacity opportunities covered effective strategy mixed in
/-- The gain of any local alternative at a public-sampling site is zero,
including for utilities of persistent types and public outcomes. -/
theorem sourceService_sample_comparison_gain
    (who : Player)
    (site : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (observed : site.1 = some (past, view))
    (event : (graph setup).EventId) (chance : (graph setup).actor? event = none)
    (granted : view.application.publicView.serviceGrant = some event)
    (law : FinDist (((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).Choice who site.1))
    (utility : Option (State L setup.program.terminalCtx) → ℝ) :
    let model := (sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let comparison := model.assessmentComparison
      (fun final => sourceReadout setup leaks final.state)
      (2 * (rosterPlan setup rosters).length + 1) assessment who
        (site, (assessment.strategy who).withLaw site.1 law)
    comparison.alternative.expect utility - comparison.prescribed.expect utility = 0 := by
  intro model comparison
  have same := sourceService_sample_comparison_law setup leaks bounds values capacity rosters
    opportunities timing network profile covered effective assessment strategy mixed who site
    past view observed event chance granted law
  change comparison.alternative = comparison.prescribed at same
  rw [same, sub_self]

end

end Vegas.SourceProgram.RevealService

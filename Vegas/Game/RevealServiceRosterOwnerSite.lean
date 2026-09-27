/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterOwnerComparison
import Vegas.Game.RevealServiceRosterLocalEvaluation

/-! # Original source information at every fresh native opening site

All timing, phase and posterior data are recovered from an actual native
information site. No selected execution or source posterior is supplied by the
caller. The site's full private recall and passive observation remain present.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_owner_site
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    [∀ who (site : (setup.informationModel admission).InformationSite who),
      Fintype ((setup.informationModel admission).InformationHistory who site.1)]
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) source (setup.decision_antichain admission))
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (timingFull : ∀ event who owned, (timing event who owned).FullSupport) :
    let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
    let scheduler := rosterScheduler setup leaks rosters network
    let horizon := (rosterPlan setup rosters).length
    let model := menu.information (initialLaw setup) horizon scheduler
    let assessment := InformationModel.BehavioralAssessment.ofStrategy
      (rosterPerturbedProfile setup leaks bounds rosters network reveals openable admission
        source mixed timing timingFull)
    let native := assessment.bayes
      (rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable
        admission source mixed timing timingFull)
      (menu.decisionInformationAntichain (initialLaw setup) horizon scheduler)
    ∀ (who : Player) (site : model.InformationSite who)
      (past : List (application setup leaks).PlayerEntry)
      (view : (application setup leaks).PlayerView) (packet : (application setup leaks).Action),
      site.1 = some (past, view) →
      rosterFresh? setup leaks rosters who past view = some packet →
      ∃ event : (graph setup).EventId,
        ∃ _owned : (graph setup).actor? event = some who, ∃ candidate raw,
          ∃ sourceSite : (setup.informationModel admission).InformationSite who,
          view.application.publicView.serviceGrant = some event ∧
          rosterOpening? setup leaks who event view = some (candidate, raw) ∧
          packet = (runtime setup).windowOpening leaks event candidate raw ∧
          (¬ ∃ entry ∈ past.drop (rosterOffset setup rosters who event),
            entry.action = (runtime setup).windowOpening leaks event candidate raw) ∧
          past.length - rosterOffset setup rosters who event < (rosters event).count who ∧
          sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission source.strategy)
              who view = (source.strategy who sourceSite.1).map
                (fun choice => OwnAction.disclosure choice.1) ∧
          (native.stateBelief who site).map (fun state => state.bind fun current =>
            sourcePrefix? setup event.val current.execution.application.config) =
              source.stateBelief who sourceSite := by
  intro menu scheduler horizon model assessment native who site past view packet siteInput fresh
  let app := application setup leaks
  let extended := bounds.withInitialValues (initialLaw setup)
  obtain ⟨event, candidate, raw, granted, owned, opening, packetEq, notRecorded⟩ :=
    rosterFresh?_shape setup leaks rosters who past view packet fresh
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active model site history
  have observed := history.2.trans siteInput
  cases current : history.1.state with
  | none =>
      rw [current] at active
      cases active
  | some control =>
      rw [current] at active
      change control.actor = some who at active
      have traced : (menu.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
        current ▸ history.1.trace
      have input : (control.execution.recall who, control.execution.observe app who) =
          (past, view) := by
        have atHistory := menu.info (initialLaw setup) horizon scheduler who history.1.trace
        have equality := (congrArg (app.observe who) current).symm.trans
          (atHistory.symm.trans observed)
        simpa only [ReactiveApplication.observe, active, ↓reduceIte, Option.some.injEq] using
          equality
      have recallEq : control.execution.recall who = past := congrArg Prod.fst input
      have viewEq : control.execution.observe app who = view := congrArg Prod.snd input
      have grant : control.execution.application.serviceGrant = some event := by
        have publicGrant := congrArg (fun seen => seen.application.publicView.serviceGrant) viewEq
        exact publicGrant.trans granted
      obtain ⟨sourceSite, sourceView, sourceDepth⟩ :=
        roster_owner_source_site setup leaks extended rosters network reveals openable admission
          who control traced active event owned grant
      have choiceLaw := roster_owner_choice_at_history setup leaks extended rosters network
        reveals openable admission source.strategy who control traced active event owned grant
        sourceSite sourceView
      rw [viewEq] at choiceLaw
      obtain ⟨actual, slot, boundary, prior, sample, initial, state, selected, _initialSupport,
          _related, _sourceSupport, phaseGrant, offset, _serials, _published, reached,
          activated, unchanged, position⟩ :=
        roster_decision_phase setup leaks extended rosters network reveals openable
          who control traced active
      have sameEvent : actual = event := by
        rw [unchanged, phaseGrant] at grant
        exact Option.some.inj grant
      subst actual
      have pastCount : past.length - rosterOffset setup rosters who event =
          ((rosters event).take slot).count who := by
        have counted := fixed_plan_response_counts setup leaks network menu.uniformResponses
          (((rosters event).take slot).map ServiceInstruction.player)
          (by simp only [List.mem_map]; rintro ⟨_, _, impossible⟩; cases impossible)
          boundary prior reached who
        simp only [List.filterMap_map, instructionActor, Function.comp_def,
          List.filterMap_some, offset who] at counted
        have priorRecall : prior.recall who = past := by
          simpa only [activated, ReactiveApplication.Execution.sampledActivation] using recallEq
        rw [priorRecall] at counted
        omega
      let before := rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        ((rosters event).take slot).map ServiceInstruction.player
      have beforeLength : before.length =
          (rosterPlanPrefix setup rosters event.val).length + 1 + slot := by
        simp only [before, List.length_append, List.length_singleton, List.length_map,
          List.length_take_of_le (List.getElem?_eq_some_iff.mp selected).1.le]
      have suffix := roster_phase_suffix setup rosters event who owned slot
      have prefixLaw : (rosterPlan setup rosters).take before.length = before := by
        rw [suffix, List.take_left]
      have selectedPlan : (rosterPlan setup rosters)[before.length]? = some (.player who) := by
        have drop := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp selected).1
        rw [(List.getElem?_eq_some_iff.mp selected).2] at drop
        rw [suffix, List.getElem?_append_right (by rfl), Nat.sub_self, drop]
        simp only [List.map_cons, List.cons_append, List.getElem?_cons_zero]
      have posterior := roster_owner_bayes_source_state setup leaks bounds rosters network reveals
        openable admission source mixed bayes timing timingFull event who owned
        ((rosters event).take slot) before.length selectedPlan prefixLaw site history control
        current
        (by rw [beforeLength]; exact position) sourceSite sourceView sourceDepth
      refine ⟨event, owned, candidate, raw, sourceSite, granted, opening, packetEq, ?_, ?_,
        choiceLaw, posterior⟩
      · rintro ⟨entry, member, same⟩
        exact notRecorded entry member (same.trans packetEq.symm)
      · rw [pastCount]
        exact roster_count_before selected

end Vegas.SourceProgram.RevealService

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterHarmless
import Vegas.Game.RevealServiceRosterContinuation
import Vegas.Game.RevealServiceRosterMixing
import Vegas.Game.ServiceRosterLocalEvaluation
import GameTheory.Analysis.Protocol.Incentives

/-! # Zero local gain at retained replay-only information sites

The absence of a fresh opening is a fact about the player's actual information.
At every hidden history in such a site, the player is foreign to the current
event or has already opened. Their alternative response lotteries preserve the
entire terminal source-state law under the same continuation profile.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem absent_opening_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (granted : view.application.publicView.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (opening : rosterOpening? setup leaks who event view = some (candidate, raw))
    (absent : rosterFresh? setup leaks rosters who past view = none) :
    ∃ entry ∈ past.drop (rosterOffset setup rosters who event),
      entry.action = (runtime setup).windowOpening leaks event candidate raw := by
  classical
  unfold rosterFresh? at absent
  rw [granted] at absent
  simp only [bind, Option.bind_some, owned, ne_eq, not_true_eq_false, ↓reduceIte,
    opening] at absent
  split at absent
  · rename_i recorded
    simpa only [List.any_eq_true, decide_eq_true_eq] using recorded
  · cases absent

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
theorem roster_harmless_history_laws [setup.FiniteInitialLaw]
    (who : Player)
    (history : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).protocol
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (absent : rosterFresh? setup leaks rosters who (execution.recall who)
      (execution.observe (application setup leaks) who) = none)
    {info : (application setup leaks).Info}
    (observed : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).infoOf who history.trace = info)
    (first second : PMF (((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Choice
          who info)) :
    let model := (rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)
    let baseline := rosterPerturbedProfile setup leaks bounds rosters network
      admission source timing
    (model.runBehavioralFrom (Profile.update baseline who
      ((baseline who).withLaw info first)) (2 * (rosterPlan setup rosters).length + 1)
        history).map (fun final => sourceReadout setup leaks final.state) =
      (model.runBehavioralFrom (Profile.update baseline who
        ((baseline who).withLaw info second)) (2 * (rosterPlan setup rosters).length + 1)
          history).map (fun final => sourceReadout setup leaks final.state) := by
  classical
  cases observed
  intro model baseline
  let app := application setup leaks
  let extended := bounds.withInitialValues (initialLaw setup)
  let menu := rosterMenu setup leaks extended rosters
  let profile := setup.decodeBehavioralProfile admission source.strategy
  let players := rosterPolicy setup leaks rosters timing profile
  have traced : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  obtain ⟨event, slot, boundary, prior, sample, initial, state, selected, initialSupport,
      related, sourceSupport, grant, offset, serials, published, reached, activated,
      unchanged, position⟩ :=
    roster_decision_phase setup leaks extended rosters network reveals openable who _ traced rfl
  change execution = _ at activated
  change execution.application = boundary.application at unchanged
  change execution.environmentRecall.length = _ at position
  obtain ⟨owner, ownedEvent⟩ := source_owner setup reveals event
  obtain ⟨site, _, choiceLaw, candidate, raw, opening, owned, valid, _⟩ :=
    roster_owner_choice_data setup leaks bounds reveals admission source.strategy owner event
      ownedEvent initial initialSupport state boundary related sourceSupport grant
  have choiceFull : FullSupport (sourceChoiceLaw setup leaks profile owner
      (boundary.observe app owner)) := by
    rw [choiceLaw]
    exact setup.reveal_choice_fullSupport reveals admission source mixed owner site
  have harmless : who ≠ owner ∨ ∃ entry ∈
      (prior.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw := by
    by_cases different : who ≠ owner
    · exact Or.inl different
    · have same : who = owner := not_ne_iff.mp different
      cases same
      right
      have grantNow : (execution.observe app who).application.publicView.serviceGrant =
          some event := by change execution.application.serviceGrant = _; rw [unchanged, grant]
      have openingNow : rosterOpening? setup leaks who event (execution.observe app who) =
          some (candidate, raw) :=
        (rosterOpening?_application_eq setup leaks who event execution boundary unchanged).trans
          opening
      have recorded := absent_opening_recorded setup leaks rosters who
        (execution.recall who) (execution.observe app who) event candidate raw grantNow
          ownedEvent openingNow absent
      rw [activated] at recorded
      exact recorded
  let visited := (rosters event).take slot
  let tail := (rosters event).drop (slot + 1)
  have splitRoster : rosters event = visited ++ who :: tail := by
    have drop := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp selected).1
    rw [(List.getElem?_eq_some_iff.mp selected).2] at drop
    simpa only [visited, tail, drop] using ((rosters event).take_append_drop slot).symm
  let before := rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
    ((rosters event).take (slot + 1)).map ServiceInstruction.player
  let rest := tail.map ServiceInstruction.player ++
    (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]) ++
    ((List.finRange (graph setup).order.eventCount).drop (event.val + 1)).flatMap
      (rosterBlock setup rosters)
  have splitPlan : rosterPlan setup rosters = before ++ rest :=
    roster_phase_suffix setup rosters event owner ownedEvent (slot + 1)
  have beforePosition : execution.environmentRecall.length = before.length := by
    simp only [before, List.length_append, List.length_singleton, List.length_map,
      List.length_take_of_le (Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp selected).1)]
    omega
  have choiceAllowed (choice : model.Choice who (model.infoOf who history.trace)) :
      choice.1.getD ⟨none⟩ ∈ rosterActions setup leaks extended rosters who
        (execution.recall who) (execution.observe app who) := by
    have infoAt : model.infoOf who history.trace =
        some (execution.recall who, execution.observe app who) := by
      change (menu.signals (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).infoOf who history.trace = _
      rw [menu.info, current]
      simp only [ReactiveApplication.observe, ↓reduceIte]
      rfl
    have allowed := Eq.mp
      (congrArg (fun info => choice.1 ∈ model.menu who info) infoAt) choice.2
    change ∃ response ∈ rosterActions setup leaks extended rosters who
      (execution.recall who) (execution.observe app who), choice.1 = some response at allowed
    obtain ⟨response, member, same⟩ := allowed
    simpa only [same, Option.getD_some] using member
  have same (response : app.Action)
      (allowed : response ∈ rosterActions setup leaks extended rosters who
        (execution.recall who) (execution.observe app who)) :
      ((runtime setup).runInteractionPlan leaks players network rest
        (execution.respond app who response)).map
          (fun final => sourceReadout setup leaks (app.finished final)) =
        ((runtime setup).runInteractionPlan leaks players network rest
          (execution.respond app who ⟨none⟩)).map
            (fun final => sourceReadout setup leaks (app.finished final)) := by
    rw [activated] at allowed ⊢
    exact roster_harmless_response_source_law setup leaks extended rosters timing network reveals
      profile initial event state boundary related owner ownedEvent grant candidate raw opening
      owned valid offset serials published menu.uniformResponses
      (fun player past view action supported =>
        (menu.uniformResponses_support player past view action).mp supported)
      visited tail who splitRoster prior reached sample response ⟨none⟩ allowed
      (silence_roster setup leaks extended rosters who _ _) harmless choiceFull
      (timingFull event owner ownedEvent) (fun disclose _ => some (.reveal owner 0 disclose))
      (fun _ => rfl)
  have localLaw (law : PMF (model.Choice who (model.infoOf who history.trace))) :=
    roster_local_law_complete_state setup leaks rosters network menu players
      (rosterPolicy_admissible setup leaks bounds rosters network reveals openable admission
        source mixed timing timingFull) history who remaining execution current before rest
      splitPlan beforePosition rfl law
  have constant (law : PMF (model.Choice who (model.infoOf who history.trace))) :
      (model.runBehavioralFrom (Profile.update baseline who
        ((baseline who).withLaw (model.infoOf who history.trace) law))
        (2 * (rosterPlan setup rosters).length + 1) history).map
          (fun final => sourceReadout setup leaks final.state) =
        ((runtime setup).runInteractionPlan leaks players network rest
          (execution.respond app who ⟨none⟩)).map
            (fun final => sourceReadout setup leaks (app.finished final)) := by
    have mapped := congrArg (fun distribution => distribution.map (sourceReadout setup leaks))
      (localLaw law)
    simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, PMF.bind_map]
      at mapped
    refine mapped.trans ?_
    calc
      _ = law.bind (fun _ => ((runtime setup).runInteractionPlan leaks players network rest
          (execution.respond app who ⟨none⟩)).map
            (fun final => sourceReadout setup leaks (app.finished final))) := by
        apply bind_congr_on_support _
        intro choice _
        exact same _ (choiceAllowed choice)
      _ = _ := PMF.bind_const _ _
  exact (constant first).trans (constant second).symm

open Classical in
include reveals openable mixed timingFull in
/-- Any posterior over a replay-only information site gives identical
prescribed and locally deviating terminal laws. No additional Bayesian premise
is needed: the equality holds at every history in the information fiber. -/
theorem roster_harmless_comparison_law [setup.FiniteInitialLaw]
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
    (absent : rosterFresh? setup leaks rosters who past view = none)
    (law : PMF (((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).Choice who site.1)) :
    let model := (rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let comparison := model.assessmentComparison
      (fun final => sourceReadout setup leaks final.state)
      (2 * (rosterPlan setup rosters).length + 1) assessment who
        (site, (assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  intro model comparison
  let app := application setup leaks
  let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
  simp only [comparison, InformationModel.assessmentComparison, InformationModel.assessmentLaw,
    PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have active := InformationModel.InformationSite.active model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have actor : control.actor = some who := by
    rw [current] at active
    exact active
  obtain ⟨remaining, actorValue, execution⟩ := control
  change actorValue = some who at actor
  subst actorValue
  have actualView : model.infoOf who history.1.trace =
      some (execution.recall who, execution.observe app who) := by
    change (menu.signals (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).infoOf who history.1.trace = _
    rw [menu.info, current]
    simp only [ReactiveApplication.observe, ↓reduceIte]
    rfl
  have same : (execution.recall who, execution.observe app who) = (past, view) :=
    Option.some.inj (actualView.symm.trans (history.2.trans observed))
  have absentHere : rosterFresh? setup leaks rosters who (execution.recall who)
      (execution.observe app who) = none := by
    exact (congrArg (fun pair : List app.PlayerEntry × app.PlayerView =>
      rosterFresh? setup leaks rosters who pair.1 pair.2) same).trans absent
  have laws := roster_harmless_history_laws setup leaks bounds rosters network reveals openable
    admission source mixed timing timingFull who history.1 remaining execution current
      absentHere history.2 law (assessment.strategy who site.1)
  rw [← strategy] at laws
  simpa only [InformationModel.BehavioralPolicy.withLaw_eq_self] using laws

open Classical in
include reveals openable mixed timingFull in
/-- Thus a harmless local alternative has exactly zero gain for every
utility of the retained terminal source state, including persistent types. -/
theorem roster_harmless_comparison_gain [setup.FiniteInitialLaw]
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
    (absent : rosterFresh? setup leaks rosters who past view = none)
    (law : PMF (((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).Choice who site.1))
    (utility : Option (State L setup.program.terminalCtx) → ℝ) :
    let model := (rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let comparison := model.assessmentComparison
      (fun final => sourceReadout setup leaks final.state)
      (2 * (rosterPlan setup rosters).length + 1) assessment who
        (site, (assessment.strategy who).withLaw site.1 law)
    expect comparison.alternative utility - expect comparison.prescribed utility = 0 := by
  intro model comparison
  have same := roster_harmless_comparison_law setup leaks bounds rosters network reveals openable
    admission source mixed timing timingFull assessment strategy who site past view observed
      absent law
  change comparison.alternative = comparison.prescribed at same
  rw [same, sub_self]

end

end Vegas

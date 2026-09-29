/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterWindowSource
import Vegas.Game.ServiceRosterLocalEvaluation
import Vegas.Game.RevealServiceRosterSitePosition
import Vegas.Game.RevealServiceRosterOwnerComparison

/-! # Local owner values at every actual retained roster history

This connects the finite protocol's local deviation evaluator to the conditional
source values. The history may be off path; its clean phase prefix is derived
from its legal trace. The source profile and all later physical responses stay
fixed throughout the comparison.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
theorem roster_owner_history_local_value
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) [network.FiniteSupport]
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (who : Player) (event : (graph setup).EventId)
    (ownedEvent : (graph setup).actor? event = some who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (grantView : view.application.publicView.serviceGrant = some event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (openingView : rosterOpening? setup leaks who event view = some (candidate, raw))
    (unopened : ¬ ∃ entry ∈ past.drop (rosterOffset setup rosters who event),
      entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose)
    (utility : State L setup.program.terminalCtx → ℝ) :
    let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
    let model := menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
    let baseline := rosterPerturbedProfile setup leaks bounds rosters network
      admission source timing
    ∀ (history : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).History)
      (remaining : Nat) (execution : (application setup leaks).Execution),
      history.state = some ⟨remaining, some who, execution⟩ →
      model.infoOf who history.trace = some (past, view) →
      ∀ law : PMF (model.Choice who (some (past, view))),
      let values := fun disclose =>
        expect ((setup.protocolStep (sourcePrefix? setup event.val execution.application.config)
          (joint disclose)).bind (setup.continuationLaw
            (setup.decodeBehavioralProfile admission source.strategy))) utility
      let residual := PMF.deferredRemaining
        (((sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission source.strategy)
          who view) true).toReal) (timing event who ownedEvent)
        (past.length - rosterOffset setup rosters who event + 1)
      expect (model.runBehavioralFrom
        (Profile.update (sig := model.behavioralSignature) baseline who
          ((baseline who).withLaw (some (past, view)) law))
        (2 * (rosterPlan setup rosters).length + 1) history)
          (fun final => (sourceReadout setup leaks final.state).elim 0 utility) =
        expect law (fun choice =>
          if choice.1.getD ⟨none⟩ = (runtime setup).windowOpening leaks event candidate raw
          then values true else residual * values true + (1 - residual) * values false) := by
  intro menu model baseline history remaining execution current observed law values residual
  let app := application setup leaks
  let extended := bounds.withInitialValues (initialLaw setup)
  let decoded := setup.decodeBehavioralProfile admission source.strategy
  let players := rosterPolicy setup leaks rosters timing decoded
  have input : (execution.recall who, execution.observe app who) = (past, view) := by
    have atHistory := menu.info (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who history.trace
    have equality := (congrArg (app.observe who) current).symm.trans
      (atHistory.symm.trans observed)
    simpa only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq] using equality
  have recallEq : execution.recall who = past := congrArg Prod.fst input
  have viewEq : execution.observe app who = view := congrArg Prod.snd input
  obtain ⟨actual, slot, boundary, prior, sample, initial, state, selected, initialSupport,
      related, sourceSupport, grant, offset, serials, published, reached, activated,
      unchanged, position⟩ :=
    roster_decision_phase setup leaks extended rosters network reveals openable who
      ⟨remaining, some who, execution⟩ (current ▸ history.trace) rfl
  change execution = prior.sampledActivation app who sample at activated
  change execution.application = boundary.application at unchanged
  change execution.environmentRecall.length =
    (rosterPlanPrefix setup rosters actual.val).length + 1 + slot + 1 at position
  have sameEvent : actual = event := by
    have actualGrant : view.application.publicView.serviceGrant = some actual := by
      rw [← viewEq]
      change execution.application.serviceGrant = some actual
      rw [unchanged, grant]
    exact Option.some.inj (actualGrant.symm.trans grantView)
  subst actual
  have opening : rosterOpening? setup leaks who event (boundary.observe app who) =
      some (candidate, raw) := by
    rw [← rosterOpening?_application_eq setup leaks who event execution boundary unchanged,
      viewEq]
    exact openingView
  obtain ⟨sourceSite, sourceObserved, choiceLaw, otherCandidate, otherRaw, otherOpening,
      owner, valid, _handle, _value⟩ :=
    roster_owner_choice_data setup leaks bounds reveals admission source.strategy who event
      ownedEvent initial initialSupport state boundary related sourceSupport grant
  have sameOpening : (otherCandidate, otherRaw) = (candidate, raw) :=
    Option.some.inj (otherOpening.symm.trans opening)
  have candidateEq : otherCandidate = candidate := congrArg Prod.fst sameOpening
  have rawEq : otherRaw = raw := congrArg Prod.snd sameOpening
  subst otherCandidate
  subst otherRaw
  have choiceFull : FullSupport (sourceChoiceLaw setup leaks decoded who
      (boundary.observe app who)) := by
    rw [choiceLaw]
    exact setup.reveal_choice_fullSupport reveals admission source mixed who sourceSite
  have rosterSplit : rosters event = (rosters event).take slot ++
      who :: (rosters event).drop (slot + 1) := by
    have drop := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp selected).1
    rw [(List.getElem?_eq_some_iff.mp selected).2] at drop
    simpa only [drop] using ((rosters event).take_append_drop slot).symm
  have complete : ((rosters event).take slot).count who + 1 +
      ((rosters event).drop (slot + 1)).count who = (rosters event).count who := by
    conv_rhs => rw [rosterSplit]
    simp only [List.count_append, List.count_cons_self]
    omega
  have counts := roster_after_response_counts setup leaks rosters network menu.uniformResponses
    event boundary prior offset ((rosters event).take slot) ((rosters event).drop (slot + 1))
    who rosterSplit reached sample
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
  have notOpened : ¬ ∃ entry ∈ (prior.recall who).drop (rosterOffset setup rosters who event),
      entry.action = (runtime setup).windowOpening leaks event candidate raw := by
    have priorRecall : prior.recall who = past := by
      simpa only [activated, ReactiveApplication.Execution.sampledActivation] using recallEq
    rw [priorRecall]
    exact unopened
  have decoder := PublicPrefixCheckpoint.decode setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state boundary related
  change sourcePrefix? setup event.val boundary.application.config = some state at decoder
  have valueEq (disclose : Bool) : values disclose =
      expect ((ProtocolState.step setup.program state (joint disclose)).bind
        (ProtocolState.continuationLaw setup.program decoded)) utility := by
    dsimp only [values]
    rw [unchanged, decoder]
    simp only [Setup.protocolStep, PMF.bind_map]
    rfl
  have residualEq : residual = PMF.deferredRemaining
      (((sourceChoiceLaw setup leaks decoded who (boundary.observe app who)) true).toReal)
      (timing event who ownedEvent) (((rosters event).take slot).count who + 1) := by
    dsimp only [residual]
    rw [pastCount, ← viewEq,
      sourceChoiceLaw_application_eq setup leaks decoded who execution boundary unchanged]
  let before := rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
    ((rosters event).take (slot + 1)).map ServiceInstruction.player
  let rest := (((rosters event).drop (slot + 1)).map ServiceInstruction.player ++
    (.includeLatest event who :: List.replicate (event.val + 1) .tick ++ [.expire event])) ++
      (((List.finRange (eventCount setup.program)).drop (event.val + 1)).flatMap
        (rosterBlock setup rosters))
  have physical := roster_local_law_complete_state setup leaks rosters network menu players
    (rosterPolicy_admissible setup leaks bounds rosters network reveals openable admission
      source mixed timing timingFull) history who remaining execution current before rest
    (roster_phase_suffix setup rosters event who ownedEvent (slot + 1))
    (by
      dsimp only [before]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        List.length_take]
      have inside : slot < (rosters event).length := (List.getElem?_eq_some_iff.mp selected).1
      omega) observed law
  have integrable : PayoffIntegrable ((law.map fun choice => choice.1.getD ⟨none⟩).bind
      fun response => ((runtime setup).runInteractionPlan leaks players network rest
        (execution.respond app who response)).map (application setup leaks).finished)
      (fun final => (sourceReadout setup leaks final).elim 0 utility) := by
    rw [← physical]
    exact payoffIntegrable_of_finite_support _ _
      (by rw [PMF.support_map]; exact (Set.toFinite _).image _)
  have expectation := congrArg (fun distribution => expect distribution
    (fun final => (sourceReadout setup leaks final).elim 0 utility)) physical
  simp only [expect_map] at expectation
  rw [expect_bind_tower _ _ _ integrable] at expectation
  simp only [expect_map, Function.comp_def] at expectation
  change expect (model.runBehavioralFrom
    (Profile.update (sig := model.behavioralSignature) baseline who
      ((baseline who).withLaw (some (past, view)) law))
    (2 * (rosterPlan setup rosters).length + 1) history)
      (fun final => (sourceReadout setup leaks final.state).elim 0 utility) = _ at expectation
  rw [expectation]
  apply expect_congr_on_support
  intro choice _supported
  obtain ⟨action, member, choiceEq⟩ := choice.2
  have decodedChoice : choice.1.getD ⟨none⟩ = action := by rw [choiceEq]; rfl
  rw [decodedChoice]
  have memberAt : action ∈ rosterActions setup leaks extended rosters who
      ((prior.sampledActivation app who sample).recall who)
      ((prior.sampledActivation app who sample).observe app who) := by
    rw [← activated, recallEq, viewEq]
    exact member
  have localValue := roster_owner_response_source_value setup leaks extended rosters timing
    network reveals decoded initial event state boundary related who ownedEvent grant candidate
    raw opening owner valid (offset who) serials published menu.uniformResponses
    (fun player past view response supported =>
      (menu.uniformResponses_support player past view response).mp supported)
    ((rosters event).take slot) ((rosters event).drop (slot + 1)) complete prior reached sample
    action memberAt notOpened (counts action) choiceFull (timingFull event who ownedEvent)
    joint chosen utility
  simpa only [rest, ReactiveApplication.finished, activated, valueEq, residualEq]
    using localValue

end Vegas

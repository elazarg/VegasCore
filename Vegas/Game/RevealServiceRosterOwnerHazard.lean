/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterMixing
import GameTheoryExtensions.Math.Probability.Support

/-! # Immediate opening probability at actual owner information sites

The private timing posterior is derived from a legal retained prefix. Its
hazard is therefore the probability in the finite behavioral profile, including
at information sites that have zero probability in the limiting profile.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
private theorem unopened_mixture_probability
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (initial : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (ownedEvent : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw)
    (offset : (initial.recall owner).length = rosterOffset setup rosters owner event)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who history view response, response ∈ (players who history view).support →
      response ∈ rosterActions setup leaks bounds rosters who history view)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (inside : visits.count owner < (rosters event).count owner)
    (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (sample : Finset (MessageId Player))
    (unseen : ∀ entry ∈ (current.recall owner).drop
      (rosterOffset setup rosters owner event),
      entry.action ≠ (runtime setup).windowOpening leaks event candidate raw)
    (choice : PMF Bool) (choiceFull : FullSupport choice)
    (timing : PMF (Fin ((rosters event).count owner))) (timingFull : FullSupport timing) :
    let app := application setup leaks
    let activated := current.sampledActivation app owner sample
    let packet := (runtime setup).windowOpening leaks event candidate raw
    ((((app.policyMixture (rosterSelection choice timing) (fun selected =>
      app.scheduledPolicy (rosterOffset setup rosters owner event) selected
        (fun _ _ => PMF.pure packet) app.replayPolicy)).policy
          (activated.recall owner) (activated.observe app owner))) packet).toReal =
      PMF.deferredHazard ((choice true).toReal) timing
        ((activated.recall owner).length - rosterOffset setup rosters owner event) := by
  intro app activated packet
  obtain ⟨selected, frame, _, recorded, posterior⟩ :=
    roster_window_posterior setup leaks bounds rosters initial event owner granted ownedEvent
      candidate raw opening owned valid offset serials published players covered network visits
        inside.le current reached
  have selectedNone : selected = none := by
    cases selected with
    | none => rfl
    | some slot =>
        obtain ⟨entry, member, same⟩ := recorded.mp rfl
        exact (unseen entry member same).elim
  subst selected
  have full := rosterSelection_fullSupport choice timing choiceFull timingFull
  have small : (choice true).toReal < 1 := by
    have positive := pmf_toReal_pos_iff.mpr (choiceFull false)
    have total := pmf_sum_toReal_eq_one choice
    simp only [Fintype.sum_bool] at total
    linarith
  let slot : Fin ((rosters event).count owner) := ⟨visits.count owner, inside⟩
  have atSlot : (activated.recall owner).length =
      rosterOffset setup rosters owner event + slot.val := frame.count
  have exactPost := posterior (rosterSelection choice timing) full
  have representation := PMF.bind_bool_mix choice (timing.map some) (PMF.pure none)
  change rosterSelection choice timing = _ at representation
  simp only [representation] at exactPost ⊢
  have probability := app.scheduledMixture_probability_of_posterior ((choice true).toReal)
    (ENNReal.toReal_nonneg) small timing (rosterOffset setup rosters owner event) packet
    app.replayPolicy (activated.recall owner) slot atSlot exactPost
      (activated.observe app owner) packet
  have replayZero : ((app.replayPolicy (activated.recall owner)
      (activated.observe app owner)) packet).toReal = 0 := by
    apply FinDist.prob_eq_zero_iff.mpr
    intro member
    rcases app.replayPolicy_cases _ _ _ member with
      impossible | ⟨id, impossible⟩
    all_goals
      dsimp only [packet, EventGraphRuntime.windowOpening] at impossible
      cases impossible
  simpa only [FinDist.prob_pure_self, replayZero, mul_one, mul_zero, add_zero,
    atSlot, Nat.add_sub_cancel_left] using probability

open Classical in
/-- The immediate canonical-opening mass in the actual finite profile is the
deferred hazard of the original source disclosure probability. The only site
classification premise is its available fresh response, an observable fact. -/
theorem roster_owner_opening_probability
    (setup : Setup (Player := Player) (L := L))
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
    (who : Player)
    (site : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (observed : site.1 = some (past, view))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (granted : view.application.publicView.serviceGrant = some event)
    (packet : (application setup leaks).Action)
    (fresh : rosterFresh? setup leaks rosters who past view = some packet) :
    ((rosterPerturbedProfile setup leaks bounds rosters network admission
      source timing who site.1).toOuterMeasure {choice | choice.1.getD ⟨none⟩ = packet}).toReal =
      PMF.deferredHazard
        (((sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission source.strategy)
          who view) true).toReal) (timing event who owned)
            (past.length - rosterOffset setup rosters who event) := by
  let app := application setup leaks
  let extended := bounds.withInitialValues (initialLaw setup)
  let menu := rosterMenu setup leaks extended rosters
  let model := menu.information (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network)
  let profile := setup.decodeBehavioralProfile admission source.strategy
  let players := rosterPolicy setup leaks rosters timing profile
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have acting : control.actor = some who := by rw [current] at active; exact active
  have atInfo : model.infoOf who history.1.trace =
      some (control.execution.recall who, control.execution.observe app who) := by
    change (menu.signals (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).infoOf who history.1.trace = _
    rw [menu.info, current]
    simp only [ReactiveApplication.observe, acting, ↓reduceIte]
    rfl
  have same : (control.execution.recall who, control.execution.observe app who) = (past, view) :=
    Option.some.inj (atInfo.symm.trans (history.2.trans observed))
  have pastEq := congrArg Prod.fst same
  have viewEq := congrArg Prod.snd same
  change control.execution.recall who = past at pastEq
  change control.execution.observe app who = view at viewEq
  have trace := current ▸ history.1.trace
  obtain ⟨actual, slot, boundary, prior, sample, initial, state, selected, initialSupport,
      related, sourceSupport, grant, offset, serials, published, reached, activated,
      unchanged, _position⟩ :=
    roster_decision_phase setup leaks extended rosters network reveals openable
      who control trace acting
  have eventEq : actual = event := by
    have actualGrant : (control.execution.observe app who).application.publicView.serviceGrant =
        some actual := by
      change control.execution.application.serviceGrant = _
      rw [unchanged, grant]
    rw [viewEq, granted] at actualGrant
    exact (Option.some.inj actualGrant).symm
  subst actual
  obtain ⟨sourceSite, _, choiceLaw, candidate, raw, opening, handleOwner, valid, _⟩ :=
    roster_owner_choice_data setup leaks bounds reveals admission source.strategy who event owned
      initial initialSupport state boundary related sourceSupport grant
  have localOpening : rosterOpening? setup leaks who event view = some (candidate, raw) := by
    have sameOpening := rosterOpening?_application_eq setup leaks who event control.execution
      boundary unchanged
    rw [viewEq] at sameOpening
    exact sameOpening.trans opening
  obtain ⟨sentEvent, sentCandidate, sentRaw, sentGrant, _, sentOpening, packetEq, unseen⟩ :=
    rosterFresh?_shape setup leaks rosters who past view packet fresh
  rw [granted] at sentGrant
  cases Option.some.inj sentGrant
  rw [localOpening] at sentOpening
  cases Option.some.inj sentOpening
  subst packet
  have choiceFull :
      FullSupport (sourceChoiceLaw setup leaks profile who (boundary.observe app who)) :=
    choiceLaw ▸ setup.reveal_choice_fullSupport reveals admission source mixed who sourceSite
  have physical := rosterPolicy_at_phase setup leaks rosters timing profile boundary
    control.execution event who grant owned candidate raw opening unchanged who
  simp only [EventGraphRuntime.openingWindowMixturePlayers, Function.update_self] at physical
  have hazard := unopened_mixture_probability setup leaks extended rosters boundary event who
    grant owned candidate raw opening handleOwner valid (offset who) serials published
    menu.uniformResponses
    (fun player before input action supported =>
      (menu.uniformResponses_support player before input action).mp supported)
    network ((rosters event).take slot) (roster_count_before selected) prior reached sample
    (by rw [← pastEq, activated] at unseen; exact unseen)
    (sourceChoiceLaw setup leaks profile who (boundary.observe app who)) choiceFull
    (timing event who owned) (timingFull event who owned)
  have choiceNow := sourceChoiceLaw_application_eq setup leaks profile who
    control.execution boundary unchanged
  rw [viewEq] at choiceNow
  have actual : ((players who past view) ((runtime setup).windowOpening leaks event candidate raw)).toReal =
      PMF.deferredHazard (((sourceChoiceLaw setup leaks profile who view) true).toReal)
        (timing event who owned) (past.length - rosterOffset setup rosters who event) := by
    rw [pastEq, viewEq] at physical
    change ((rosterPolicy setup leaks rosters timing profile who past view) _).toReal = _
    rw [physical]
    dsimp only at hazard
    rw [choiceNow]
    simpa only [← pastEq, ← viewEq, activated] using hazard
  have represented := menu.restrictPolicy_map_val (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
    (players who) past view
    (by intro action supported; rw [← pastEq, ← viewEq] at supported ⊢
        exact rosterPolicy_admissible setup leaks bounds rosters network reveals openable
          admission source mixed timing timingFull who control trace acting action supported)
  have restored := congrArg (fun law => law.map (fun action => action.getD ⟨none⟩)) represented
  simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at restored
  change _ = (players who past view).map id at restored
  rw [PMF.map_id] at restored
  have probability := congrArg
    (fun law => (law ((runtime setup).windowOpening leaks event candidate raw)).toReal) restored
  rw [FinDist.prob_map_eq_probOf_preimage_singleton] at probability
  rw [observed]
  exact probability.trans actual

end Vegas

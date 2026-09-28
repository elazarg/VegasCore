/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterSupport
import Vegas.Game.RevealServiceRosterWindowSource
import Vegas.Game.RevealServiceRosterSitePosition

/-! # Harmless local responses inside a disclosure phase

A foreign player may learn the pending disclosure early. Its retained responses
nevertheless have identical eventual disclosure laws. The same holds for the
owner after its unique fresh opening. The proof retains observations and recall;
it compares outcomes without identifying these information sets with source ones.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (rosters : (graph setup).EventId → List Player)

/-- Every local response has the same eventual disclosure law at a foreign
visit or after the owner's opening. This holds pointwise in the hidden execution,
so no posterior equality with a source information set is needed. -/
theorem roster_harmless_response_disclosure
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
    (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (who : Player) (sample : Finset (MessageId Player))
    (action alternative : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters who
      ((current.sampledActivation (application setup leaks) who sample).recall who)
      ((current.sampledActivation (application setup leaks) who sample).observe
        (application setup leaks) who))
    (alternativeMember : alternative ∈ rosterActions setup leaks bounds rosters who
      ((current.sampledActivation (application setup leaks) who sample).recall who)
      ((current.sampledActivation (application setup leaks) who sample).observe
        (application setup leaks) who))
    (within : visits.count owner + (if who = owner then 1 else 0) ≤
      (rosters event).count owner)
    (harmless : who ≠ owner ∨ ∃ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (choices : FinDist (Option (Fin ((rosters event).count owner)))) (full : choices.FullSupport) :
    let app := application setup leaks
    let family := fun mode => app.scheduledPolicy (rosterOffset setup rosters owner event) mode
      (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
        app.replayPolicy
    let activated := current.sampledActivation app who sample
    (((app.policyMixture choices family).posterior
      ((activated.respond app who action).recall owner)).map Option.isSome) =
      ((app.policyMixture choices family).posterior
        ((activated.respond app who alternative).recall owner)).map Option.isSome := by
  intro app family activated
  rcases harmless with foreign | recorded
  · rw [app.respond_recall_other activated who owner foreign.symm action,
      app.respond_recall_other activated who owner foreign.symm alternative]
  · obtain ⟨firstMode, _, _, firstOpen, firstPosterior⟩ :=
      roster_response_posterior setup leaks bounds rosters initial event owner granted ownedEvent
        candidate raw opening owned valid offset serials published players covered network visits
        current reached who sample action member within
    obtain ⟨secondMode, _, _, secondOpen, secondPosterior⟩ :=
      roster_response_posterior setup leaks bounds rosters initial event owner granted ownedEvent
        candidate raw opening owned valid offset serials published players covered network visits
        current reached who sample alternative alternativeMember within
    have firstSome := firstOpen.mpr (Or.inl recorded)
    have secondSome := secondOpen.mpr (Or.inl recorded)
    rw [firstPosterior choices full, secondPosterior choices full]
    cases firstMode with
    | none => cases firstSome
    | some first =>
        cases secondMode with
        | none => cases secondSome
        | some second =>
            simp only [FinDist.map_pure, Option.isSome_some]

/-- The harmless alternatives have identical final source-state laws under
the actual global roster policy. They may change traffic and recall, but these
changes do not change any later source choice or payoff. -/
theorem roster_harmless_response_source_law
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly) (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (event : (graph setup).EventId)
    (source : ProtocolState setup.program) (boundary : (application setup leaks).Execution)
    (related : PublicPrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source boundary)
    (owner : Player) (ownedEvent : (graph setup).actor? event = some owner)
    (granted : boundary.application.serviceGrant = some event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (boundary.observe (application setup leaks) owner) = some (candidate, raw))
    (owned : candidate.1 = owner)
    (valid : boundary.application.candidates.lookup candidate = .openable raw)
    (offset : ∀ player,
      (boundary.recall player).length = rosterOffset setup rosters player event)
    (serials : boundary.network.SerialsBeforeNext)
    (published : boundary.network.Satisfies fun message =>
      message.id ∈ boundary.network.ledger.map Message.id)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who history view response, response ∈ (players who history view).support →
      response ∈ rosterActions setup leaks bounds rosters who history view)
    (visited remaining : List Player) (who : Player)
    (split : rosters event = visited ++ who :: remaining)
    (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visited.map ServiceInstruction.player) boundary).support)
    (sample : Finset (MessageId Player))
    (action alternative : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters who
      ((current.sampledActivation (application setup leaks) who sample).recall who)
      ((current.sampledActivation (application setup leaks) who sample).observe
        (application setup leaks) who))
    (alternativeMember : alternative ∈ rosterActions setup leaks bounds rosters who
      ((current.sampledActivation (application setup leaks) who sample).recall who)
      ((current.sampledActivation (application setup leaks) who sample).observe
        (application setup leaks) who))
    (harmless : who ≠ owner ∨ ∃ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (choiceFull : (sourceChoiceLaw setup leaks profile owner
      (boundary.observe (application setup leaks) owner)).FullSupport)
    (timingFull : (timing event owner ownedEvent).FullSupport)
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose owner) = disclose) :
    let app := application setup leaks
    let rest := (remaining.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event])) ++
      (((List.finRange (eventCount setup.program)).drop (event.val + 1)).flatMap
        (rosterBlock setup rosters))
    let output := fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)
    (((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network rest ((current.sampledActivation app who sample).respond app who action)).map
        output) =
      (((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
        network rest ((current.sampledActivation app who sample).respond app who alternative)).map
          output) := by
  intro app rest output
  let choices := rosterSelection (sourceChoiceLaw setup leaks profile owner
    (boundary.observe app owner)) (timing event owner ownedEvent)
  have full : choices.FullSupport := rosterSelection_fullSupport _ _ choiceFull timingFull
  let family := fun mode : Option (Fin ((rosters event).count owner)) =>
    app.scheduledPolicy (rosterOffset setup rosters owner event) mode
    (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
      app.replayPolicy
  let after := fun response => (current.sampledActivation app who sample).respond app who response
  let posterior := fun response =>
    (app.policyMixture choices family).posterior ((after response).recall owner)
  let visits := visited.count owner + (if who = owner then 1 else 0)
  have complete : visits + remaining.count owner = (rosters event).count owner := by
    rw [split, List.count_append, List.count_cons]
    simp only [beq_iff_eq]
    dsimp only [visits]
    omega
  have within : visited.count owner + (if who = owner then 1 else 0) ≤
      (rosters event).count owner := by
    change visits ≤ _
    omega
  have sourceLaw (response : app.Action)
      (allowed : response ∈ rosterActions setup leaks bounds rosters who
        ((current.sampledActivation app who sample).recall who)
        ((current.sampledActivation app who sample).observe app who)) :
      ((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
        network rest (after response)).map output =
        ((posterior response).bind fun mode =>
          (ProtocolState.step setup.program source (joint mode.isSome)).bind
            (ProtocolState.continuationLaw setup.program profile)).map some := by
    obtain ⟨selected, frame, _, _, exactModes⟩ :=
      roster_response_posterior setup leaks bounds rosters boundary event owner granted ownedEvent
        candidate raw opening owned valid (offset owner) serials published players covered network
        visited current reached who sample response allowed within
    have frames := roster_response_frames setup leaks rosters owner event candidate raw selected
      visits boundary (after response) frame choices full
      (by cases selected <;> exact exactModes choices full)
    exact roster_global_window_source_step_law setup leaks rosters timing network reveals profile
      initial event source boundary related owner ownedEvent granted candidate raw opening visits
      (after response) serials remaining complete
      (roster_after_response_counts setup leaks rosters network players event boundary current
        offset visited remaining who split reached sample response) joint chosen frames
  rw [sourceLaw action member, sourceLaw alternative alternativeMember]
  have same := roster_harmless_response_disclosure setup leaks bounds rosters boundary event
    owner granted ownedEvent candidate raw opening owned valid (offset owner) serials published
    players covered network visited current reached who sample action alternative member
    alternativeMember within harmless choices full
  have mapped := congrArg (fun law : FinDist Bool =>
    (law.bind fun disclose => (ProtocolState.step setup.program source (joint disclose)).bind
      (ProtocolState.continuationLaw setup.program profile)).map some) same
  simpa only [FinDist.bind_map] using mapped

end Vegas.SourceProgram.RevealService

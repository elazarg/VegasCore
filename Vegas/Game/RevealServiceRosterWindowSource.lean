/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPhase
import Vegas.Game.RevealServiceRosterWindowValue

/-! # The global roster policy implements its conditional source continuation

The same policy used by the finite native game runs both the current remainder
and all later phases. Its private timing posterior is only a proof expression.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Lift the concrete selected frame returned by the response classifier to
every mode of its exact private-recall posterior. -/
theorem roster_response_frames
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (owner : Player)
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (application setup leaks).Execution)
    (frame : (runtime setup).OpeningWindowFrame leaks owner event candidate raw
      (rosterOffset setup rosters owner event) selected visits initial current)
    (choices : PMF (Option (Fin slots))) (full : FullSupport choices) :
    let app := application setup leaks
    let family := fun mode => app.scheduledPolicy (rosterOffset setup rosters owner event) mode
      (fun _ _ => PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
        app.replayPolicy
    let posterior := (app.policyMixture choices family).posterior (current.recall owner)
    posterior = (match selected with
      | none => choices.filter (ReactiveApplication.remainingOpeningSlots visits)
          ⟨none, True.intro, full none⟩
      | some slot => PMF.pure (some slot)) →
    ∀ mode ∈ posterior.support,
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        (rosterOffset setup rosters owner event) mode visits initial current := by
  intro app family posterior exactModes mode possible
  rw [exactModes] at possible
  cases selected with
  | none =>
      have kept := ((PMF.mem_support_filter_iff _).mp possible).1
      apply frame.relabel (runtime setup) leaks owner event candidate raw
        (rosterOffset setup rosters owner event) none mode visits initial current
      cases mode with
      | none => rfl
      | some slot =>
          change visits ≤ slot.val at kept
          simpa only [openingPassed, Option.any_some, Option.any_none,
            decide_eq_false_iff_not, not_lt] using kept
  | some slot =>
      rw [PMF.mem_support_pure_iff _ _] at possible
      cases possible
      exact frame

private theorem settlement_players
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (left right : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId)
    (owner : Player) (ticks : Nat) (current : (application setup leaks).Execution) :
    (runtime setup).runInteractionPlan leaks left network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) current =
    (runtime setup).runInteractionPlan leaks right network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) current := by
  have includeStep (execution : (application setup leaks).Execution) :
      (runtime setup).interactionStep leaks left network (.includeLatest event owner) execution =
      (runtime setup).interactionStep leaks right network (.includeLatest event owner) execution :=
      by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind]
    unfold reactiveLatest
    split <;> rfl
  have tail (execution : (application setup leaks).Execution) :
      (runtime setup).runInteractionPlan leaks left network
        (List.replicate ticks .tick ++ [.expire event]) execution =
      (runtime setup).runInteractionPlan leaks right network
        (List.replicate ticks .tick ++ [.expire event]) execution := by
    induction ticks generalizing execution with
    | zero =>
        simp only [List.replicate_zero, List.nil_append, runInteractionPlan,
          interactionStep, interactionInstruction, PMF.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
        rfl
    | succ ticks ih =>
        simp only [List.replicate_succ, List.cons_append, runInteractionPlan]
        have step : (runtime setup).interactionStep leaks left network .tick execution =
            (runtime setup).interactionStep leaks right network .tick execution := by
          simp only [interactionStep, interactionInstruction, PMF.pure_bind,
            ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
          rfl
        rw [step]
        apply bind_congr_on_support _
        intro next _
        exact ih next
  change ((runtime setup).interactionStep leaks left network (.includeLatest event owner)
    current).bind _ = ((runtime setup).interactionStep leaks right network
      (.includeLatest event owner) current).bind _
  rw [includeStep]
  apply bind_congr_on_support _
  intro next _
  exact tail next

theorem roster_global_window_source_step_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly) (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (event : (graph setup).EventId)
    (source : ProtocolState setup.program) (execution : (application setup leaks).Execution)
    (related : PublicPrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source execution)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (granted : execution.application.serviceGrant = some event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (execution.observe (application setup leaks) owner) = some (candidate, raw))
    (visits : Nat) (current : (application setup leaks).Execution)
    (serials : execution.network.SerialsBeforeNext)
    (remaining : List Player)
    (complete : visits + remaining.count owner = (rosters event).count owner)
    (counts : ∀ who, (current.recall who).length + remaining.count who =
      (((List.finRange (graph setup).order.eventCount).take (event.val + 1)).flatMap
        rosters).count who)
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose owner) = disclose) :
    let app := application setup leaks
    let choices := rosterSelection (sourceChoiceLaw setup leaks profile owner
      (execution.observe app owner)) (timing event owner owned)
    let family := fun mode => app.scheduledPolicy (rosterOffset setup rosters owner event) mode
      (fun _ _ => PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
        app.replayPolicy
    let posterior := (app.policyMixture choices family).posterior (current.recall owner)
    (∀ mode ∈ posterior.support,
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        (rosterOffset setup rosters owner event) mode visits execution current) →
    ((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network ((remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event])) ++
        (((List.finRange (eventCount setup.program)).drop (event.val + 1)).flatMap
          (rosterBlock setup rosters))) current).map
      (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      (posterior.bind fun mode => (ProtocolState.step setup.program source (joint mode.isSome)).bind
        (ProtocolState.continuationLaw setup.program profile)).map some := by
  intro app choices family posterior frames
  obtain ⟨mode, supported⟩ := posterior.support_nonempty
  have unchanged := (frames mode supported).application
  have phaseLaw : (runtime setup).runInteractionPlan leaks
      (rosterPolicy setup leaks rosters timing profile) network
      (remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
      current =
      (runtime setup).runInteractionPlan leaks
        ((runtime setup).openingWindowMixturePlayers leaks owner event candidate raw
          (rosterOffset setup rosters owner event) choices) network
        (remaining.map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
        current := by
    rw [runInteractionPlan_append, runInteractionPlan_append,
      rosterPolicy_window_eq setup leaks rosters timing profile execution current event owner
        granted owned candidate raw opening unchanged network remaining]
    apply bind_congr_on_support _
    intro next _
    exact settlement_players setup leaks _ _ network event owner (event.val + 1) next
  rw [runInteractionPlan_append, phaseLaw]
  exact roster_window_source_step_law setup leaks rosters timing network reveals profile initial
    event source execution related owner owned candidate raw opening
    (rosterOffset setup rosters owner event) ((rosters event).count owner) choices visits current
    serials remaining complete counts joint chosen frames

open Classical in
/-- The full actual source-terminal value after any legal local owner
response before opening. All later phases use the original global profile. -/
theorem roster_owner_response_source_value [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
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
    (offset : (boundary.recall owner).length = rosterOffset setup rosters owner event)
    (serials : boundary.network.SerialsBeforeNext)
    (published : boundary.network.Satisfies fun message =>
      message.id ∈ boundary.network.ledger.map Message.id)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who history view response, response ∈ (players who history view).support →
      response ∈ rosterActions setup leaks bounds rosters who history view)
    (visited remaining : List Player)
    (complete : visited.count owner + 1 + remaining.count owner = (rosters event).count owner)
    (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visited.map ServiceInstruction.player) boundary).support)
    (sample : Finset (MessageId Player)) (action : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters owner
      ((current.sampledActivation (application setup leaks) owner sample).recall owner)
      ((current.sampledActivation (application setup leaks) owner sample).observe
        (application setup leaks) owner))
    (unopened : ¬ ∃ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (counts : ∀ who,
      (((current.sampledActivation (application setup leaks) owner sample).respond
        (application setup leaks) owner action).recall who).length + remaining.count who =
        (((List.finRange (graph setup).order.eventCount).take (event.val + 1)).flatMap
          rosters).count who)
    (choiceFull : FullSupport (sourceChoiceLaw setup leaks profile owner
      (boundary.observe (application setup leaks) owner)))
    (timingFull : FullSupport (timing event owner ownedEvent))
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose owner) = disclose)
    (utility : State L setup.program.terminalCtx → ℝ) :
    let app := application setup leaks
    let after := (current.sampledActivation app owner sample).respond app owner action
    let sourceValue := fun disclose =>
      expect ((ProtocolState.step setup.program source (joint disclose)).bind
        (ProtocolState.continuationLaw setup.program profile)) utility
    let probability := ((sourceChoiceLaw setup leaks profile owner
      (boundary.observe app owner)) true).toReal
    expect ((runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing profile)
      network ((remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event])) ++
        (((List.finRange (eventCount setup.program)).drop (event.val + 1)).flatMap
          (rosterBlock setup rosters))) after)
      (fun final => (sourceReadout setup leaks (some ⟨0, none, final⟩)).elim 0 utility) =
      if action = (runtime setup).windowOpening leaks event candidate raw then sourceValue true else
        PMF.deferredRemaining probability (timing event owner ownedEvent)
          (visited.count owner + 1) * sourceValue true +
        (1 - PMF.deferredRemaining probability (timing event owner ownedEvent)
          (visited.count owner + 1)) * sourceValue false := by
  intro app after sourceValue probability
  let choice := sourceChoiceLaw setup leaks profile owner (boundary.observe app owner)
  let choices := rosterSelection choice (timing event owner ownedEvent)
  have full : FullSupport choices := rosterSelection_fullSupport _ _ choiceFull timingFull
  let family := fun mode : Option (Fin ((rosters event).count owner)) =>
    app.scheduledPolicy (rosterOffset setup rosters owner event) mode
    (fun _ _ => PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
      app.replayPolicy
  let posterior := (app.policyMixture choices family).posterior (after.recall owner)
  obtain ⟨selected, frame, _recorded, _same, exactModes⟩ :=
    roster_response_posterior setup leaks bounds rosters boundary event owner granted ownedEvent
      candidate raw opening owned valid offset serials published players covered network visited
      current reached owner sample action member (by simp only [↓reduceIte]; omega)
  have frames (mode : Option (Fin ((rosters event).count owner)))
      (possible : mode ∈ posterior.support) :
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        (rosterOffset setup rosters owner event) mode (visited.count owner + 1) boundary after := by
    exact roster_response_frames setup leaks rosters owner event candidate raw selected
      (visited.count owner + 1) boundary after (by simpa only [↓reduceIte] using frame) choices full
      (by cases selected <;> simpa only [↓reduceIte] using exactModes choices full) mode possible
  have law := roster_global_window_source_step_law setup leaks rosters timing network reveals
    profile initial event source boundary related owner ownedEvent granted candidate raw opening
    (visited.count owner + 1) after serials remaining complete counts joint chosen frames
  have value := congrArg
    (fun distribution => expect distribution (fun output => output.elim 0 utility)) law
  simp only [expect_map, Option.elim_some, FinDist.expect_bind] at value
  rw [value]
  have conditional := roster_owner_response_value setup leaks bounds rosters boundary event owner
    granted ownedEvent candidate raw opening owned valid offset serials published players covered
    network visited (by omega) current reached sample action member unopened choice choiceFull
    (timing event owner ownedEvent) timingFull (sourceValue true) (sourceValue false)
  convert conditional using 1
  apply expect_congr_on_support
  intro mode _
  cases mode <;> simp only [sourceValue, FinDist.expect_bind, Option.isSome_none,
    Option.isSome_some, Bool.false_eq_true, ↓reduceIte]

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterMenu
import Vegas.Pending.ReactiveOpeningSettlement

/-! # All permitted prefixes of a revelation roster

The support argument ranges over arbitrary policies covered by the retained
menu. A first fresh submission selects an owner slot; actual response recall
then rules out another one. No source equilibrium or compiled-policy support
is assumed.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (rosters : (graph setup).EventId → List Player)

private def compatibleMode {slots : Nat} (selected : Option (Fin slots))
    (visits : Nat) (mode : Option (Fin slots)) : Prop :=
  match selected with
  | none => match mode with | none => True | some slot => visits ≤ slot.val
  | some slot => mode = some slot

private def mixtureModes (owner : Player) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) (raw : Raw L) {slots : Nat}
    (selected : Option (Fin slots)) (visits : Nat)
    (current : (application setup leaks).Execution) : Prop :=
  ∀ choices : FinDist (Option (Fin slots)), choices.FullSupport → ∀ mode,
    compatibleMode selected visits mode →
    mode ∈ (((application setup leaks).policyMixture choices (fun selected =>
      (application setup leaks).scheduledPolicy (rosterOffset setup rosters owner event) selected
        (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
        (application setup leaks).replayPolicy)).posterior (current.recall owner)).support

private def mixtureExact (owner : Player) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) (raw : Raw L) {slots : Nat}
    (selected : Option (Fin slots)) (visits : Nat)
    (current : (application setup leaks).Execution) : Prop :=
  ∀ choices : FinDist (Option (Fin slots)), ∀ full : choices.FullSupport,
    (((application setup leaks).policyMixture choices (fun selected =>
      (application setup leaks).scheduledPolicy (rosterOffset setup rosters owner event) selected
        (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
        (application setup leaks).replayPolicy)).posterior (current.recall owner)) =
      match selected with
      | none => choices.condOn (ReactiveApplication.remainingOpeningSlots visits)
          ⟨none, True.intro, full none⟩
      | some slot => FinDist.pure (some slot)

private theorem own_response_entry (current : (application setup leaks).Execution)
    (owner : Player) (action : (application setup leaks).Action) :
    ∃ emitted, (current.respond (application setup leaks) owner action).recall owner =
      current.recall owner ++
        [⟨current.observe (application setup leaks) owner, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨none, by simp only [ReactiveApplication.Execution.respond, ↓reduceIte]⟩
  | some transmission =>
      cases transmission with
      | replay id => exact ⟨(current.network.replay owner id).1, by
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]⟩
      | submit submission =>
          refine ⟨some (current.network.submit owner ((application setup leaks).packet
            ((application setup leaks).submit current.application owner submission) owner
              (current.network.known owner) submission)).1, ?_⟩
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]

private theorem windowOpening_not_replay (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (runtime setup).windowOpening leaks event candidate raw ∉
      ((application setup leaks).replayPolicy past view).support := by
  intro member
  rcases (application setup leaks).replayPolicy_cases past view _ member with
    impossible | ⟨id, impossible⟩ <;> cases impossible

private theorem exact_waiting (current : (application setup leaks).Execution)
    (owner : Player) (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (raw : Raw L) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (count : (current.recall owner).length =
      rosterOffset setup rosters owner event + visits)
    (exactModes :
      mixtureExact setup leaks rosters owner event candidate raw selected visits current)
    (action : (application setup leaks).Action)
    (waiting : action ∈ ((application setup leaks).replayPolicy
      (current.recall owner) (current.observe (application setup leaks) owner)).support) :
    mixtureExact setup leaks rosters owner event candidate raw selected (visits + 1)
      (current.respond (application setup leaks) owner action) := by
  intro choices full
  obtain ⟨emitted, recall⟩ := own_response_entry setup leaks current owner action
  rw [recall]
  cases selected with
  | none =>
      exact (application setup leaks).scheduledMixture_waiting_step choices (full none)
        (rosterOffset setup rosters owner event) _ _
        (windowOpening_not_replay setup leaks event candidate raw) _ _ visits count
          (exactModes choices full) waiting
  | some slot =>
      exact (application setup leaks).policyMixture_posterior_pure_snoc choices _ _ _
        (some slot) (exactModes choices full)

private theorem posterior_response {Index : Type} (choices : FinDist Index)
    (policies : Index → (application setup leaks).Policy)
    (current : (application setup leaks).Execution) (owner : Player)
    (action : (application setup leaks).Action) (mode : Index)
    (prior : mode ∈ (((application setup leaks).policyMixture choices policies).posterior
      (current.recall owner)).support)
    (possible : action ∈
      (policies mode (current.recall owner)
        (current.observe (application setup leaks) owner)).support) :
    mode ∈ (((application setup leaks).policyMixture choices policies).posterior
      ((current.respond (application setup leaks) owner action).recall owner)).support := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
      apply (application setup leaks).policyMixture_posterior_support_snoc choices policies
        _ _ mode prior possible
  | some transmission =>
      cases transmission with
      | replay id =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
          apply (application setup leaks).policyMixture_posterior_support_snoc choices policies
            _ _ mode prior possible
      | submit submission =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
          apply (application setup leaks).policyMixture_posterior_support_snoc choices policies
            _ _ mode prior possible

private theorem fresh_at_phase
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (unchanged : current.application = initial.application) (who : Player)
    (action : (application setup leaks).Action)
    (fresh : rosterFresh? setup leaks rosters who (current.recall who)
      (current.observe (application setup leaks) who) = some action) :
    who = owner ∧ action = (runtime setup).windowOpening leaks event candidate raw ∧
      ∀ entry ∈ (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action ≠ (runtime setup).windowOpening leaks event candidate raw := by
  obtain ⟨otherEvent, otherCandidate, otherRaw, grant, actor, data, actionEq, fresh⟩ :=
    rosterFresh?_shape setup leaks rosters who _ _ action fresh
  have currentGrant : current.application.serviceGrant = some event := by rw [unchanged, granted]
  change current.application.serviceGrant = some otherEvent at grant
  have eventEq : otherEvent = event := Option.some.inj (grant.symm.trans currentGrant)
  subst otherEvent
  have whoEq : who = owner := Option.some.inj (actor.symm.trans owned)
  subst who
  rw [rosterOpening?_application_eq setup leaks owner event current initial unchanged,
    opening] at data
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj data)
  exact ⟨rfl, actionEq, fun entry member => actionEq ▸ fresh entry member⟩

private theorem recorded_response
    (current : (application setup leaks).Execution) (who owner : Player)
    (response opening : (application setup leaks).Action) (offset : Nat)
    (before : offset ≤ (current.recall owner).length)
    (recorded : ∃ entry ∈ (current.recall owner).drop offset, entry.action = opening) :
    ∃ entry ∈ ((current.respond (application setup leaks) who response).recall owner).drop offset,
      entry.action = opening := by
  obtain ⟨entry, member, same⟩ := recorded
  obtain ⟨suffix, recall⟩ :=
    (application setup leaks).respond_recall_prefix current who owner response
  refine ⟨entry, ?_, same⟩
  rw [← recall, List.drop_append_of_le_length before]
  exact List.mem_append_left _ member

private theorem choose_current_slot
    (owner : Player) (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (raw : Raw L) (offset : Nat) {slots : Nat} (slot : Fin slots)
    (initial current : (application setup leaks).Execution)
    (frame : (runtime setup).OpeningWindowFrame leaks owner event candidate raw offset
      (none : Option (Fin slots)) slot.val initial current) :
    (runtime setup).OpeningWindowFrame leaks owner event candidate raw offset
      (some slot) slot.val initial current := by
  refine ⟨frame.application, frame.ledger, frame.receipts, frame.count, ?_,
    frame.serials, frame.packets, ?_⟩
  · simpa only [openingPassed, Option.any_none, Option.any_some, lt_self_iff_false,
      decide_false] using frame.counters
  · simp only [openingPassed, Option.any_some, lt_self_iff_false, decide_false,
      Bool.false_eq_true, false_implies]

private theorem initial_exact (initial : (application setup leaks).Execution)
    (owner : Player) (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (raw : Raw L) (slots : Nat)
    (offset : (initial.recall owner).length = rosterOffset setup rosters owner event) :
    mixtureExact setup leaks rosters owner event candidate raw
      (none : Option (Fin slots)) 0 initial := by
  intro choices full
  have dormant := (application setup leaks).policyMixture_posterior_dormant choices
    (fun selected => (application setup leaks).scheduledPolicy
      (rosterOffset setup rosters owner event) selected
        (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
          (application setup leaks).replayPolicy)
    (application setup leaks).replayPolicy (rosterOffset setup rosters owner event)
    (fun selected before view earlier => (application setup leaks).scheduledPolicy_before
      _ selected _ _ before view earlier) (initial.recall owner) offset.le
  have all : ReactiveApplication.remainingOpeningSlots (slots := slots) 0 = Set.univ := by
    ext selected
    cases selected with
    | none => change True ↔ True; rfl
    | some slot => change 0 ≤ slot.val ↔ True; simp
  simpa only [all, FinDist.condOn_univ] using dormant

variable [Fintype Player]

private theorem frame_response
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (ownedEvent : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw)
    {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (frame : (runtime setup).OpeningWindowFrame leaks owner event candidate raw
      (rosterOffset setup rosters owner event) selected visits initial current)
    (past : ∀ slot, selected = some slot → slot.val < visits)
    (recorded : selected.isSome → ∃ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (absent : selected = none → ∀ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action ≠ (runtime setup).windowOpening leaks event candidate raw)
    (modes : mixtureModes setup leaks rosters owner event candidate raw selected visits current)
    (exactModes :
      mixtureExact setup leaks rosters owner event candidate raw selected visits current)
    (who : Player) (action : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters who
      (current.recall who) (current.observe (application setup leaks) who))
    (remaining : visits + (if who = owner then 1 else 0) ≤ slots) :
    ∃ next : Option (Fin slots),
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        (rosterOffset setup rosters owner event) next
          (visits + if who = owner then 1 else 0) initial
            (current.respond (application setup leaks) who action) ∧
      (∀ slot, next = some slot → slot.val < visits + (if who = owner then 1 else 0)) ∧
      (next.isSome → ∃ entry ∈
        ((current.respond (application setup leaks) who action).recall owner).drop
          (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw) ∧
      (next = none → ∀ entry ∈
        ((current.respond (application setup leaks) who action).recall owner).drop
          (rosterOffset setup rosters owner event),
        entry.action ≠ (runtime setup).windowOpening leaks event candidate raw) ∧
      mixtureModes setup leaks rosters owner event candidate raw next
        (visits + if who = owner then 1 else 0)
        (current.respond (application setup leaks) who action) ∧
      mixtureExact setup leaks rosters owner event candidate raw next
        (visits + if who = owner then 1 else 0)
        (current.respond (application setup leaks) who action) := by
  let app := application setup leaks
  have before : rosterOffset setup rosters owner event ≤ (current.recall owner).length := by
    rw [frame.count]
    omega
  rcases roster_response_cases setup leaks bounds rosters who _ _ action member with waiting | fresh
  · refine ⟨selected, ?_, fun slot chosen => lt_of_lt_of_le (past slot chosen) (by omega),
      ?_, ?_, ?_, ?_⟩
    · apply frame.waiting_response (runtime setup) leaks owner event candidate raw
        (rosterOffset setup rosters owner event) selected visits initial current who action
          (app.replayPolicy_cases _ _ action waiting)
      cases selected with
      | none => rfl
      | some slot =>
          have earlier := past slot rfl
          have later : slot.val < visits + (if who = owner then 1 else 0) := by omega
          simp only [openingPassed, Option.any_some, earlier, later, decide_true]
    · intro chosen
      exact recorded_response setup leaks current who owner action _ _ before (recorded chosen)
    · intro empty entry member
      by_cases active : who = owner
      · subst who
        obtain ⟨emitted, recall⟩ := own_response_entry setup leaks current owner action
        rw [recall, List.drop_append_of_le_length before] at member
        rcases List.mem_append.mp member with earlier | latest
        · exact absent empty entry earlier
        · cases List.mem_singleton.mp latest
          intro equal
          change action = (runtime setup).windowOpening leaks event candidate raw at equal
          exact windowOpening_not_replay setup leaks event candidate raw _ _ (equal ▸ waiting)
      · rw [app.respond_recall_other current who owner (Ne.symm active) action] at member
        exact absent empty entry member
    · intro choices full mode compatible
      by_cases active : who = owner
      · subst who
        have previous : compatibleMode selected visits mode := by
          cases selected with
          | none =>
              cases mode with
              | none => trivial
              | some slot =>
                  change visits + (if owner = owner then 1 else 0) ≤ slot.val at compatible
                  change visits ≤ slot.val
                  simp only [↓reduceIte] at compatible
                  omega
          | some slot => exact compatible
        have old := modes choices full mode previous
        apply posterior_response setup leaks choices _ current owner action mode old
        change action ∈ (app.scheduledPolicy (rosterOffset setup rosters owner event) mode
          (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
            app.replayPolicy (current.recall owner) (current.observe app owner)).support
        have different : mode.map (fun slot => rosterOffset setup rosters owner event + slot.val) ≠
            some (current.recall owner).length := by
          rw [frame.count]
          cases selected with
          | none =>
              cases mode with
              | none => simp
              | some slot =>
                  change visits + (if owner = owner then 1 else 0) ≤ slot.val at compatible
                  simp only [↓reduceIte] at compatible
                  simp only [Option.map_some]
                  intro equal
                  have same := Option.some.inj equal
                  omega
          | some slot =>
              change mode = some slot at compatible
              subst mode
              have earlier := past slot rfl
              simp only [Option.map_some]
              intro equal
              have same := Option.some.inj equal
              omega
        simpa only [ReactiveApplication.scheduledPolicy, ite_eq_right different] using waiting
      · have different : owner ≠ who := Ne.symm active
        simp only [active, ↓reduceIte, Nat.add_zero] at compatible ⊢
        rw [app.respond_recall_other current who owner different action]
        exact modes choices full mode compatible
    · by_cases active : who = owner
      · subst who
        simpa only [↓reduceIte] using exact_waiting setup leaks rosters current owner event
          candidate raw selected visits frame.count exactModes action waiting
      · intro choices full
        simp only [active, ↓reduceIte, Nat.add_zero]
        rw [app.respond_recall_other current who owner (Ne.symm active) action]
        exact exactModes choices full
  · obtain ⟨whoEq, actionEq, freshAbsent⟩ :=
      fresh_at_phase setup leaks rosters initial current event owner
        granted ownedEvent candidate raw opening frame.application who action fresh
    subst who
    subst action
    have empty : selected = none := by
      cases selected with
      | none => rfl
      | some slot =>
          obtain ⟨entry, member, same⟩ := recorded rfl
          exact False.elim (freshAbsent entry member same)
    subst selected
    have inside : visits < slots := by
      simp only [↓reduceIte] at remaining
      omega
    let slot : Fin slots := ⟨visits, inside⟩
    have chosen := choose_current_slot setup leaks owner event candidate raw
      (rosterOffset setup rosters owner event) slot initial current frame
    have next := chosen.opening_response (runtime setup) leaks owner event candidate raw
      (rosterOffset setup rosters owner event) slot initial current owned valid
    refine ⟨some slot, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [↓reduceIte] using next
    · intro other same
      cases Option.some.inj same
      simp only [slot, ↓reduceIte]
      omega
    · intro _
      simp only [EventGraphRuntime.windowOpening, ReactiveApplication.Execution.respond, ↓reduceIte]
      rw [List.drop_append_of_le_length before]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩
    · simp only [reduceCtorEq, false_implies]
    · intro choices full mode compatible
      change mode = some slot at compatible
      subst mode
      have prior := modes choices full (some slot) (show visits ≤ slot.val from le_rfl)
      apply posterior_response setup leaks choices _ current owner _ (some slot) prior
      simp only [ReactiveApplication.scheduledPolicy, Option.map_some, frame.count,
        slot, ↓reduceIte, FinDist.mem_support_pure]
    · intro choices full
      obtain ⟨emitted, recall⟩ := own_response_entry setup leaks current owner
        ((runtime setup).windowOpening leaks event candidate raw)
      rw [recall]
      apply app.scheduledMixture_posterior_open choices
        (rosterOffset setup rosters owner event)
        ((runtime setup).windowOpening leaks event candidate raw) app.replayPolicy slot
        (current.recall owner) ⟨current.observe app owner,
          (runtime setup).windowOpening leaks event candidate raw, emitted⟩ frame.count rfl
        (windowOpening_not_replay setup leaks event candidate raw _ _)
      apply app.policyMixture_action_support choices _ _ _ (some slot)
      · exact modes choices full (some slot) (show visits ≤ slot.val from le_rfl)
      · simp only [ReactiveApplication.scheduledPolicy, Option.map_some, frame.count,
          slot, ↓reduceIte, FinDist.mem_support_pure]

private theorem frame_run
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (ownedEvent : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw)
    {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (frame : (runtime setup).OpeningWindowFrame leaks owner event candidate raw
      (rosterOffset setup rosters owner event) selected visits initial current)
    (past : ∀ slot, selected = some slot → slot.val < visits)
    (recorded : selected.isSome → ∃ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (absent : selected = none → ∀ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action ≠ (runtime setup).windowOpening leaks event candidate raw)
    (modes : mixtureModes setup leaks rosters owner event candidate raw selected visits current)
    (exactModes :
      mixtureExact setup leaks rosters owner event candidate raw selected visits current)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who history view response, response ∈ (players who history view).support →
      response ∈ rosterActions setup leaks bounds rosters who history view)
    (network : (runtime setup).NetworkPolicy leaks) (remaining : List Player)
    (enough : visits + remaining.count owner ≤ slots)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (remaining.map ServiceInstruction.player) current).support) :
    ∃ next : Option (Fin slots),
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        (rosterOffset setup rosters owner event) next (visits + remaining.count owner)
          initial final ∧
      (∀ slot, next = some slot → slot.val < visits + remaining.count owner) ∧
      (next.isSome → ∃ entry ∈
        (final.recall owner).drop (rosterOffset setup rosters owner event),
          entry.action = (runtime setup).windowOpening leaks event candidate raw) ∧
      (next = none → ∀ entry ∈
        (final.recall owner).drop (rosterOffset setup rosters owner event),
          entry.action ≠ (runtime setup).windowOpening leaks event candidate raw) ∧
      mixtureModes setup leaks rosters owner event candidate raw next
        (visits + remaining.count owner) final ∧
      mixtureExact setup leaks rosters owner event candidate raw next
        (visits + remaining.count owner) final := by
  let app := application setup leaks
  induction remaining generalizing current visits selected with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      simpa only [List.count_nil, Nat.add_zero] using
        ⟨selected, frame, past, recorded, absent, modes, exactModes⟩
  | cons who rest ih =>
      have count : (who :: rest).count owner =
          (if who = owner then 1 else 0) + rest.count owner := by
        by_cases same : who = owner <;> simp [same, Nat.add_comm]
      rw [count] at enough
      have actor : (ReactiveApplication.Command.activate who).actor?
          ((runtime setup).reactiveApplication leaks) = some who := rfl
      simp only [List.map_cons, EventGraphRuntime.runInteractionPlan,
        EventGraphRuntime.interactionStep, EventGraphRuntime.interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, actor,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map,
        FinDist.bind_bind] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨action, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      let activated := current.sampledActivation app who sample
      have activatedFrame := frame.activate (runtime setup) leaks owner event candidate raw
        (rosterOffset setup rosters owner event) selected visits initial current who sample
      obtain ⟨next, responded, nextPast, nextRecorded, nextAbsent, nextModes, nextExact⟩ :=
        frame_response setup leaks bounds rosters
        initial activated event owner granted ownedEvent candidate raw opening owned valid
          selected visits activatedFrame past recorded absent modes exactModes who action
            (covered who _ _ action supported) (by omega)
      have continued := ih (activated.respond app who action) next
        (visits + if who = owner then 1 else 0) responded nextPast nextRecorded nextAbsent nextModes
          nextExact (by omega) reached
      simpa only [count, Nat.add_assoc] using continued

/-- Every supported window of arbitrary retained-menu policies has one
actual first-opening slot or no opening. This is a support theorem, including
all off-path retained histories, rather than a property of prescribed play. -/
theorem roster_window_support
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
    (within : visits.count owner ≤ (rosters event).count owner)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    ∃ selected : Option (Fin ((rosters event).count owner)),
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        (rosterOffset setup rosters owner event) selected (visits.count owner) initial final ∧
      (∀ slot, selected = some slot → slot.val < visits.count owner) ∧
      (selected.isSome → ∃ entry ∈
        (final.recall owner).drop (rosterOffset setup rosters owner event),
          entry.action = (runtime setup).windowOpening leaks event candidate raw) := by
  have start := OpeningWindowFrame.initial (runtime setup) leaks owner event candidate raw
    (none : Option (Fin ((rosters event).count owner))) initial serials published
  rw [offset] at start
  have modes : mixtureModes setup leaks rosters owner event candidate raw
      (none : Option (Fin ((rosters event).count owner))) 0 initial := by
    intro choices full mode _
    have dormant := (application setup leaks).policyMixture_posterior_dormant choices
      (fun selected => (application setup leaks).scheduledPolicy
        (rosterOffset setup rosters owner event) selected
          (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
            (application setup leaks).replayPolicy)
      (application setup leaks).replayPolicy (rosterOffset setup rosters owner event)
      (fun selected before view earlier => (application setup leaks).scheduledPolicy_before
        _ selected _ _ before view earlier) (initial.recall owner) offset.le
    rw [dormant]
    exact full mode
  have result := frame_run setup leaks bounds rosters initial initial event owner granted
    ownedEvent candidate raw opening owned valid none 0 start (by simp) (by simp)
      (by simp only [← offset, List.drop_length, List.not_mem_nil, false_implies, implies_true])
      modes (initial_exact setup leaks rosters initial owner event candidate raw _ offset)
      players covered network visits (by simpa only [Nat.zero_add] using within) final reached
  obtain ⟨selected, frame, past, recorded, _, _, _⟩ := result
  exact ⟨selected, by simpa only [Nat.zero_add] using frame,
    by simpa only [Nat.zero_add] using past, recorded⟩

private theorem frame_owner_full
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (ownedEvent : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (frame : (runtime setup).OpeningWindowFrame leaks owner event candidate raw
      (rosterOffset setup rosters owner event) selected visits initial current)
    (past : ∀ slot, selected = some slot → slot.val < visits)
    (recorded : selected.isSome → ∃ entry ∈
      (current.recall owner).drop (rosterOffset setup rosters owner event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw)
    (modes : mixtureModes setup leaks rosters owner event candidate raw selected visits current)
    (inside : visits < slots) (choices : FinDist (Option (Fin slots)))
    (full : choices.FullSupport) (action : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters owner
      (current.recall owner) (current.observe (application setup leaks) owner)) :
    action ∈ (((application setup leaks).policyMixture choices (fun selected =>
      (application setup leaks).scheduledPolicy (rosterOffset setup rosters owner event) selected
        (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
        (application setup leaks).replayPolicy)).policy
          (current.recall owner) (current.observe (application setup leaks) owner)).support := by
  let app := application setup leaks
  rcases roster_response_cases setup leaks bounds rosters owner _ _ action member with
    waiting | fresh
  · apply app.policyMixture_action_support choices _ _ _ selected action
    · apply modes choices full selected
      cases selected <;> simp [compatibleMode]
    · have different : selected.map
          (fun slot => rosterOffset setup rosters owner event + slot.val) ≠
          some (current.recall owner).length := by
        rw [frame.count]
        cases selected with
        | none => simp
        | some slot =>
            have earlier := past slot rfl
            intro equal
            have same := Option.some.inj equal
            change rosterOffset setup rosters owner event + slot.val =
              rosterOffset setup rosters owner event + visits at same
            omega
      simpa only [ReactiveApplication.scheduledPolicy, ite_eq_right different] using waiting
  · obtain ⟨_, actionEq, absent⟩ := fresh_at_phase setup leaks rosters initial current event owner
      granted ownedEvent candidate raw opening frame.application owner action fresh
    have empty : selected = none := by
      cases selected with
      | none => rfl
      | some slot =>
          obtain ⟨entry, member, same⟩ := recorded rfl
          exact False.elim (absent entry member same)
    subst selected
    subst action
    let slot : Fin slots := ⟨visits, inside⟩
    apply app.policyMixture_action_support choices _ _ _ (some slot)
    · exact modes choices full (some slot) (show visits ≤ slot.val from le_rfl)
    · simp only [ReactiveApplication.scheduledPolicy, Option.map_some, frame.count,
        slot, ↓reduceIte, FinDist.mem_support_pure]

/-- The owner's actual recall at any retained prefix has the exact scheduled
posterior: unpassed slots before opening, or its unique opening slot afterward.
Replay likelihoods and arbitrary passive samples have cancelled. The initial
law may be any fully supported timing/never law. -/
theorem roster_window_posterior
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
    (within : visits.count owner ≤ (rosters event).count owner)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    ∃ selected : Option (Fin ((rosters event).count owner)),
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        (rosterOffset setup rosters owner event) selected (visits.count owner) initial final ∧
      (∀ slot, selected = some slot → slot.val < visits.count owner) ∧
      (selected.isSome ↔ ∃ entry ∈
        (final.recall owner).drop (rosterOffset setup rosters owner event),
          entry.action = (runtime setup).windowOpening leaks event candidate raw) ∧
      ∀ choices : FinDist (Option (Fin ((rosters event).count owner))),
        ∀ full : choices.FullSupport,
        (((application setup leaks).policyMixture choices (fun selected =>
          (application setup leaks).scheduledPolicy
            (rosterOffset setup rosters owner event) selected
            (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
              (application setup leaks).replayPolicy)).posterior (final.recall owner)) =
          match selected with
          | none => choices.condOn
              (ReactiveApplication.remainingOpeningSlots (visits.count owner))
                ⟨none, True.intro, full none⟩
          | some slot => FinDist.pure (some slot) := by
  have start := OpeningWindowFrame.initial (runtime setup) leaks owner event candidate raw
    (none : Option (Fin ((rosters event).count owner))) initial serials published
  rw [offset] at start
  have modes : mixtureModes setup leaks rosters owner event candidate raw
      (none : Option (Fin ((rosters event).count owner))) 0 initial := by
    intro choices full mode _
    have dormant := (application setup leaks).policyMixture_posterior_dormant choices
      (fun selected => (application setup leaks).scheduledPolicy
        (rosterOffset setup rosters owner event) selected
          (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
            (application setup leaks).replayPolicy)
      (application setup leaks).replayPolicy (rosterOffset setup rosters owner event)
      (fun selected before view earlier => (application setup leaks).scheduledPolicy_before
        _ selected _ _ before view earlier) (initial.recall owner) offset.le
    rw [dormant]
    exact full mode
  obtain ⟨selected, frame, past, recorded, absent, _, exactModes⟩ :=
    frame_run setup leaks bounds rosters
    initial initial event owner granted ownedEvent candidate raw opening owned valid none 0
      start (by simp) (by simp)
      (by simp only [← offset, List.drop_length, List.not_mem_nil, false_implies, implies_true])
      modes
      (initial_exact setup leaks rosters initial owner event candidate raw _ offset)
      players covered network visits (by omega) final reached
  exact ⟨selected, by simpa only [Nat.zero_add] using frame,
    by simpa only [Nat.zero_add] using past, ⟨recorded, fun ⟨entry, member, same⟩ => by
      cases selected with
      | none => exact False.elim (absent rfl entry member same)
      | some slot => rfl⟩,
      fun choices full => by
        cases selected <;> simpa only [Nat.zero_add] using exactModes choices full⟩

/-- At every permitted phase prefix, every retained owner response receives
positive probability under a fully supported timing law. The prefix can be
generated by any retained policies, including early off-path openings. Passive
observation at the current activation is arbitrary. -/
theorem roster_owner_fullSupport
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
    (choices : FinDist (Option (Fin ((rosters event).count owner)))) (full : choices.FullSupport)
    (action : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters owner
      ((current.sampledActivation (application setup leaks) owner sample).recall owner)
      ((current.sampledActivation (application setup leaks) owner sample).observe
        (application setup leaks) owner)) :
    action ∈ (((application setup leaks).policyMixture choices (fun selected =>
      (application setup leaks).scheduledPolicy (rosterOffset setup rosters owner event) selected
        (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
        (application setup leaks).replayPolicy)).policy
      ((current.sampledActivation (application setup leaks) owner sample).recall owner)
      ((current.sampledActivation (application setup leaks) owner sample).observe
        (application setup leaks) owner)).support := by
  have start := OpeningWindowFrame.initial (runtime setup) leaks owner event candidate raw
    (none : Option (Fin ((rosters event).count owner))) initial serials published
  rw [offset] at start
  have modes : mixtureModes setup leaks rosters owner event candidate raw
      (none : Option (Fin ((rosters event).count owner))) 0 initial := by
    intro law lawFull mode _
    have dormant := (application setup leaks).policyMixture_posterior_dormant law
      (fun selected => (application setup leaks).scheduledPolicy
        (rosterOffset setup rosters owner event) selected
          (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
            (application setup leaks).replayPolicy)
      (application setup leaks).replayPolicy (rosterOffset setup rosters owner event)
      (fun selected before view earlier => (application setup leaks).scheduledPolicy_before
        _ selected _ _ before view earlier) (initial.recall owner) offset.le
    rw [dormant]
    exact lawFull mode
  obtain ⟨selected, frame, past, recorded, _, modes, _⟩ := frame_run setup leaks bounds rosters
    initial initial event owner granted ownedEvent candidate raw opening owned valid
      none 0 start (by simp) (by simp)
      (by simp only [← offset, List.drop_length, List.not_mem_nil, false_implies, implies_true])
      modes
      (initial_exact setup leaks rosters initial owner event candidate raw _ offset)
      players covered network visits
        (by omega) current reached
  apply frame_owner_full setup leaks bounds rosters initial
    (current.sampledActivation (application setup leaks) owner sample) event owner
      granted ownedEvent
      candidate raw opening selected (0 + visits.count owner)
        (frame.activate (runtime setup) leaks owner event candidate raw
          (rosterOffset setup rosters owner event) selected _ initial current owner sample)
        past recorded modes (by omega) choices full action member

end Vegas.SourceProgram.RevealService

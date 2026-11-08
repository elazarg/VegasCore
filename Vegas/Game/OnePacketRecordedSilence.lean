/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSiteConsistent

/-! # Components keep silence once the owner has sent for its event

A response is silent or names the event (`Vegas.SilentOrNames`). Along every
history of the one-packet game, once the player's recall has submitted for its
event, the one-packet choice of every such response keeps silence
(`Vegas.decoded_silent_of_recorded`). The as-if-honest choice, every late
option, the slot tier and silence all choose such responses at the player's
turn, so every slot-trembled component built from them keeps silence outside
its uniform tier (`Vegas.parts_silent_of_recorded`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A response is silent or names the event. -/
def SilentOrNames (event : (graph setup).EventId) (response : (application setup timeouts
  leaks).Action) :
    Prop :=
  response.transmission = none ∨ (submittedEvent? timeouts) leaks response = some event

/-- Canonical decisions are silent or name their event. -/
theorem canonical_silentOrNames (who : Player) (past : List (application setup timeouts
  leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    (action : (graph setup).Action event) :
    SilentOrNames (timeouts := timeouts) event
      ((canonicalServiceDecision timeouts) leaks who past view event action) := by
  rcases (canonicalServiceDecision_cases timeouts) leaks who past view event action with
    silent | named
  · left
    rw [silent]
  · exact Or.inr named

/-- Slot-tier responses are silent or name their event. -/
theorem slotResponse_silentOrNames (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId) (slot :
      Nat)
    (choice : Option (OwnAction Player L)) :
    SilentOrNames (timeouts := timeouts) event (slotResponse setup timeouts leaks who past view
      event
      slot choice) := by
  unfold slotResponse
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact canonical_silentOrNames (timeouts := timeouts) who past view event _
    · exact canonical_silentOrNames (timeouts := timeouts) who past view event _

section Recall

variable (setup timeouts leaks) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

/-- Along a history, the owner has sent nothing for an event exactly when its
recall has not recorded the event. -/
theorem unsentFor_iff_unrecorded {who : Player}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} {control : (application setup timeouts
      leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    (recallEq : control.execution.logs who = past) {key : LateKey setup timeouts leaks}
    (siteKey : lateKey setup timeouts leaks who (some (past, view)) = some key)
    (event : (graph setup).EventId) :
    UnsentFor (timeouts := timeouts) key event ↔ (eventRecorded timeouts) leaks past event = false
      := by
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  constructor
  · intro unsent
    apply Bool.eq_false_of_not_eq_true
    intro recorded
    rw [← recallEq] at recorded
    obtain ⟨message, member, named⟩ := (history_eventRecorded_iff (timeouts := timeouts) trace who
      event).mp recorded
    rw [recallEq] at member
    obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
    exact unsent _ (List.mem_map_of_mem entryMember) message emitted named
  · intro unrecorded recalledEntry member message emitted named
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    have recorded := (history_eventRecorded_iff (timeouts := timeouts) trace who event).mpr
      ⟨message, by
        rw [recallEq]
        exact List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩, named⟩
    rw [recallEq, unrecorded] at recorded
    cases recorded

/-- **A late delivery decides its pending event.** At a decision input of `who`
with pending event `event`, along a history whose recall of `who` is the
input's, the late-delivery key decides `event`. -/
theorem decidedEvent_eq_of_pending {who : Player}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} {event : (graph setup).EventId}
    (pending : pendingEvent setup timeouts leaks who (some (past, view)) = some event)
    {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    (recallEq : control.execution.logs who = past) {key : LateKey setup timeouts leaks}
    (siteKey : lateKey setup timeouts leaks who (some (past, view)) = some key) :
    decidedEvent (timeouts := timeouts) key = some event := by
  obtain ⟨turn, _, owned, unrecorded⟩ := pendingEvent_spec (timeouts := timeouts) pending
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst ownerEq
      unfold decidedEvent
      rw [turnEvent_of_publicationTurn (timeouts := timeouts) ⟨turn, payload, binding, checks,
        outputEq, codeEq, node⟩]
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((EventGraph.actor?_of_outputLayout_binding _ outputEq).symm.trans
          owned)
      subst ownerEq
      have noPublication : turnEvent (timeouts := timeouts) (setup := setup) (leaks := leaks)
          { owner := owner
            current := operationalView setup timeouts leaks view
            recalled := past.map fun entry =>
              (operationalView setup timeouts leaks entry.beforeView, entry.emitted)
            delivered := deliveredValue setup timeouts leaks owner view } =
              none := by
        cases found : turnEvent (timeouts := timeouts) (setup := setup) (leaks := leaks) _ with
        | none => rfl
        | some other =>
            obtain ⟨otherTurn, _, _, _, _, _, otherNode⟩ := publicationTurn_of_turnEvent (timeouts
              := timeouts) found
            have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
            subst same
            rw [node] at otherNode
            cases otherNode
      have unsent : UnsentFor (timeouts := timeouts) (setup := setup) (leaks := leaks)
          { owner := owner
            current := operationalView setup timeouts leaks view
            recalled := past.map fun entry =>
              (operationalView setup timeouts leaks entry.beforeView, entry.emitted)
            delivered := deliveredValue setup timeouts leaks owner view }
              event := by
        intro recalledEntry member message emitted named
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        have recorded := (history_eventRecorded_iff (timeouts := timeouts) trace owner event).mpr
          ⟨message, by
            rw [recallEq]
            exact List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩, named⟩
        rw [recallEq, unrecorded] at recorded
        cases recorded
      have binding : BindingTurn (timeouts := timeouts) (setup := setup) (leaks := leaks)
          { owner := owner
            current := operationalView setup timeouts leaks view
            recalled := past.map fun entry =>
              (operationalView setup timeouts leaks entry.beforeView, entry.emitted)
            delivered := deliveredValue setup timeouts leaks owner view }
              event payload :=
        ⟨turn, ⟨outputEq, codeEq, node⟩, unsent⟩
      unfold decidedEvent
      rw [noPublication]
      cases found : bindingTurn (timeouts := timeouts) (setup := setup) (leaks := leaks) _ with
      | none =>
          unfold bindingTurn at found
          split at found
          · cases found
          · rename_i noTurn
            exact (noTurn ⟨(event, payload), binding⟩).elim
      | some decided =>
          obtain ⟨decidedTurn, _, _⟩ := bindingTurn_spec (timeouts := timeouts) found
          exact congrArg some (Option.some.inj (decidedTurn.symm.trans turn))

end Recall

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **Recorded events are silent.** Along every history of the one-packet game,
once the player's recall has submitted for an event, the one-packet choice of a
response that is silent or names the event keeps silence. -/
theorem decoded_silent_of_recorded {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : (eventRecorded timeouts) leaks (control.execution.logs who) event = true)
    (response : (application setup timeouts leaks).Action) (named : SilentOrNames (timeouts :=
      timeouts) event response) :
    (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
      (some (control.execution.logs who,
        control.execution.observe (application setup timeouts leaks) who)) response).1.getD ⟨none⟩ =
      ⟨none⟩ := by
  by_cases member : response ∈ bounds.onePacketActions timeouts leaks who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who)
  · rcases named with silent | names
    · simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]
      rcases response with ⟨transmission⟩
      change transmission = none at silent
      rw [silent]
    · exact (onePacket_recorded_not_offered (timeouts := timeouts) trace who event recorded response
        names
        member).elim
  · simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]

/-- Laws of responses that are silent or name the event give choices that keep
silence once the event is recorded. -/
theorem map_responseChoice_silent {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : (eventRecorded timeouts) leaks (control.execution.logs who) event = true)
    (law : PMF (application setup timeouts leaks).Action)
    (named : ∀ response ∈ law.support, SilentOrNames (timeouts := timeouts) event response) :
    ∀ choice ∈ (law.map (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler
      who (some (control.execution.logs who,
        control.execution.observe (application setup timeouts leaks) who)))).support,
      choice.1.getD ⟨none⟩ = ⟨none⟩ := by
  intro choice member
  obtain ⟨response, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  exact decoded_silent_of_recorded (timeouts := timeouts) trace who event recorded response (named
    response supported)

/-- **The parts of a component keep silence once the event is recorded.** At the
player's turn at an event its recall has submitted for, the as-if-honest choice,
every late option, the slot tier and silence choose only silence. -/
theorem parts_silent_of_recorded (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (recorded : (eventRecorded timeouts) leaks (control.execution.logs who) event = true) :
    (∀ choice ∈ (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      assessment
        who (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))).support,
        choice.1.getD ⟨none⟩ = ⟨none⟩) ∧
    (∀ choice ∈ (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      assessment
        who (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))).support,
        choice.1.getD ⟨none⟩ = ⟨none⟩) ∧
    (∀ {slots : Nat} (option : LateOption slots),
      ∀ choice ∈ (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        assessment
        who (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who)) option).support,
        choice.1.getD ⟨none⟩ = ⟨none⟩) ∧
    (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))).1.getD ⟨none⟩ =
      ⟨none⟩ := by
  have turnView : (control.execution.observe (application setup timeouts leaks)
      who).application.publicView.ownTurn? who = some event := turn
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply map_responseChoice_silent (timeouts := timeouts) trace who event recorded
    intro response supported
    unfold honestResponse at supported
    rw [turnView] at supported
    obtain ⟨choice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    split
    · exact Or.inl rfl
    · exact canonical_silentOrNames (timeouts := timeouts) who _ _ event _
  · apply map_responseChoice_silent (timeouts := timeouts) trace who event recorded
    intro response supported
    unfold slotTierResponse at supported
    rw [turnView] at supported
    obtain ⟨pair, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact slotResponse_silentOrNames (timeouts := timeouts) who _ _ event pair.1 pair.2
  · intro slots option
    apply map_responseChoice_silent (timeouts := timeouts) trace who event recorded
    intro response supported
    cases option with
    | none =>
        rw [lateResponse, PMF.mem_support_pure_iff] at supported
        rw [supported]
        exact Or.inl rfl
    | some slot =>
        unfold lateResponse at supported
        rw [turnView] at supported
        obtain ⟨choice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        exact slotResponse_silentOrNames (timeouts := timeouts) who _ _ event slot.val choice
  · rw [silenceChoice_val (timeouts := timeouts) who _ rfl]
    rfl

end Vegas

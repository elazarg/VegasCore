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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A response is silent or names the event. -/
def SilentOrNames (event : (graph setup).EventId) (response : (application setup leaks).Action) :
    Prop :=
  response.transmission = none ∨ (runtime setup).submittedEvent? leaks response = some event

/-- Canonical decisions are silent or name their event. -/
theorem canonical_silentOrNames (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (action : (graph setup).Action event) :
    SilentOrNames event
      ((runtime setup).canonicalServiceDecision leaks who past view event action) := by
  rcases (runtime setup).canonicalServiceDecision_cases leaks who past view event action with
    silent | named
  · left
    rw [silent]
  · exact Or.inr named

/-- Slot-tier responses are silent or name their event. -/
theorem slotResponse_silentOrNames (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId) (slot : Nat)
    (choice : Option (OwnAction Player L)) :
    SilentOrNames event (slotResponse setup leaks who past view event slot choice) := by
  unfold slotResponse
  split
  · exact Or.inl rfl
  · split
    · right
      rfl
    · exact canonical_silentOrNames who past view event _
    · exact canonical_silentOrNames who past view event _

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Recorded events are silent.** Along every history of the one-packet game,
once the player's recall has submitted for an event, the one-packet choice of a
response that is silent or names the event keeps silence. -/
theorem decoded_silent_of_recorded {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event = true)
    (response : (application setup leaks).Action) (named : SilentOrNames event response) :
    (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who)) response).1.getD ⟨none⟩ =
      ⟨none⟩ := by
  by_cases member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
  · rcases named with silent | names
    · simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]
      rcases response with ⟨transmission⟩
      change transmission = none at silent
      rw [silent]
    · exact (onePacket_recorded_not_offered trace who event recorded response names
        member).elim
  · simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]

/-- Laws of responses that are silent or name the event give choices that keep
silence once the event is recorded. -/
theorem map_responseChoice_silent {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event = true)
    (law : PMF (application setup leaks).Action)
    (named : ∀ response ∈ law.support, SilentOrNames event response) :
    ∀ choice ∈ (law.map (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler
      who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who)))).support,
      choice.1.getD ⟨none⟩ = ⟨none⟩ := by
  intro choice member
  obtain ⟨response, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  exact decoded_silent_of_recorded trace who event recorded response (named response supported)

/-- **The parts of a component keep silence once the event is recorded.** At the
player's turn at an event its recall has submitted for, the as-if-honest choice,
every late option, the slot tier and silence choose only silence. -/
theorem parts_silent_of_recorded (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event = true) :
    (∀ choice ∈ (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
        who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))).support,
        choice.1.getD ⟨none⟩ = ⟨none⟩) ∧
    (∀ choice ∈ (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
        who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))).support,
        choice.1.getD ⟨none⟩ = ⟨none⟩) ∧
    (∀ {slots : Nat} (option : LateOption slots),
      ∀ choice ∈ (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
        who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) option).support,
        choice.1.getD ⟨none⟩ = ⟨none⟩) ∧
    (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))).1.getD ⟨none⟩ =
      ⟨none⟩ := by
  have turnView : (control.execution.observe (application setup leaks)
      who).application.publicView.ownTurn? who = some event := turn
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply map_responseChoice_silent trace who event recorded
    intro response supported
    unfold honestResponse at supported
    rw [turnView] at supported
    obtain ⟨choice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    split
    · exact Or.inl rfl
    · exact canonical_silentOrNames who _ _ event _
  · apply map_responseChoice_silent trace who event recorded
    intro response supported
    unfold slotTierResponse at supported
    rw [turnView] at supported
    obtain ⟨pair, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact slotResponse_silentOrNames who _ _ event pair.1 pair.2
  · intro slots option
    apply map_responseChoice_silent trace who event recorded
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
        exact slotResponse_silentOrNames who _ _ event slot.val choice
  · rw [silenceChoice_val who _ rfl]
    rfl

end Vegas

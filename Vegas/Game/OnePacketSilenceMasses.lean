module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketBindingMasses

@[expose] public section

/-! # Silence masses of the as-if-honest and slot laws

Without a turn, the as-if-honest law and the slot tier are silent
(`Vegas.honestChoice_silence_of_noTurn`, `Vegas.slotChoice_silence_of_noTurn`).
Along every history of the one-packet game, the menu offers no packet naming an
event the player's recall has submitted for (`Vegas.onePacket_recorded_not_offered`),
so after the player's packet for its turn, both laws are silent as well
(`Vegas.honestChoice_silence_of_recorded`, `Vegas.slotChoice_silence_of_recorded`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (application setup timeouts leaks).State} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- Laws pushed along maps agreeing on the support agree. -/
private theorem map_congr_support {α β : Type} (law : PMF α) {f g : α → β}
    (agree : ∀ x ∈ law.support, f x = g x) : law.map f = law.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases supported : x ∈ law.support
  · rw [agree x supported]
  · simp [(PMF.apply_eq_zero_iff law x).mpr supported]

/-- A response the one-packet menu does not offer is sent as silence. -/
theorem responseChoice_of_not_offered (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (response : (application setup timeouts
      leaks).Action)
    (absent : response ∉ bounds.onePacketActions timeouts leaks who past view) :
    responseChoice setup timeouts leaks bounds initial horizon scheduler who (some (past, view))
      response =
      silenceChoice setup timeouts leaks bounds initial horizon scheduler who (some (past, view))
        := by
  classical
  apply Subtype.ext
  simp only [silenceChoice, responseChoice, absent,
    bounds.silence_onePacket timeouts leaks who past view, ↓reduceDIte]

/-- **Silence without a turn.** Without a turn, the as-if-honest choice is
silence. -/
theorem honestChoice_silence_of_noTurn (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView)
    (noTurn : view.application.publicView.ownTurn? who = none) :
    honestChoice setup timeouts leaks bounds initial horizon scheduler assessment who (some (past,
      view)) =
      PMF.pure (silenceChoice setup timeouts leaks bounds initial horizon scheduler who
        (some (past, view))) := by
  change (honestResponse setup timeouts leaks assessment who past view).map _ = _
  have silent : honestResponse setup timeouts leaks assessment who past view = PMF.pure ⟨none⟩ := by
    unfold honestResponse
    rw [noTurn]
  rw [silent, PMF.pure_map]
  rfl

/-- **Silence without a turn.** Without a turn, the slot tier is silence. -/
theorem slotChoice_silence_of_noTurn (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView)
    (noTurn : view.application.publicView.ownTurn? who = none) :
    slotChoice setup timeouts leaks bounds initial horizon scheduler assessment who (some (past,
      view)) =
      PMF.pure (silenceChoice setup timeouts leaks bounds initial horizon scheduler who
        (some (past, view))) := by
  rw [slotChoice]
  have silent : slotTierResponse setup timeouts leaks bounds assessment who past view =
      PMF.pure ⟨none⟩ := by
    simp only [slotTierResponse, noTurn]
  rw [silent, PMF.pure_map]
  rfl

/-- **No second packet.** Along every history of the one-packet game, the menu
offers no packet naming an event the player's recall has submitted for. -/
theorem onePacket_recorded_not_offered {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : (eventRecorded timeouts) leaks (control.execution.logs who) event = true)
    (response : (application setup timeouts leaks).Action)
    (named : (submittedEvent? timeouts) leaks response = some event) :
    response ∉ bounds.onePacketActions timeouts leaks who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) := by
  intro member
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  unfold EventGraphRuntime.submittedEvent? at named
  cases sends : response.transmission with
  | none =>
      rw [sends] at named
      cases named
  | some material =>
      rw [sends] at named
      dsimp only at named
      obtain ⟨entry, entryMember, submitted⟩ := List.any_eq_true.mp recorded
      have submittedEq := of_decide_eq_true submitted
      unfold EventGraphRuntime.submittedEvent? at submittedEq
      cases transmits : entry.action.transmission with
      | none =>
          rw [transmits] at submittedEq
          cases submittedEq
      | some earlier =>
          rw [transmits] at submittedEq
          dsimp only at submittedEq
          obtain ⟨message, emits, call⟩ := (transmissionsEmitted_serviceInvariant (timeouts :=
            timeouts) scheduler).history
            (initialLaw setup) horizon (fun _ _ _ _ member => (List.not_mem_nil member).elim)
            rawTrace who entry entryMember earlier transmits
          have output : message ∈ (application setup timeouts leaks).outputs
              (control.execution.logs who) :=
            List.mem_filterMap.mpr ⟨entry, entryMember, emits⟩
          obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions timeouts leaks who _ _
            response).mp member
          have verdict : CountPermits ((application setup timeouts leaks).outputs
              (control.execution.logs who))
              ((localEnvelope timeouts) leaks who (control.execution.logs who)
                (control.execution.observe (application setup timeouts leaks) who) material) := by
            rcases permitted with silent | ⟨other, otherSends, counted⟩
            · rw [sends] at silent
              cases silent
            · rw [sends] at otherSends
              cases Option.some.inj otherSends
              exact (countPermits_eq_true_iff _ _).mp counted
          have recalled := (countRecall_history timeouts) leaks rawTrace
          have callEq : ((localEnvelope timeouts) leaks who (control.execution.logs who)
              (control.execution.observe (application setup timeouts leaks) who)
                material).payload.call =
              material.call.packet := rfl
          have first := verdict.2.2 message
          rw [(localEnvelope_eq_of_recall timeouts) leaks control.execution recalled.1
            recalled.2.1 who material] at first
          apply first (earlierOwnPacket_of_output rawTrace who _ message output)
          rw [call, submittedEq]
          rw [(localEnvelope_eq_of_recall timeouts) leaks control.execution recalled.1
            recalled.2.1 who material] at callEq
          rw [callEq, named]

/-- Along every history of the one-packet game, a response at the player's turn
that is silent or names the turn's event, for which its recall has submitted, is
sent as silence. -/
theorem onePacket_responseChoice_of_recorded {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : (eventRecorded timeouts) leaks (control.execution.logs who) event = true)
    (response : (application setup timeouts leaks).Action)
    (names : response = ⟨none⟩ ∨ (submittedEvent? timeouts) leaks response = some event) :
    responseChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who)) response =
      silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who)) := by
  rcases names with silent | named
  · subst silent
    rfl
  · exact responseChoice_of_not_offered (timeouts := timeouts) who _ _ response
      (onePacket_recorded_not_offered (timeouts := timeouts) trace who event recorded response
        named)

omit [Fintype Player] in
/-- The slot tier's response at an event is silent or names the event. -/
theorem slotResponse_names (who : Player) (past : List (application setup timeouts
  leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId) (slot :
      Nat)
    (choice : Option (OwnAction Player L)) :
    slotResponse setup timeouts leaks who past view event slot choice = ⟨none⟩ ∨
      (submittedEvent? timeouts) leaks
        (slotResponse setup timeouts leaks who past view event slot choice) = some event := by
  cases encoded : choice.bind (encodeEventAction? setup.program event) with
  | none =>
      left
      unfold slotResponse
      rw [encoded]
  | some action =>
      cases node : nodeView (graph setup) event with
      | bind owner payload outputEq codeEq =>
          by_cases omitted : cast (congrArg EventGraph.EventField.Action outputEq) action = none
          · left
            rw [slotResponse_of_bind setup timeouts leaks who past view event node slot choice
              action encoded, omitted]
          have present : (cast (congrArg EventGraph.EventField.Action outputEq) action).isSome =
              true := Option.isSome_iff_ne_none.mpr omitted
          right
          obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup timeouts leaks
            who past
            view event node slot choice action encoded present
          unfold EventGraphRuntime.submittedEvent?
          rw [transmits]
          change material.call.packet.event? (graph setup) = some event
          have call := congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
            message.payload.call) envelope
          change material.call.packet = .commitment event (who, .prepared slot) at call
          rw [call]
          rfl
      | resolve owner payload binding checks outputEq codeEq =>
          have decision : slotResponse setup timeouts leaks who past view event slot choice =
              (canonicalServiceDecision timeouts) leaks who past view event action := by
            unfold slotResponse
            rw [encoded]
            simp only [node]
          rw [decision]
          exact (canonicalServiceDecision_cases timeouts) leaks who past view event action
      | sample payload law outputEq codeEq =>
          have decision : slotResponse setup timeouts leaks who past view event slot choice =
              (canonicalServiceDecision timeouts) leaks who past view event action := by
            unfold slotResponse
            rw [encoded]
            simp only [node]
          rw [decision]
          exact (canonicalServiceDecision_cases timeouts) leaks who past view event action

omit [Fintype Player] in
/-- The as-if-honest response at a turn is silent or names the turn's event. -/
theorem honestResponse_names (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (response : (application setup timeouts leaks).Action)
    (supported : response ∈ (honestResponse setup timeouts leaks assessment who past
      view).support) :
    response = ⟨none⟩ ∨ (submittedEvent? timeouts) leaks response = some event := by
  unfold honestResponse at supported
  rw [turn] at supported
  obtain ⟨choice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases choice.bind (encodeEventAction? setup.program event) with
  | none => exact Or.inl rfl
  | some action =>
      exact (canonicalServiceDecision_cases timeouts) leaks who past view event action

/-- **Silence after the packet.** Along every history of the one-packet game, at
the player's turn at an event its recall has submitted for, the as-if-honest
choice is silence. -/
theorem honestChoice_silence_of_recorded (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (recorded : (eventRecorded timeouts) leaks (control.execution.logs who) event = true) :
    honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who)) =
      PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))) := by
  change (honestResponse setup timeouts leaks assessment who _ _).map _ = _
  rw [show (honestResponse setup timeouts leaks assessment who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who)).map
      (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))) =
      (honestResponse setup timeouts leaks assessment who (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who)).map
        (fun _ => silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.logs who,
            control.execution.observe (application setup timeouts leaks) who))) from
    map_congr_support _ fun response supported =>
      onePacket_responseChoice_of_recorded (timeouts := timeouts) trace who event recorded response
        (honestResponse_names (timeouts := timeouts) assessment who _ _ event turn response
          supported)]
  exact PMF.map_const _ _

/-- **Silence after the packet.** Along every history of the one-packet game, at
the player's turn at an event its recall has submitted for, the slot tier is
silence. -/
theorem slotChoice_silence_of_recorded (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (recorded : (eventRecorded timeouts) leaks (control.execution.logs who) event = true) :
    slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who)) =
      PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))) := by
  rw [slotChoice_eq_map (timeouts := timeouts) (initialLaw setup) horizon scheduler turn]
  rw [show (slotPairs setup timeouts leaks bounds assessment who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who)).map
      (fun pair => slotChoiceOf setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (control.execution.logs who) (control.execution.observe (application setup timeouts
          leaks) who)
        event pair.1 pair.2) =
      (slotPairs setup timeouts leaks bounds assessment who (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who)).map
        (fun _ => silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.logs who,
            control.execution.observe (application setup timeouts leaks) who))) from
    map_congr_support _ fun pair _ =>
      onePacket_responseChoice_of_recorded (timeouts := timeouts) trace who event recorded _
        (slotResponse_names (timeouts := timeouts) who _ _ event pair.1 pair.2)]
  exact PMF.map_const _ _

end Vegas

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSourceTurn
import Vegas.Game.OnePacketFactorization
import Vegas.Game.IntendedAuthenticOpening
import Vegas.Game.SourceServiceFacts

/-! # Transmissions with positive content

Every packet the one-packet menu offers is a commitment to a binding event or an
opening at a reveal, so the source action it decodes to is an action the event
encodes (`Vegas.onePacket_sentSourceAction`). Along every history of the
one-packet game, a transmission whose content factor is positive names the
player's turn, and its recall has not submitted for that event
(`Vegas.onePacket_content_pos`): without a turn, as-if-honest play chooses no
action; at a turn, it chooses only actions encoding at the turn's event, and a
source action encodes at no other event; and a second packet for a recorded
event is not permitted.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Decoding is defined at every event whose output is not public data. -/
theorem decodeEventAction_isSome : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (event : Fin (eventCount program))
    (action : EventGraph.EventField.Action (outputLayout program event)),
    (∀ payload, outputLayout program event ≠ .publicData payload) →
      (decodeEventAction program event action).isSome
  | _, _, .ret _, event, _, _ => nomatch event
  | _, _, .sample _ _ _ next, event, action, notData => by
      cases event using Fin.cases with
      | zero => exact (notData _ rfl).elim
      | succ tail => exact decodeEventAction_isSome next tail action notData
  | _, _, .commit _ _ _ _ next, event, action, notData => by
      cases event using Fin.cases with
      | zero => rfl
      | succ tail => exact decodeEventAction_isSome next tail action notData
  | _, _, .reveal _ _ _ _ _ _ next, event, action, notData => by
      cases event using Fin.cases with
      | zero => rfl
      | succ tail => exact decodeEventAction_isSome next tail action notData

variable {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **Offered packets decode.** A transmission the one-packet menu offers names
an event, and decodes, after any execution, to a source action encoding at that
event. -/
theorem onePacket_sentSourceAction (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (response : (application setup timeouts
      leaks).Action)
    (member : response ∈ bounds.onePacketActions timeouts leaks who past view)
    (material : (application setup timeouts leaks).Submission)
    (sends : response.transmission = some material)
    (after : (application setup timeouts leaks).Execution) :
    ∃ event action, material.call.packet.event? (graph setup) = some event ∧
      sentSourceAction setup timeouts leaks after response = some action ∧
      (encodeEventAction? setup.program event action).isSome := by
  obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions timeouts leaks who past view
    response).mp member
  have verdict : CountPermits ((application setup timeouts leaks).outputs past)
      ((localEnvelope timeouts) leaks who past view material) := by
    rcases permitted with silent | ⟨other, transmits, counted⟩
    · rw [sends] at silent
      cases silent
    · rw [sends] at transmits
      cases Option.some.inj transmits
      exact (countPermits_eq_true_iff _ _).mp counted
  have correct := verdict.2.1
  unfold CountCallCorrect at correct
  have callEq : ((localEnvelope timeouts) leaks who past view material).payload.call =
      material.call.packet := rfl
  rw [callEq] at correct
  have content : sentSourceAction setup timeouts leaks after response =
      callContent setup after.application material.call.packet := by
    unfold sentSourceAction
    rw [sends]
    rfl
  rw [content]
  generalize material.call.packet = packet at correct ⊢
  cases packet with
  | malformed => exact correct.elim
  | commitment event candidate =>
      obtain ⟨owned, _⟩ := correct
      unfold bindingOwnedBy at owned
      cases node : nodeView (graph setup) event with
      | sample payload law outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
      | resolve owner payload binding checks outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
      | bind owner payload outputEq codeEq =>
          have defined := decodeEventAction_isSome setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (some (after.application.bindingResult candidate payload))) fun payload same => by
              rw [show outputLayout setup.program event = (graph setup).outputLayout event
                from rfl, outputEq] at same
              cases same
          obtain ⟨action, decoded⟩ := Option.isSome_iff_exists.mp defined
          exact ⟨event, action, rfl, by simp only [callContent, node]; exact decoded, by
            rw [encodeEventAction?_decodeEventAction_eq_some _ _ _ _ decoded]
            rfl⟩
  | opening event candidate raw =>
      obtain ⟨_, resolves⟩ := correct
      cases node : nodeView (graph setup) event with
      | sample payload law outputEq codeEq =>
          rw [node] at resolves
          exact resolves.elim
      | bind owner payload outputEq codeEq =>
          rw [node] at resolves
          exact resolves.elim
      | resolve owner payload binding checks outputEq codeEq =>
          have defined := decodeEventAction_isSome setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
            fun payload same => by
              rw [show outputLayout setup.program event = (graph setup).outputLayout event
                from rfl, outputEq] at same
              cases same
          obtain ⟨action, decoded⟩ := Option.isSome_iff_exists.mp defined
          exact ⟨event, action, rfl, by simp only [callContent, node]; exact decoded, by
            rw [encodeEventAction?_decodeEventAction_eq_some _ _ _ _ decoded]
            rfl⟩

/-- Every history of the one-packet game decodes at its completed prefix. -/
theorem onePacket_decodes (profile : BehavioralProfile setup.program)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) :
    ∃ rank point, control.execution.application.config.cut.IsPrefix rank ∧
      sourceServicePrefix? setup rank control.execution.application.config = some point := by
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) profile _ horizon
    scheduler trace control rfl
  exact ⟨rank, _, residual.checkpoint.ordered, residual.decode⟩

/-- **Positive content names the unrecorded turn.** Along every history of the
one-packet game, a transmission the menu offers whose content factor after any
execution is positive names the player's turn, and its recall has not submitted
for that event. -/
theorem onePacket_content_pos (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (response : (application setup timeouts leaks).Action)
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who))
    (material : (application setup timeouts leaks).Submission)
    (sends : response.transmission = some material) (after : (application setup timeouts
      leaks).Execution)
    (positive : 0 < contentFactor setup timeouts leaks assessment who control.execution after
      response) :
    ∃ event, control.execution.application.publicView.ownTurn? who = some event ∧
      (eventRecorded timeouts) leaks (control.execution.logs who) event = false ∧
      material.call.packet.event? (graph setup) = some event := by
  obtain ⟨named, action, packetEvent, sent, encoded⟩ :=
    onePacket_sentSourceAction (timeouts := timeouts) who _ _ response member material sends after
  have weighted : some action ∈ ((assessment.strategy who (sourceViewOf setup timeouts leaks who
      (control.execution.observe (application setup timeouts leaks) who))).map Subtype.val).support
        := by
    unfold contentFactor at positive
    rw [sends] at positive
    dsimp only at positive
    rw [sent] at positive
    exact (PMF.mem_support_iff _ _).mpr (ENNReal.toReal_pos_iff.mp positive).1.ne'
  have supported : some action ∈ (asIfHonestProfile setup timeouts leaks assessment who
      (some (control.execution.logs who,
        control.execution.observe (application setup timeouts leaks) who))).support := weighted
  obtain ⟨rank, point, ordered, decoded⟩ :=
    onePacket_decodes (timeouts := timeouts) (setup.intendedOpeningProfile assessment.strategy)
      trace
  cases turn : control.execution.application.publicView.ownTurn? who with
  | none =>
      rw [asIfHonestProfile_eq_pure_none (timeouts := timeouts) assessment who control.execution
        rank ordered point
        decoded _ turn] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
  | some event =>
      have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
        horizon scheduler trace
      have ready : control.execution.application.config.cut.Ready event :=
        (control.execution.application.publicView_eventReady event).mp
          (PublicView.ownTurn?_spec _ who event turn).1
      have active := control.execution.application.active_of_ready_owned
        (legalFacts setup leaks horizon scheduler control rawTrace).quiescent ready
        (PublicView.ownTurn?_spec _ who event turn).2
      have atTurn := asIfHonestProfile_encodes (timeouts := timeouts) assessment who
        control.execution rank ordered
        point decoded _ event turn active _ supported
      have same : named = event :=
        encodeEventAction?_event_unique setup.program named event action encoded atTurn
      subst same
      refine ⟨named, rfl, ?_, packetEvent⟩
      cases recorded : (eventRecorded timeouts) leaks (control.execution.logs who) named
        with
      | false => rfl
      | true =>
          exfalso
          have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
              scheduler).Trace (some control) :=
            (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
              scheduler trace
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
              have emitted := (transmissionsEmitted_serviceInvariant (timeouts := timeouts)
                scheduler).history
                (initialLaw setup) horizon (fun _ _ _ _ member => (List.not_mem_nil member).elim)
                rawTrace who entry entryMember earlier transmits
              obtain ⟨message, emits, call⟩ := emitted
              have output : message ∈ (application setup timeouts leaks).outputs
                  (control.execution.logs who) :=
                List.mem_filterMap.mpr ⟨entry, entryMember, emits⟩
              obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions timeouts leaks who _ _
                response).mp member
              have verdict : CountPermits ((application setup timeouts leaks).outputs
                  (control.execution.logs who))
                  ((localEnvelope timeouts) leaks who (control.execution.logs who)
                    (control.execution.observe (application setup timeouts leaks) who) material) :=
                      by
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
              rw [callEq, packetEvent]

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotChoiceMasses
import Vegas.Game.OnePacketContentSupport
import Vegas.Game.OnePacketActorRecord

/-! # Realized commitments with positive content

Along every history of the one-packet game, at a binding of the player's turn,
a transmission of the one-packet menu whose content factor after the response
is positive commits at a prepared slot within capacity, fresh before the
response, a successful value of the bound type; it is the slot tier's response
at that slot to the source choice decoded from the value, and its content factor
is the as-if-honest mass of that source choice
(`Vegas.onePacket_commitment_realized`). A commitment of a failed binding
decodes to a failing source action, which as-if-honest play never supports.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Raw data read at its own type is its value. -/
theorem Raw.eq_of_as?_eq_some {raw : Raw L} {payload : L.Ty} {value : L.Val payload}
    (read : raw.as? payload = some value) : raw = ⟨payload, value⟩ := by
  rcases raw with ⟨ty, rawValue⟩
  unfold Raw.as? at read
  split_ifs at read with same
  subst same
  cases Option.some.inj read
  rfl

/-- **Realized commitments with positive content.** Along every history of the
one-packet game, at a binding of the player's turn, a transmission of the
one-packet menu whose content factor after the response is positive is the slot
tier's response, at a prepared slot within capacity, to the source choice
decoded from a value of the bound type, and its content factor is the
as-if-honest mass of that source choice. -/
theorem onePacket_commitment_realized (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material)
    (positive : 0 < contentFactor setup leaks assessment who control.execution
      (control.execution.respond (application setup leaks) who response) response) :
    ∃ serial value, serial < bounds.candidateCount ∧
      response = slotResponse setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event serial
        (sourceOfValue setup event outputEq value) ∧
      contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response =
        (asIfHonestProfile setup leaks assessment who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
            (sourceOfValue setup event outputEq value)).toReal := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := (runtime setup).countRecall_history leaks rawTrace
  obtain ⟨named, turnNamed, _, packetEvent⟩ :=
    onePacket_content_pos assessment trace who response member material sends _ positive
  rw [turn] at turnNamed
  cases Option.some.inj turnNamed
  obtain ⟨effective, permitted⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who _ _
    response).mp member
  have verdict : CountPermits ((application setup leaks).outputs (control.execution.recall who))
      ((runtime setup).localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) material) := by
    rcases permitted with silent | ⟨other, otherSends, counted⟩
    · rw [sends] at silent
      cases silent
    · rw [sends] at otherSends
      cases Option.some.inj otherSends
      exact (countPermits_eq_true_iff _ _).mp counted
  have callEq : ((runtime setup).localEnvelope leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) material).payload.call =
      material.call.packet := rfl
  -- The packet commits at a prepared slot of the player.
  obtain ⟨serial, packet⟩ : ∃ serial,
      material.call.packet = .commitment event (who, .prepared serial) := by
    have correct := verdict.2.1
    unfold CountCallCorrect at correct
    rw [callEq] at correct
    generalize material.call.packet = sent at correct packetEvent ⊢
    cases sent with
    | malformed => exact correct.elim
    | opening other candidate raw =>
        cases Option.some.inj packetEvent
        obtain ⟨_, resolves⟩ := correct
        rw [node] at resolves
        exact resolves.elim
    | commitment other candidate =>
        cases Option.some.inj packetEvent
        obtain ⟨_, _, owner, ⟨serial, slot⟩, _⟩ := correct
        exact ⟨serial, by rw [show candidate = (who, .prepared serial) from Prod.ext owner slot]⟩
  have capacity := offered_commitment_capacity who _ _ response effective material sends packet
  -- No earlier packet of the player commits to the slot, so it is fresh.
  have correct := verdict.2.1
  unfold CountCallCorrect at correct
  rw [callEq, packet] at correct
  obtain ⟨_, evidenceNone, _, _, unused⟩ := correct
  have freshState : control.execution.application.candidates.lookup (who, .prepared serial) =
      .fresh := by
    refine ((preparedFresh_history horizon scheduler rawTrace) who serial).mpr ?_
    rintro ⟨message, input, sender, committed, call⟩
    have output : message ∈ (application setup leaks).outputs (control.execution.recall who) := by
      rw [← recalled.1 who]
      exact List.mem_filter.mpr ⟨input, by simp [sender]⟩
    have earlier := earlierOwnPacket_of_output rawTrace who
      ((application setup leaks).packet ((application setup leaks).submit
        control.execution.application who material) who (control.execution.network.known who)
          material) message output
    rw [← (runtime setup).localEnvelope_eq_of_recall leaks control.execution recalled.1
      recalled.2.1 who material] at earlier
    exact unused message earlier committed call
  have fresh : (control.execution.observe (application setup leaks) who).application.candidates
      (.prepared serial) = .fresh := freshState
  -- The submission carries no evidence and an opening.
  have materialEvidence : material.evidence = .none := by
    have normal := ((runtime setup).reactiveNormalization leaks).menu_normal
      (bounds.rawMenu (runtime setup) leaks) who _ _ response effective
    have materialNormal : material.normalizeReactive who
        (control.execution.observe (application setup leaks) who).application
        (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
          (control.execution.observe (application setup leaks) who)) = material := by
      have transmitted := congrArg ReactiveApplication.Action.transmission normal
      rcases response with ⟨transmission⟩
      change transmission = some material at sends
      subst sends
      exact Option.some.inj transmitted
    have evidence := congrArg WitnessedSubmission.evidence materialNormal
    change EvidenceRequest.canonical (ReactiveApplication.ResponseMenu.knownPackets
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
      (material.evidence.resolve who (material.call.candidateAfter who
        (control.execution.observe (application setup leaks) who).application.candidates)
        (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
          (control.execution.observe (application setup leaks) who))) = material.evidence
      at evidence
    rw [show material.evidence.resolve who (material.call.candidateAfter who
        (control.execution.observe (application setup leaks) who).application.candidates)
        (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
          (control.execution.observe (application setup leaks) who)) = none
      from evidenceNone] at evidence
    exact evidence.symm
  -- The binding result after the response reads the opening.
  rcases material with ⟨⟨sentPacket, opening⟩, sentEvidence⟩
  change sentPacket = _ at packet
  change sentEvidence = _ at materialEvidence
  subst packet materialEvidence
  rcases response with ⟨transmission⟩
  change transmission = _ at sends
  subst sends
  have result := submitted_bindingResult (runtime setup) leaks control.execution who event payload
    serial opening freshState
  have supported : sentSourceAction setup leaks
      (control.execution.respond (application setup leaks) who
        ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩)
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ ∈
      (asIfHonestProfile setup leaks assessment who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).support := by
    unfold contentFactor at positive
    exact (PMF.mem_support_iff _ _).mpr (ENNReal.toReal_pos_iff.mp positive).1.ne'
  have sentEq : sentSourceAction setup leaks
      (control.execution.respond (application setup leaks) who
        ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩)
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ =
      decodeEventAction setup.program event (cast (congrArg EventGraph.EventField.Action
        outputEq.symm) ((opening.bind fun raw => raw.as? payload).elim .failure
          PublicationResult.success)) := by
    unfold sentSourceAction
    simp only [node]
    exact congrArg _ (congrArg _ result)
  cases read : opening.bind fun raw => raw.as? payload with
  | none =>
      exfalso
      rw [read, Option.elim_none] at sentEq
      have failing : Failing (decodeEventAction setup.program event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)))) :=
        decodeEventAction_failing_binding setup.program event.val (by exact event.isLt)
          (by exact outputEq)
      obtain ⟨rank, point, ordered, decoded⟩ :=
        onePacket_decodes (setup.intendedOpeningProfile assessment.strategy) trace
      obtain ⟨action, decodedAction⟩ := Option.isSome_iff_exists.mp
        (decodeEventAction_isSome setup.program event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)))
          fun payload same => by
            rw [show outputLayout setup.program event = (graph setup).outputLayout event
              from rfl, outputEq] at same
            cases same)
      rw [sentEq, decodedAction] at supported
      rw [decodedAction] at failing
      obtain ⟨noFailure, noWithholding⟩ := asIfHonestProfile_success assessment who
        control.execution rank ordered point decoded _ action supported
      cases action with
      | commit owner name actionPayload choice =>
          have failed := failing.1 owner name actionPayload choice rfl
          subst failed
          exact noFailure owner name actionPayload rfl
      | reveal owner name disclose =>
          have withheld : disclose = false := failing.2
          subst withheld
          exact noWithholding owner name rfl
  | some value =>
      obtain ⟨raw, rawOpening, rawRead⟩ := Option.bind_eq_some_iff.mp read
      subst rawOpening
      have rawEq := Raw.eq_of_as?_eq_some rawRead
      subst rawEq
      refine ⟨serial, value, capacity, ?_, ?_⟩
      · exact onePacket_commitment_eq_slotResponse setup leaks bounds who _ _ event node _ member
          _ rfl serial rfl fresh value rfl
      · unfold contentFactor
        dsimp only
        rw [sentEq, read]
        rfl

end Vegas

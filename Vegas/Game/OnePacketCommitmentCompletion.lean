/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstActivationCompletion
import Vegas.Game.OnePacketRealizedCommitment

/-! # Fresh slots and the acceptance invariant after a one-packet commitment

**One-packet commitments use fresh slots.** A transmission of the one-packet
menu committing an event to a prepared slot of the player carries no evidence,
and the slot is fresh before the response: no earlier packet of the player
commits to it (`Vegas.onePacket_commitment_fresh`).

**The acceptance invariant after a commitment.** After such a response whose
meaning after the submission is a successful value at a binding of the player's
turn, the acceptance invariant holds, and the meaning of the slot is that value
(`Vegas.acceptanceInvariant_respond_commitment`). Sent at the first activation,
the packet is a fresh call (`Vegas.onePacket_commitment_freshCall`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **One-packet commitments use fresh slots.** At a history of the one-packet
game, a transmission of the one-packet menu committing an event to a prepared
slot of the player carries no evidence, and the slot is fresh before the
response. -/
theorem onePacket_commitment_fresh {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {serial : Nat} (packet : material.call.packet = .commitment event (who, .prepared serial)) :
    control.execution.application.candidates.lookup (who, .prepared serial) = .fresh ∧
      material.evidence = .none := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := (runtime setup).countRecall_history leaks rawTrace
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
  have correct := verdict.2.1
  unfold CountCallCorrect at correct
  rw [callEq, packet] at correct
  obtain ⟨_, evidenceNone, _, _, unused⟩ := correct
  refine ⟨?_, ?_⟩
  · refine ((preparedFresh_history horizon scheduler rawTrace) who serial).mpr ?_
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
  · have normal := ((runtime setup).reactiveNormalization leaks).menu_normal
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

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem exists_of_forall₂_mem' {α β : Type} {relation : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ relation left right →
      ∀ b ∈ right, ∃ a ∈ left, relation a b
  | _, _, .nil, _, member => (List.not_mem_nil member).elim
  | _, _, .cons head tail, b, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨a, inTail, related⟩ := exists_of_forall₂_mem' tail b later
        exact ⟨a, List.mem_cons_of_mem _ inTail, related⟩

/-- **The acceptance invariant after a commitment.** At a decision of who at
its turn at a binding event in the one-packet game, a transmission of the
one-packet menu committing the event to a prepared slot of who whose meaning
after the submission is a successful value leaves the acceptance invariant at
the state it reaches, and the slot's meaning there is that value. -/
theorem acceptanceInvariant_respond_commitment {remaining : Nat} {who : Player}
    {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    (afterTrace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨remaining, none,
        execution.respond (application setup leaks) who response⟩)) :
    AcceptanceInvariant setup leaks bounds horizon scheduler who
        (respondEntry setup leaks execution who response)
        (sentEnvelope setup leaks execution who material) event execution.application.config
        (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) ∧
      (execution.respond (application setup leaks) who response).application.candidates.lookup
        (who, .prepared serial) = .openable ⟨payload, value⟩ := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have evidenceNone := (onePacket_commitment_fresh trace who response member material sends
    packet).2
  have respondApplication : (execution.respond (application setup leaks) who
      response).application =
      (application setup leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [sends]
  have sameConfig : ((application setup leaks).submit execution.application who
      material).config = execution.application.config := by
    change (submitStep (material.call.register execution.application who) who
      material.call.packet).config = _
    rw [submitStep_config]
    unfold Submission.register
    split
    · split <;> rfl
    · rfl
  have lookupAfter : (execution.respond (application setup leaks) who
      response).application.candidates.lookup (who, .prepared serial) =
      .openable ⟨payload, value⟩ := by
    rw [respondApplication]
    change (submitStep (material.call.register execution.application who) who
      material.call.packet).candidates.lookup (who, .prepared serial) = _
    rw [Submission.candidateAfter_eq]
    exact after
  have callEq : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event (who, .prepared serial) := by
    rcases material with ⟨call, evidence⟩
    change evidence = .none at evidenceNone
    subst evidenceNone
    unfold sentEnvelope
    rw [reactiveApplication_packet_none]
    exact packet
  refine ⟨⟨⟨afterTrace⟩, recordsEntry_respond execution who _ remaining none,
    by rw [respondEntry_of_transmission execution who _ material sends], ready,
    Or.inl ⟨(who, .prepared serial), who, payload, value, callEq, outputEq, lookupAfter⟩,
    fun _ => ?_, fun receipt => ?_⟩, lookupAfter⟩
  · change (execution.respond (application setup leaks) who response).application.config = _
    rw [respondApplication]
    exact sameConfig
  · exfalso
    change (_, true) ∈ execution.receipts at receipt
    obtain ⟨ledgerMessage, inLedger, sameId, _⟩ :=
      exists_of_forall₂_mem' facts.receipts _ receipt
    have lower := facts.serials.ledger ledgerMessage inLedger
    change (who, execution.network.nextSerial who) = ledgerMessage.id at sameId
    rw [← sameId] at lower
    exact Nat.lt_irrefl _ lower

/-- A count-permitted commitment sent while its protected inclusion window fits
is recorded as a fresh call. Only the actual window is needed. -/
theorem onePacket_commitment_freshCall {bound : (graph setup).EventId → Nat}
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial)) :
    FreshCall setup leaks who event bound (respondEntry setup leaks execution who response)
      (sentEnvelope setup leaks execution who material) := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have ready := (execution.application.publicView_eventReady event).mp readyView
  obtain ⟨fresh, evidenceNone⟩ := onePacket_commitment_fresh trace who response member material
    sends packet
  have inTime : (match execution.application.activatedAt event with
      | none => False
      | some entered => execution.application.clock - entered <
          (runtime setup).deadline event) := fits.withinDeadline
  have vacant : execution.application.accepted (.inr event) = none := by
    cases associated : execution.application.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        exact False.elim (ready.1
          (facts.binding.toAssociationInvariant.accepted_complete event candidate associated))
  have unused : ∀ field, execution.application.accepted field ≠ some (who, .prepared serial) :=
    fun field associated => facts.binding.accepted_fixed field _ associated fresh
  rcases material with ⟨⟨sentPacket, opening⟩, sentEvidence⟩
  change sentPacket = _ at packet
  change sentEvidence = .none at evidenceNone
  subst packet evidenceNone
  refine
    { fresh := ⟨_, sends⟩
      emitted := respondEntry_of_transmission execution who response _ sends ▸ rfl
      authored := rfl
      addressed := ?_
      ready := readyView
      fits := fits
      conforming := ?_ }
  · unfold sentEnvelope
    rw [reactiveApplication_packet_none]
    rfl
  · change (runtime setup).freshServiceAcceptable execution.application.publicView
      ⟨(who, execution.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit execution.application who _) who
        (execution.network.known who) _⟩
    rw [reactiveApplication_packet_none,
      execution.application.publicView_tokenFor_of_ready _ event rfl ready]
    refine ⟨?_, rfl⟩
    simp only [PublicView.BindingIncludable, node]
    exact ⟨readyView, inTime, by trivial, by trivial, vacant, unused⟩

end Vegas

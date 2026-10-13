/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstActivationCompletion
import Vegas.Game.OnePacketRealizedCommitment

/-! # The completion point after any one-packet commitment at the first activation

**One-packet commitments use fresh slots.** A transmission of the one-packet
menu committing an event to a prepared slot of the player carries no evidence,
and the slot is fresh before the response: no earlier packet of the player
commits to it (`Vegas.onePacket_commitment_fresh`).

**The acceptance invariant after a commitment.** After such a response whose
meaning after the submission is a successful value at a binding of the player's
turn, the acceptance invariant holds, and the meaning of the slot is that value
(`Vegas.acceptanceInvariant_respond_commitment`). Sent at the first activation,
the packet is a fresh call (`Vegas.onePacket_commitment_freshCall`).

**The completion-point law.** Under the asynchronous contract and the timeliness
margin, at a first activation for a binding whose configuration decodes to a
point of the intended game, a choice transmitting such a commitment whose value
decodes to an intended source action has, under play of any other policies
until the event completes, the completion-point law of the source step of that
action, with success one and no error
(`Vegas.firstActivation_commitment_completionPointLaw`).
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

/-- **A commitment sent at the first activation is a fresh call.** Under the
asynchronous contract and the timeliness margin, at the first activation of who
for a binding event at its turn in the one-packet game, a transmission of the
one-packet menu committing the event to a prepared slot of who is recorded by
the response as a fresh call of who for the event. -/
theorem onePacket_commitment_freshCall {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
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
  have fits := firstActivation_inclusionFits contract timely rawTrace rfl event turn never
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

/-- **The completion-point law of a commitment at the first activation.** Under
the asynchronous contract and the timeliness margin, let who be at its first
activation for the binding event, at a history whose configuration is a prefix
of rank events decoding to a point of the intended game. Let a choice transmit a
commitment of the event to a prepared slot of who whose meaning after the
submission is a value, decoding to a source action intended at the decoded
point. Then, with that choice committed at the history's information state and
any other policies, until the event completes, the completion-point law is the
source step of that source action at the decoded point, with success one and no
error, for every property fresh of controls implied by the event not having
failed. -/
theorem firstActivation_commitment_completionPointLaw
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (profile : ∀ player, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (info : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).InfoState
      who)
    (observed : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      info)
    {response : (application setup leaks).Action} (selected : choice.1 = some response)
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {sourceAction : OwnAction Player L}
    (decodes : sourceOfValue setup event outputEq value = some sourceAction)
    (intendedAction : sourceAction ∈ ProtocolView.intendedAvailable who setup.program
      (ProtocolState.observe who setup.program point))
    {fresh : (application setup leaks).Control → Prop}
    (freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store event →
      fresh control) :
    CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).behavioralSignature) profile who ((profile who).commit info choice))
      rank fresh history 1 (ProtocolState.step setup.program point (fun _ => some sourceAction))
      0 := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  -- The response is in the one-packet menu.
  have infoEq : model.infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change (menu.signals (initialLaw setup) horizon scheduler).infoOf who history.trace = _
    rw [menu.info, current]
    simp [ReactiveApplication.observe]
  have member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who) := by
    have legal := choice.2
    have atSite := observed.symm.trans infoEq
    subst atSite
    obtain ⟨action, offered, actionEq⟩ := legal
    rw [selected] at actionEq
    cases Option.some.inj actionEq
    exact offered
  subst observed
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have rankEq := (ready_iff_rank setup _ rank ordered event).mp ready
  let action : (graph setup).Action event :=
    cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (PublicationResult.success value : PublicationResult (L.Val payload))
  have successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value := by
    simp only [action, cast_cast, cast_eq]
  have actionDecodes : decodeEventAction setup.program event action = some sourceAction :=
    decodes
  -- The source step at the decoded point.
  obtain ⟨found, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program) menu
    horizon scheduler trace _ rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => some sourceAction) (acts who)
  have targetIntended : ProtocolState.Intended setup.program target := by
    refine ProtocolState.intended_step_of_actors setup.program point _ target intendedPoint
      (fun player active => ?_) (by rw [stepEq]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    cases (acts player).symm.trans active
    exact ⟨sourceAction, rfl, intendedAction⟩
  -- Every stop completes the event at the target point.
  have notStopped : ¬ LateStopped setup leaks bounds horizon scheduler found history := by
    rintro ⟨control, state, prefixed⟩
    rw [current] at state
    cases Option.some.inj state
    exact Nat.succ_ne_self found (isPrefix_unique prefixed ordered)
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have call := onePacket_commitment_freshCall contract timely trace event turn never node response
    member material sends packet
  have callEq : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event (who, .prepared serial) := by
    have evidenceNone := (onePacket_commitment_fresh trace who response member material sends
      packet).2
    rcases material with ⟨call, evidence⟩
    change evidence = .none at evidenceNone
    subst evidenceNone
    unfold sentEnvelope
    rw [reactiveApplication_packet_none]
    exact packet
  have pointAt : ∀ stop ∈ (model.runBehavioralUntil certificate
      (Profile.update (sig := model.behavioralSignature) profile who
        ((profile who).commit (model.infoOf who history.trace) choice))
      (LateStopped setup leaks bounds horizon scheduler found) history).support,
      completionPoint setup leaks bounds horizon scheduler found fresh stop = some target := by
    intro stop reaching
    rw [model.runBehavioralUntil_of_running certificate _ notStopped running,
      PMF.mem_support_bind_iff] at reaching
    obtain ⟨next, stepped, reached⟩ := reaching
    have nextState : next.state = some ⟨remaining, none, execution.respond
        (application setup leaks) who response⟩ := by
      have committedStep := menu.run_commit_response (initialLaw setup) horizon scheduler profile
        history who remaining execution current choice _ selected
      have inLaw : next.state ∈ (PMF.pure (α := (application setup leaks).ProtocolState)
          (some ⟨remaining, none, execution.respond (application setup leaks) who
            response⟩)).support := by
        rw [← committedStep, PMF.support_map]
        exact ⟨next, by convert stepped, rfl⟩
      exact (PMF.mem_support_pure_iff _ _).mp inLaw
    have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) :=
      nextState ▸ next.trace
    obtain ⟨invariant, fixed⟩ := acceptanceInvariant_respond_commitment trace event turn
      outputEq response member material sends packet after afterTrace
    obtain ⟨final, state, stepMember, succeeded⟩ := committed_stop_config contract.completes
      certificate _ ready ordered (outputEq := outputEq) codeEq callEq action successful
      (fun control later records done => by
        obtain ⟨earlier, rest, split⟩ := records
        exact (onePacket_freshCall_settles bounds contract.inclusion later who event owned
          earlier rest _ _ split call).2 done)
      next nextState invariant
      ((runtime setup).reactive_respond_application leaks execution who _).1 fixed stop reached
    obtain ⟨before, after, beforeDecoded, afterDecoded, reachedPoint⟩ :=
      decodedPoint_step residual event ready action _ stepMember
    rw [pointDecoded] at beforeDecoded
    cases Option.some.inj beforeDecoded
    rw [actionDecodes, stepEq, PMF.mem_support_pure_iff] at reachedPoint
    subst reachedPoint
    have prefixed : final.execution.application.config.cut.IsPrefix (found + 1) := by
      rw [execution.application.config.step_cut event ready action _ stepMember]
      exact ordered.complete_at event ready rankEq
    have prefixDecoded : sourceServicePrefix? setup (found + 1)
        final.execution.application.config = some after :=
      (decodedPoint_eq_of_isPrefix prefixed).symm.trans afterDecoded
    have good : ProtocolState.Intended setup.program after ∧ fresh final :=
      ⟨targetIntended, freshOf final (not_storeEventFailed_of_outputSucceeded succeeded)⟩
    unfold completionPoint
    rw [state]
    dsimp only
    rw [ite_eq_left prefixed .., prefixDecoded]
    dsimp only
    rw [ite_eq_left good ..]
  intro value bound _
  rw [expect_congr_on_support (g := fun _ => value target) fun stop reaching => by
      rw [pointAt stop reaching]
      rfl,
    expect_constant, stepEq, expect_pure, one_mul, sub_self, abs_zero, zero_mul]

end Vegas

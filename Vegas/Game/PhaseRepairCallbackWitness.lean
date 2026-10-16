/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairSendingWitness

/-! # Actual directed callbacks have the four chronological response forms -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- The actual callback prefixes supply the chronological category witnesses.
Only a genuine final clear binding site is used to classify earlier openings;
there is no local probability, successful-binding or image-support premise. -/
theorem phase_repair_callback_pair (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (who : Player) (remaining : Nat) (original repaired : (app).Execution)
    (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks
      (graph := serviceGraph setup mode)))
    (frame : PhaseBindingRepair.Frame runtime leaks memory who original repaired)
    (past : (original.recall who).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (repaired.recall who).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (left : (E).Trace (some ⟨remaining, some who, original⟩))
    (right : (E).Trace (some ⟨remaining, some who, repaired⟩))
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix left finalTrace)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (finalClear : final.execution.application.current.excluded = ∅)
    (finalRequest : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩)
    (response : (app).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (original.recall who) (original.observe app who)) :
    ∃ sends waits, PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      [(some (original.recall who, original.observe app who), response)]
      [(some (repaired.recall who, repaired.observe app who),
        PhaseBindingRepair.Frame.responseImage (runtime := runtime) (leaks := leaks)
          who who response)] sends waits := by
  classical
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact left
  have rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, repaired⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact right
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ leftTrace
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ rightTrace
  have recallLeft := (app).history_inputRecall _ horizon scheduler rawLeft
  have recallRight := (app).history_inputRecall _ horizon scheduler rawRight
  have outputsEq := frame.outputs recallLeft recallRight who
  obtain ⟨first, last, path⟩ :
      ∃ (first : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
            (some ⟨remaining, some who, original⟩))
        (last : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some final)),
        TracePrefix first last := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact ⟨left, finalTrace, isPrefix⟩
  have attemptEq : original.application.attempt = repaired.application.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have values (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
      (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload ∨
        (serviceGraph setup mode).outputLayout event = .publication payload) :
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
    have allValues := covered event
    rcases outputEq with outputEq | outputEq <;> rwa [outputEq] at allValues
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [PhaseBindingRepair.Frame.responseImage, ↓reduceIte]
      by_cases absent : ∀ coordinate, ¬original.application.SeedRequest who coordinate
      · refine ⟨0, 0, .inert ?_ .nil⟩
        exact ⟨⟨remaining, some who, original⟩, ⟨remaining, some who, repaired⟩,
          left, right, rfl, rfl, frame.clearOriginal, frame.clearRepaired, Or.inl absent,
          Or.inl (fun coordinate request => absent coordinate
            ((frame.seedRequest_iff who coordinate).mpr request)), rfl, rfl⟩
      · obtain ⟨coordinate, request⟩ := not_forall_not.mp absent
        by_cases sent : ∃ message ∈ (app).outputs (original.recall who),
            PhaseSeedScheduler.ownPacket coordinate who message = true
        · refine ⟨0, 0, .inert ?_ .nil⟩
          exact ⟨⟨remaining, some who, original⟩, ⟨remaining, some who, repaired⟩,
            left, right, rfl, rfl, frame.clearOriginal, frame.clearRepaired,
            Or.inr ⟨coordinate, request, sent⟩,
            Or.inr ⟨coordinate, (frame.seedRequest_iff who coordinate).mp request,
              by rwa [← outputsEq]⟩, rfl, rfl⟩
        · rcases coordinate with ⟨attempt, event⟩
          have current : attempt = original.application.attempt := request.1
          subst attempt
          have imageRequest := (frame.seedRequest_iff who
            ⟨original.application.attempt, event⟩).mp request
          rw [attemptEq] at imageRequest
          have unsent : ∀ message ∈ (app).outputs (original.recall who),
              PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩ := by
            intro message output same
            apply sent
            have own : message.sender = who := by
              have authored := output
              rw [← recallLeft who] at authored
              simpa only [decide_eq_true_eq] using (List.mem_filter.mp authored).2
            unfold PhaseCount.event? at same
            obtain ⟨named, actual, same⟩ := Option.map_eq_some_iff.mp same
            have tagEq := congrArg CommitAttemptEvent.attempt same
            have eventEq : named = event := congrArg CommitAttemptEvent.event same
            refine ⟨message, output, ?_⟩
            simp only [PhaseSeedScheduler.ownPacket, decide_eq_true_eq]
            exact ⟨own, tagEq, actual.trans (congrArg some eventEq)⟩
          have imageUnsent : ∀ message ∈ (app).outputs (repaired.recall who),
              PhaseCount.event? message.payload ≠ some ⟨repaired.application.attempt, event⟩ := by
            rw [← outputsEq, ← attemptEq]
            exact unsent
          have acting := request.2.2.2.1
          cases node : nodeView (serviceGraph setup mode) event with
          | sample payload law outputEq codeEq =>
              have codeActor := congrArg EventCode.actor codeEq
              rw [EventCode.actor_cast outputEq _] at codeActor
              have actorNone : (serviceGraph setup mode).actor? event = none := by
                exact codeActor
              rw [actorNone] at acting
              cases acting
          | bind owner payload outputEq codeEq =>
              rw [EventGraph.actor?_of_outputLayout_binding _ outputEq] at acting
              cases Option.some.inj acting
              refine ⟨0, 1, .waiting ?_ .nil⟩
              exact ⟨event, payload, outputEq, ⟨remaining, some who, original⟩,
                ⟨remaining, some who, repaired⟩, left, right, rfl, rfl, request, imageRequest,
                unsent, imageUnsent, values event payload (Or.inl outputEq), frame.clearOriginal,
                frame.clearRepaired, rfl, rfl⟩
          | resolve owner payload binding checks outputEq codeEq =>
              have ownerEq : owner = who := by
                change ((serviceGraph setup mode).nodes event).actor = some who at acting
                rw [← EventCode.actor_cast outputEq _, codeEq] at acting
                exact Option.some.inj acting
              subst owner
              have key := frame.opening_timingKey_eq runtime leaks bounds plan
                (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler who
                  remaining original repaired memory past first final last path finalClear event
                    payload binding checks outputEq codeEq node request imageRequest bindingEvent
                      bindingOwner bindingPayload bindingOutput finalRequest
              refine ⟨0, 0, .opening ?_ .nil⟩
              exact ⟨remaining, original, repaired, memory, frame, left, right, final, finalTrace,
                isPrefix, event, payload, binding, checks, outputEq, codeEq, node,
                bindingEvent, bindingOwner, bindingPayload, bindingOutput, ⟨none⟩,
                finalClear, request, imageRequest, unsent, imageUnsent,
                values event payload (Or.inr outputEq), finalRequest, rfl, rfl, key⟩
  | some material =>
      obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks
        bounds plan inputs horizon scheduler remaining who original leftTrace
          material member
      have named := PhaseCount.onePacket_event_of_request runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
          original leftTrace coordinate request material member
      have allowed : PhaseCount.permits ((app).outputs (original.recall who))
          (PhaseCount.localEnvelope runtime leaks who (original.recall who)
            (original.observe app who) material) = true := by
        rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds who _ _ _).mp member).2
          with impossible | ⟨supplied, same, allowed⟩
        · cases impossible
        · cases Option.some.inj same
          exact allowed
      have correct := ((PhaseCount.permits_eq_true_iff _ _).mp allowed).2.1
      have actualCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks who
          (original.recall who) (original.observe app who) material)).payload.call =
            material.call.packet := PhaseCount.maskPacket_call _ _
      unfold CountCallCorrect at correct
      rw [actualCall] at correct
      rcases material with ⟨⟨packet, preparation⟩, evidence⟩
      cases packet with
      | malformed raw => cases correct
      | commitment event candidate =>
          obtain ⟨bindingOwned, _, candidateOwned, ⟨serial, slot⟩, _⟩ := correct
          change candidate.1 = who at candidateOwned
          have candidateEq : candidate = (who, .prepared serial) := Prod.ext candidateOwned slot
          subst candidate
          have eventEq : coordinate.event = event := Option.some.inj named.symm
          have requestEvent := request
          change original.application.SeedRequest who
            ⟨coordinate.attempt, coordinate.event⟩ at requestEvent
          rw [request.1, eventEq] at requestEvent
          cases node : nodeView (serviceGraph setup mode) event with
          | sample payload law outputEq codeEq =>
              simp only [bindingOwnedBy, outputEq] at bindingOwned
              cases bindingOwned
          | resolve actor payload binding checks outputEq codeEq =>
              simp only [bindingOwnedBy, outputEq] at bindingOwned
              cases bindingOwned
          | bind actor payload outputEq codeEq =>
              change bindingOwnedBy (serviceGraph setup mode) who event = true at bindingOwned
              have actorEq : actor = who := by
                simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq] using bindingOwned
              subst actor
              exact ⟨1, 0, .sending (phase_binding_sending_pair setup mode runtime leaks bounds plan
                horizon scheduler covered who remaining original repaired memory frame left right
                  event payload outputEq serial preparation evidence codeEq node requestEvent
                    member) .nil⟩
      | opening event candidate raw =>
          have eventEq : coordinate.event = event := Option.some.inj named.symm
          have requestEvent := request
          change original.application.SeedRequest who
            ⟨coordinate.attempt, coordinate.event⟩ at requestEvent
          rw [request.1, eventEq] at requestEvent
          have imageRequest := (frame.seedRequest_iff who
            ⟨original.application.attempt, event⟩).mp requestEvent
          rw [attemptEq] at imageRequest
          have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan
            (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
              original leftTrace ⟨original.application.attempt, event⟩ requestEvent
                ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩ member
          have imageUnsent : ∀ message ∈ (app).outputs (repaired.recall who),
              PhaseCount.event? message.payload ≠ some ⟨repaired.application.attempt, event⟩ := by
            rw [← outputsEq, ← attemptEq]
            exact unsent
          cases node : nodeView (serviceGraph setup mode) event with
          | bind actor payload outputEq codeEq => simp only [node, and_false] at correct
          | sample payload law outputEq codeEq => simp only [node, and_false] at correct
          | resolve actor payload binding checks outputEq codeEq =>
              simp only [node] at correct
              have actorEq : actor = who := correct.2.1.symm
              subst actor
              simp only [PhaseBindingRepair.Frame.responseImage, ↓reduceIte]
              have key := frame.opening_timingKey_eq runtime leaks bounds plan
                (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler who
                  remaining original repaired memory past first final last path finalClear event
                    payload binding checks outputEq codeEq node requestEvent imageRequest
                      bindingEvent
                      bindingOwner bindingPayload bindingOutput finalRequest
              refine ⟨0, 0, .opening ?_ .nil⟩
              exact ⟨remaining, original, repaired, memory, frame, left, right, final, finalTrace,
                isPrefix, event, payload, binding, checks, outputEq, codeEq, node,
                bindingEvent, bindingOwner, bindingPayload, bindingOutput,
                ⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩,
                finalClear, requestEvent, imageRequest, unsent, imageUnsent,
                values event payload (Or.inr outputEq), finalRequest, rfl, rfl, key⟩

end Vegas

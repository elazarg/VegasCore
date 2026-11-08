/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairOpeningCandidates
import Vegas.Game.OnePacketDirectedRepairResponseTurn
import Vegas.Game.OnePacketDirectedRepairTrace
import Vegas.Pending.ReactiveCountedResponseForms
import Vegas.Pending.ReactiveBindingSubmittedRepair

/-! # Every actual response has a directed repaired trace extension -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

namespace DirectedBindingFrame

/-- The directed repair lifts every permitted response in a history ending at a
forced focal information set. It retains actual submitted-binding provenance,
private shadow ownership, and the complete operational trace record. -/
theorem response_trace
    {memory : BindingMemory timeouts leaks} {owner : Player}
    {original repaired : (application setup timeouts leaks).Execution}
    (frame : DirectedBindingFrame (timeouts := timeouts) memory owner original repaired)
    (submittedRecords : memory.RecordsSubmittedBindings timeouts leaks owner
      original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (remaining : Nat) (actor : Player)
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some actor, original⟩))
    (imagePrior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some actor, repaired⟩))
    (records : operationalRecord setup timeouts leaks bounds horizon scheduler prior =
      operationalRecord setup timeouts leaks bounds horizon scheduler imagePrior)
    (response : (application setup timeouts leaks).Action)
    (available : response ∈ bounds.onePacketActions timeouts leaks actor
      (original.logs actor) (original.observe (application setup timeouts leaks) actor))
    (covered : bounds.CoversOutputValues)
    {focal : Player} (other : owner ≠ focal)
    {info : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InfoState focal}
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler focal info)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (decision : info = some (past, view))
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory focal
      info)
    {final : (application setup timeouts leaks).Control} (current : history.1.state = some final)
    (afterTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some ⟨remaining, none, original.respond (application setup timeouts leaks) actor response⟩))
    (isPrefix : TracePrefix afterTrace history.1.trace) :
    ∃ targetResponse : (application setup timeouts leaks).Action,
      ∃ nextMemory : BindingMemory timeouts leaks,
        DirectedBindingFrame (timeouts := timeouts) nextMemory owner
          (original.respond (application setup timeouts leaks) actor response)
          (repaired.respond (application setup timeouts leaks) actor targetResponse) ∧
        nextMemory.RecordsSubmittedBindings timeouts leaks owner
          (original.respond (application setup timeouts leaks) actor response)
          (repaired.respond (application setup timeouts leaks) actor targetResponse) ∧
        nextMemory.shadow.OwnBindings owner ∧
        ∃ targetTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
            (some ⟨remaining, none,
              repaired.respond (application setup timeouts leaks) actor targetResponse⟩),
          operationalRecord setup timeouts leaks bounds horizon scheduler targetTrace =
            operationalState setup timeouts leaks
                (some ⟨remaining, none,
                  original.respond (application setup timeouts leaks) actor response⟩) ::
              operationalRecord setup timeouts leaks bounds horizon scheduler prior := by
  classical
  let app := application setup timeouts leaks
  by_cases foreign : actor ≠ owner
  · obtain ⟨afterFrame, targetTrace, targetRecord⟩ := frame.foreign_response_trace (timeouts :=
      timeouts) remaining actor
      foreign prior imagePrior records response available
    exact ⟨response, memory, afterFrame,
      submittedRecords.respond actor response response (Or.inl foreign), onlyBindings,
      targetTrace, targetRecord⟩
  have same : actor = owner := not_ne_iff.mp foreign
  subst actor
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
    horizon scheduler prior
  have count := (countRecall_history timeouts) leaks rawTrace
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      let silence : app.Action := ⟨none⟩
      let nextMemory := memory.record timeouts leaks
        (memory.shadow.inputView timeouts leaks (repaired.observe app owner)) silence
      obtain ⟨afterFrame, targetTrace, targetRecord⟩ :=
        frame.silence_trace remaining prior imagePrior records
      have nonbinding : ∀ material, silence.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate := by
        intro material impossible
        cases impossible
      exact ⟨silence, nextMemory, afterFrame,
        (submittedRecords.respond owner silence silence (Or.inr nonbinding)).record _ silence,
        onlyBindings, targetTrace, targetRecord⟩
  | some material =>
      have parts := (bounds.mem_onePacketActions timeouts leaks owner _ _ _).mp available
      have normal := ((bounds.menu_mem timeouts leaks owner _ _ _).mp parts.1).2
      change (⟨some (material.normalizeReactive owner (original.observe app owner).application
        (ReactiveApplication.ResponseMenu.knownPackets (original.logs owner)
          (original.observe app owner)))⟩ : app.Action) = ⟨some material⟩ at normal
      have materialNormal := Option.some.inj
        (congrArg ReactiveApplication.Action.transmission normal)
      have permitted : countPermits (app.outputs (original.logs owner))
          ((localEnvelope timeouts) leaks owner (original.logs owner)
            (original.observe app owner) material) = true := by
        rcases parts.2 with impossible | ⟨supplied, same, verdict⟩
        · cases impossible
        · cases Option.some.inj same
          exact verdict
      have correct := ((countPermits_eq_true_iff _ _).mp permitted).2.1
      cases packet : material.call.packet with
      | malformed raw =>
          simp only [CountCallCorrect, localEnvelope, packet] at correct
      | commitment event candidate =>
          simp only [CountCallCorrect, localEnvelope, packet] at correct
          have absent : ((localEnvelope timeouts) leaks owner (original.logs owner)
              (original.observe app owner) material).payload.evidence = none := correct.2.1
          have owned : candidate.1 = owner := correct.2.2.1
          obtain ⟨serial, slot⟩ := correct.2.2.2.1
          have candidateEq : candidate = (owner, .prepared serial) := Prod.ext owned slot
          subst candidate
          have shape := (normal_binding_of_absent_evidence timeouts) leaks owner
            (original.logs owner) (original.observe app owner) material event
            (owner, .prepared serial) materialNormal packet absent
          generalize openingEq : material.call.opening = opening at shape
          subst material
          have turn := response_atTurn_of_forced_prefix (timeouts := timeouts) forced decision
            history current remaining
            owner other original ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩,
              .none⟩⟩ afterTrace isPrefix event rfl
          have ready := (original.application.publicView_eventReady event).mp
            (original.application.publicView.ownTurn?_spec owner event turn).1
          cases output : (graph setup).outputLayout event with
          | publicData payload =>
              have impossible : false = true := by
                simpa only [bindingOwnedBy, output] using correct.1
              cases impossible
          | privateInput actor payload =>
              have impossible : false = true := by
                simpa only [bindingOwnedBy, output] using correct.1
              cases impossible
          | publication payload =>
              have impossible : false = true := by
                simpa only [bindingOwnedBy, output] using correct.1
              cases impossible
          | binding actor payload =>
              have ownerEq : actor = owner := of_decide_eq_true (by
                simpa only [bindingOwnedBy, output, Message.sender] using correct.1)
              subst actor
              have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) output)
                  ((graph setup).nodes event) = .bind owner payload := by
                generalize cast (congrArg (EventGraph.EventCode (graph setup).layout) output)
                  ((graph setup).nodes event) = code
                cases code
                rfl
              have node := nodeView_eq_bind output codeEq
              let rawResponse : app.Action :=
                ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
              let changed := memory.repairResponse timeouts leaks owner
                (repaired.observe app owner) rawResponse
              let nextMemory : BindingMemory timeouts leaks :=
                ⟨changed.2, memory.responses ++
                  [(memory.shadow.inputView timeouts leaks (repaired.observe app owner),
                    rawResponse)]⟩
              have initializedPrior := prior
              change ((bounds.onePacketMenu timeouts leaks).protocol
                (serviceInitialLaw setup .sequential) horizon scheduler).Trace _ at initializedPrior
              rw [serviceInitialLaw_eq_inputs] at initializedPrior
              have fresh := bounds.onePacket_binding_fresh timeouts leaks
                (setup.initialLaw.map setup.eventInputs) horizon scheduler initializedPrior owner
                event serial opening available
              obtain ⟨afterFrame, targetTrace, targetRecord⟩ := frame.binding_trace (timeouts :=
                timeouts) remaining prior
                imagePrior records event payload output codeEq node serial opening ready turn
                covered available
              exact ⟨changed.1, nextMemory, afterFrame,
                submittedRecords.binding_submission frame.toFrame count event
                  payload output
                  codeEq node serial opening fresh permitted,
                memory.repairResponse_ownBindings timeouts leaks owner onlyBindings
                  (repaired.observe app owner) rawResponse, targetTrace, targetRecord⟩
      | opening event candidate raw =>
          simp only [CountCallCorrect, localEnvelope, packet] at correct
          obtain ⟨actual, offered, claimed, token, envelope⟩ :=
            (certifiedOpening_iff _).mp correct.1
          have envelopeCall := congrArg WitnessedPacket.call envelope
          change Payload.opening event candidate raw = .opening actual offered claimed
            at envelopeCall
          obtain ⟨rfl, rfl, rfl⟩ := Payload.opening.inj envelopeCall
          have certified := congrArg WitnessedPacket.evidence envelope
          have leftFixed := onePacket_opening_candidate (timeouts := timeouts) prior owner material
            event candidate raw
            packet certified
          cases node : nodeView (graph setup) event with
          | bind | sample => simp only [node, and_false] at correct
          | resolve actor payload binding checks outputEq codeEq =>
              have details : owner = actor ∧ raw.ty = payload ∧
                  SignedBinding
                    (EarlierOwnPacket (app.outputs (original.logs owner))
                      ((localEnvelope timeouts) leaks owner (original.logs owner)
                        (original.observe app owner) material))
                    owner candidate binding.field := by
                simpa only [localEnvelope, packet, node, Message.sender] using correct.2
              have actorEq : actor = owner := details.1.symm
              subst actor
              have typed := details.2.1
              have signed := details.2.2
              rcases raw with ⟨rawPayload, value⟩
              dsimp only at typed
              subst rawPayload
              obtain ⟨owned, rightFixed⟩ := frame.opening_candidate_of_signed
                submittedRecords
                prior imagePrior material binding candidate value leftFixed signed
              have localFixed : (original.observe app owner).application.candidates candidate.2 =
                  .openable ⟨payload, value⟩ := by
                change original.application.candidates.lookup (owner, candidate.2) =
                  .openable ⟨payload, value⟩
                simpa only [← owned, Prod.mk.eta] using leftFixed
              have shape := (normal_opening_of_owned_evidence timeouts) leaks owner
                (original.logs owner) (original.observe app owner) material event candidate
                ⟨payload, value⟩ materialNormal packet certified owned localFixed
              have known : ReactiveApplication.ResponseMenu.knownPackets (original.logs owner)
                  (original.observe app owner) = original.network.known owner :=
                (app.known_from_recall original owner count.1).symm
              rw [known] at shape
              subst material
              let openingMaterial :=
                (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
                  owner (app.observePlayer original.application owner)
                  (original.network.known owner)
              let openingResponse : app.Action := ⟨some openingMaterial⟩
              let nextMemory := memory.record timeouts leaks
                (memory.shadow.inputView timeouts leaks (repaired.observe app owner))
                openingResponse
              obtain ⟨afterFrame, targetTrace, targetRecord⟩ := frame.normalized_opening_trace
                (timeouts := timeouts)
                remaining prior imagePrior records event candidate ⟨payload, value⟩ owned leftFixed
                rightFixed available
              have nonbinding : ∀ supplied, openingResponse.transmission = some supplied →
                  ∀ named handle, supplied.call.packet ≠ .commitment named handle := by
                intro supplied same named handle impossible
                cases Option.some.inj same
                change Payload.opening event candidate ⟨payload, value⟩ = _ at impossible
                cases impossible
              exact ⟨openingResponse, nextMemory, afterFrame,
                (submittedRecords.respond owner openingResponse openingResponse
                  (Or.inr nonbinding)).record _ openingResponse,
                onlyBindings, targetTrace, targetRecord⟩

end DirectedBindingFrame

end Vegas

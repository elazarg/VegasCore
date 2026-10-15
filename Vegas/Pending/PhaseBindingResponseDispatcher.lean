/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSubmittedRawRepair
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.ReactiveFiniteCompiler

/-! # Every actual response extends the directed phased repair invariants -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Only the repaired owner's binding responses change. The replacement keeps
the original prepared slot, uses canonical absent evidence, and replaces an
unusable preparation by a value of the binding type. -/
def responseImage (repairOwner actor : Player)
    (response : (phaseApplication runtime leaks).Action) :
    (phaseApplication runtime leaks).Action :=
  if actor = repairOwner then
    match response.transmission with
    | some ⟨⟨.commitment event candidate, preparation⟩, _⟩ =>
        match nodeView graph event with
        | .bind _ payload _ _ =>
            ⟨some ⟨⟨.commitment event candidate,
              match preparation.bind (fun raw => raw.as? payload) with
              | none => some ⟨payload, L.someValue payload⟩
              | some _ => preparation⟩, .none⟩⟩
        | .sample .. | .resolve .. => response
    | _ => response
  else response

/-- All actual callback forms have a legal image with exact private memory.
Readiness, fresh slots and delayed binding records come from genuine histories;
no image response support or assumed successful original binding is supplied. -/
theorem response_records (frame : Frame runtime leaks memory owner original repaired)
    (recorded : memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
      (execution runtime leaks original) (execution runtime leaks repaired))
    (onlyBindings : memory.shadow.OwnBindings owner)
    (bounds : MessageBounds graph) (covered : bounds.CoversOutputValues)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (actor : Player)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some actor, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some actor, repaired⟩))
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
      (original.recall actor) (original.observe (phaseApplication runtime leaks) actor)) :
    ∃ (target : (phaseApplication runtime leaks).Action)
      (remembered : BindingMemory runtime (nativeLeaks (graph := graph))),
      target ∈ PhaseCount.onePacketActions runtime leaks bounds actor (repaired.recall actor)
          (repaired.observe (phaseApplication runtime leaks) actor) ∧
        Frame runtime leaks remembered owner
          (original.respond (phaseApplication runtime leaks) actor response)
          (repaired.respond (phaseApplication runtime leaks) actor target) ∧
        remembered.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
          (execution runtime leaks
            (original.respond (phaseApplication runtime leaks) actor response))
          (execution runtime leaks
            (repaired.respond (phaseApplication runtime leaks) actor target)) ∧
        remembered.shadow.OwnBindings owner ∧
        target = responseImage (runtime := runtime) (leaks := leaks) owner actor response := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler left
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler right
  have countLeft := PhaseCount.countRecall_history runtime leaks rawLeft
  have countRight := PhaseCount.countRecall_history runtime leaks rawRight
  by_cases foreign : actor ≠ owner
  · have paired := frame.foreign_response bounds countLeft countRight actor foreign response member
    exact ⟨response, memory, paired.1, paired.2,
      submittedRecords_respond recorded bounds actor response response member paired.1
        (Or.inl foreign), onlyBindings, by
        simp only [responseImage, foreign, ↓reduceIte]⟩
  · have actorEq : actor = owner := not_ne_iff.mp foreign
    subst actor
    rcases response with ⟨transmission⟩
    cases transmission with
    | none =>
        have legal := PhaseCount.silence_onePacket runtime leaks bounds owner
          (repaired.recall owner) (repaired.observe app owner)
        let view := memory.shadow.inputView runtime (nativeLeaks (graph := graph))
          ((execution runtime leaks repaired).observe nativeApp owner)
        have retained := submittedRecords_respond recorded bounds owner ⟨none⟩ ⟨none⟩ member legal
          (Or.inr (by intro material impossible; cases impossible))
        exact ⟨⟨none⟩, memory.record runtime (nativeLeaks (graph := graph)) view ⟨none⟩,
          legal, frame.silence, retained.record view ⟨none⟩, onlyBindings, by
            simp only [responseImage, ↓reduceIte]⟩
    | some material =>
        obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks
          bounds plan inputs horizon scheduler remaining owner original left frame.clearOriginal
            material member
        have named := PhaseCount.onePacket_event_of_request runtime leaks bounds plan ordered inputs
          horizon scheduler remaining owner original left coordinate request material member
        have allowed : PhaseCount.permits (app.outputs (original.recall owner))
            (PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
              (original.observe app owner) material) = true := by
          rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2
            with impossible | ⟨supplied, same, allowed⟩
          · cases impossible
          · cases Option.some.inj same
            exact allowed
        have correct := ((PhaseCount.permits_eq_true_iff _ _).mp allowed).2.1
        have actualCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks owner
            (original.recall owner) (original.observe app owner) material)).payload.call =
              material.call.packet := PhaseCount.maskPacket_call _ _
        unfold CountCallCorrect at correct
        rw [actualCall] at correct
        rcases material with ⟨⟨packet, preparation⟩, evidence⟩
        cases packet with
        | malformed raw => cases correct
        | commitment event candidate =>
            obtain ⟨bindingOwned, _, candidateOwned, ⟨serial, slot⟩, _⟩ := correct
            change candidate.1 = owner at candidateOwned
            have candidateEq : candidate = (owner, .prepared serial) := Prod.ext candidateOwned slot
            subst candidate
            have eventEq : coordinate.event = event := Option.some.inj named.symm
            have requestEvent := request
            change original.application.SeedRequest owner
              ⟨coordinate.attempt, coordinate.event⟩ at requestEvent
            rw [request.1, eventEq] at requestEvent
            cases node : nodeView graph event with
            | sample payload law outputEq codeEq =>
                simp only [bindingOwnedBy, outputEq] at bindingOwned
                cases bindingOwned
            | resolve actor payload binding checks outputEq codeEq =>
                simp only [bindingOwnedBy, outputEq] at bindingOwned
                cases bindingOwned
            | bind actor payload outputEq codeEq =>
                change bindingOwnedBy graph owner event = true at bindingOwned
                have actorEq : actor = owner := by
                  simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq] using bindingOwned
                subst actor
                have fresh := PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs
                  horizon scheduler left owner event serial preparation evidence member
                have bounded : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values := by
                  have values := covered event
                  rw [outputEq] at values
                  exact values _
                have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon
                  scheduler rawRight
                have paired := frame.raw_binding_response_records recorded bounds plan inputs
                  horizon
                  scheduler remaining left right stored event payload outputEq codeEq node serial
                    preparation evidence fresh requestEvent.2.2.1 bounded member
                refine ⟨_, _, paired.1, paired.2.1, paired.2.2, ?_, ?_⟩
                · exact memory.repairResponse_ownBindings runtime
                    (nativeLeaks (graph := graph)) owner onlyBindings _ _
                · simp only [responseImage, ↓reduceIte, node]
                  rfl
        | opening event candidate raw =>
            have eventEq : coordinate.event = event := Option.some.inj named.symm
            have requestEvent := request
            change original.application.SeedRequest owner
              ⟨coordinate.attempt, coordinate.event⟩ at requestEvent
            rw [request.1, eventEq] at requestEvent
            cases node : nodeView graph event with
            | bind actor payload outputEq codeEq => simp only [node, and_false] at correct
            | sample payload law outputEq codeEq => simp only [node, and_false] at correct
            | resolve actor payload binding checks outputEq codeEq =>
                simp only [node] at correct
                have actorEq : actor = owner := correct.2.1.symm
                subst actor
                let source : app.Action :=
                  ⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩
                have paired := frame.opening_response bounds plan inputs horizon scheduler remaining
                  left right event candidate raw preparation evidence member requestEvent payload
                    binding checks outputEq codeEq node
                let view := memory.shadow.inputView runtime (nativeLeaks (graph := graph))
                  ((execution runtime leaks repaired).observe nativeApp owner)
                have retained := submittedRecords_respond recorded bounds owner source source member
                  paired.1 (Or.inr (by
                    intro material same event candidate
                    cases Option.some.inj same
                    intro impossible
                    cases impossible))
                exact ⟨source, memory.record runtime (nativeLeaks (graph := graph)) view
                  (action runtime leaks source), paired.1, paired.2,
                    retained.record view (action runtime leaks source), onlyBindings, by
                      simp only [responseImage, source, ↓reduceIte]⟩

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

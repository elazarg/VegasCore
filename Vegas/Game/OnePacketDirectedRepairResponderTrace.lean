/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketDirectedRepairResponse
import Vegas.Game.OnePacketDirectedRepairTrace
import Vegas.Game.OnePacketPendingLumping

/-! # Actual responder traces through directed binding repair

Every response leaves the source configuration and public contract view fixed,
so the value currently delivered at a reveal is unchanged. Equal complete
operational records already imply equality of those delivered values. A
concrete response-frame constructor and an admitted repaired action therefore
extend an actual repaired history with the same entire operational record.
Silence and foreign responses discharge both conditions directly.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Responses can prepare private candidates and emit packets, but they cannot
change the source value currently delivered by an opening. -/
theorem deliveredValue_respond (execution : (application setup leaks).Execution)
    (actor observer : Player) (response : (application setup leaks).Action) :
    deliveredValue setup leaks observer
        ((execution.respond (application setup leaks) actor response).observe
          (application setup leaks) observer) =
      deliveredValue setup leaks observer
        (execution.observe (application setup leaks) observer) := by
  obtain ⟨config, publicView⟩ := (runtime setup).reactive_respond_application leaks execution actor
    response
  apply deliveredValue_congr observer
  · change
      (execution.respond (application setup leaks) actor response).application.publicView.ownTurn?
        observer = execution.application.publicView.ownTurn? observer
    rw [publicView]
  · change ((graph setup).playerObserve observer
      (execution.respond (application setup leaks) actor response).application.config).store =
        ((graph setup).playerObserve observer execution.application.config).store
    rw [config]

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Equality of complete operational records implies equality of the currently
delivered value for every player, without an additional exposure hypothesis. -/
theorem deliveredValue_eq_of_operationalRecord
    {first second : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some first))
    (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some second))
    (records : operationalRecord setup leaks bounds horizon scheduler prior =
      operationalRecord setup leaks bounds horizon scheduler imagePrior)
    (who : Player) :
    deliveredValue setup leaks who (first.execution.observe (application setup leaks) who) =
      deliveredValue setup leaks who (second.execution.observe (application setup leaks) who) := by
  obtain ⟨leftRest, left⟩ := operationalRecord_head prior
  obtain ⟨rightRest, right⟩ := operationalRecord_head imagePrior
  rw [left, right] at records
  have current := (List.cons.inj records).1
  have observed := congrArg (fun state : Option (OperationalState setup leaks) =>
    state.bind fun operational => (operational.keys who).map LateKey.delivered) current
  simpa only [operationalState, Option.bind_some, lateKey, Option.map_some,
    Option.some.injEq] using observed

namespace DirectedBindingFrame

variable {memory nextMemory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

/-- Lift a concrete paired responder operation to an actual repaired trace.
The complete record determines the pre-response delivered value, and actual
response invariance carries it to the resulting binding frame. -/
theorem responder_trace (frame : DirectedBindingFrame memory owner original repaired)
    (remaining : Nat) (actor : Player)
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some actor, original⟩))
    (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some actor, repaired⟩))
    (records : operationalRecord setup leaks bounds horizon scheduler prior =
      operationalRecord setup leaks bounds horizon scheduler imagePrior)
    (left right : (application setup leaks).Action)
    (available : right ∈ bounds.onePacketActions (runtime setup) leaks actor
      (repaired.recall actor) (repaired.observe (application setup leaks) actor))
    (after : BindingMemory.Frame (runtime setup) leaks nextMemory owner
      (original.respond (application setup leaks) actor left)
      (repaired.respond (application setup leaks) actor right)) :
    DirectedBindingFrame nextMemory owner
        (original.respond (application setup leaks) actor left)
        (repaired.respond (application setup leaks) actor right) ∧
      ∃ trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
          (some ⟨remaining, none, repaired.respond (application setup leaks) actor right⟩),
        operationalRecord setup leaks bounds horizon scheduler trace =
          operationalState setup leaks
              (some ⟨remaining, none, original.respond (application setup leaks) actor left⟩) ::
            operationalRecord setup leaks bounds horizon scheduler prior := by
  have directed : DirectedBindingFrame nextMemory owner
      (original.respond (application setup leaks) actor left)
      (repaired.respond (application setup leaks) actor right) := by
    by_cases same : actor = owner
    · subst actor
      exact frame.respond left right after
    · refine ⟨after, ?_⟩
      rw [(application setup leaks).respond_recall_other original actor owner (Ne.symm same),
        (application setup leaks).respond_recall_other repaired actor owner (Ne.symm same)]
      exact frame.recalled
  refine ⟨directed, ?_⟩
  let joint := fun player => if player = actor then some right else none
  have legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
      (some ⟨remaining, some actor, repaired⟩) joint := by
    constructor
    · simp [onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
        ReactiveApplication.terminal]
    · intro player
      by_cases same : player = actor
      · subst player
        simpa [joint, onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, ReactiveApplication.ResponseMenu.available,
          MessageBounds.onePacketMenu] using available
      · simp [joint, onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, same, Ne.symm same]
  have realized : some ⟨remaining, none,
      repaired.respond (application setup leaks) actor right⟩ ∈
      ((onePacketProtocol setup leaks bounds horizon scheduler).step
        (some ⟨remaining, some actor, repaired⟩) ⟨joint, legal⟩).support := by
    change _ ∈ (PMF.pure _).support
    simp only [joint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]
  refine ⟨imagePrior.extend joint legal realized, ?_⟩
  have delivered := deliveredValue_eq_of_operationalRecord prior imagePrior records owner
  have afterDelivered : deliveredValue setup leaks owner
        ((original.respond (application setup leaks) actor left).observe
          (application setup leaks) owner) =
      deliveredValue setup leaks owner
        ((repaired.respond (application setup leaks) actor right).observe
          (application setup leaks) owner) := by
    rw [deliveredValue_respond, deliveredValue_respond]
    exact delivered
  have stateEq := after.operationalState directed.recalled afterDelivered remaining none
  change operationalState setup leaks
      (some ⟨remaining, none, repaired.respond (application setup leaks) actor right⟩) ::
        operationalRecord setup leaks bounds horizon scheduler imagePrior = _
  rw [← records, ← stateEq]

/-- Every foreign response transports unchanged through an actual repaired
history. Its legality follows from equality of the responder's full input. -/
theorem foreign_response_trace (frame : DirectedBindingFrame memory owner original repaired)
    (remaining : Nat) (actor : Player) (foreign : actor ≠ owner)
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some actor, original⟩))
    (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some actor, repaired⟩))
    (records : operationalRecord setup leaks bounds horizon scheduler prior =
      operationalRecord setup leaks bounds horizon scheduler imagePrior)
    (response : (application setup leaks).Action)
    (available : response ∈ bounds.onePacketActions (runtime setup) leaks actor
      (original.recall actor) (original.observe (application setup leaks) actor)) :
    DirectedBindingFrame memory owner
        (original.respond (application setup leaks) actor response)
        (repaired.respond (application setup leaks) actor response) ∧
      ∃ trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
          (some ⟨remaining, none, repaired.respond (application setup leaks) actor response⟩),
        operationalRecord setup leaks bounds horizon scheduler trace =
          operationalState setup leaks
              (some ⟨remaining, none, original.respond (application setup leaks) actor response⟩) ::
            operationalRecord setup leaks bounds horizon scheduler prior := by
  apply frame.responder_trace remaining actor prior imagePrior records response response
  · rw [← frame.recall actor foreign, ← frame.toFrame.foreign_observed actor foreign]
    exact available
  · exact frame.toFrame.foreign_response actor foreign response

/-- Silence is an actual legal unchanged owner response, preserving the repair
frame and the complete operational record while recording the original input. -/
theorem silence_trace (frame : DirectedBindingFrame memory owner original repaired)
    (remaining : Nat)
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, original⟩))
    (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, repaired⟩))
    (records : operationalRecord setup leaks bounds horizon scheduler prior =
      operationalRecord setup leaks bounds horizon scheduler imagePrior) :
    let response : (application setup leaks).Action := ⟨none⟩
    let remembered := memory.record (runtime setup) leaks
      (memory.shadow.inputView (runtime setup) leaks
        (repaired.observe (application setup leaks) owner)) response
    DirectedBindingFrame remembered owner
        (original.respond (application setup leaks) owner response)
        (repaired.respond (application setup leaks) owner response) ∧
      ∃ trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
          (some ⟨remaining, none, repaired.respond (application setup leaks) owner response⟩),
        operationalRecord setup leaks bounds horizon scheduler trace =
          operationalState setup leaks
              (some ⟨remaining, none, original.respond (application setup leaks) owner response⟩) ::
            operationalRecord setup leaks bounds horizon scheduler prior := by
  intro response remembered
  exact frame.responder_trace remaining owner prior imagePrior records response response
    (bounds.silence_onePacket (runtime setup) leaks owner _ _)
    (frame.toFrame.transport_response response (fun _ impossible => by cases impossible))

end DirectedBindingFrame

end Vegas

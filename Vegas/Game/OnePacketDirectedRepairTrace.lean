/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairSteps
import Vegas.Game.OnePacketDirectedRepairMenu
import Vegas.Pending.ReactiveOnePacketFreshness

/-! # Actual one-packet traces through directed binding repair

A legal raw binding response extends both actual histories. Its fresh candidate
is derived from the original history's count permissions, and the owner-local
repair produces a legal response on the second history. Their complete
operational records remain equal through the response.
-/

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

private theorem exists_response_trace_with_record
    (remaining : Nat) (execution : (application setup timeouts leaks).Execution) (who : Player)
    (response : (application setup timeouts leaks).Action)
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (execution.logs who) (execution.observe (application setup timeouts leaks) who)) :
    ∃ trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond (application setup timeouts leaks) who response⟩),
      operationalRecord setup timeouts leaks bounds horizon scheduler trace =
        operationalState setup timeouts leaks
            (some ⟨remaining, none, execution.respond (application setup timeouts leaks) who
              response⟩) ::
          operationalRecord setup timeouts leaks bounds horizon scheduler prior := by
  let joint := fun actor => if actor = who then some response else none
  have legal : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Legal
      (some ⟨remaining, some who, execution⟩) joint := by
    constructor
    · simp [onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
        ReactiveApplication.terminal]
    · intro actor
      by_cases same : actor = who
      · subst actor
        simpa [joint, onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, ReactiveApplication.ResponseMenu.available,
          MessageBounds.onePacketMenu] using member
      · simp [joint, onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, same, Ne.symm same]
  have realized : some ⟨remaining, none,
      execution.respond (application setup timeouts leaks) who response⟩ ∈
      ((onePacketProtocol setup timeouts leaks bounds horizon scheduler).step
        (some ⟨remaining, some who, execution⟩) ⟨joint, legal⟩).support := by
    change _ ∈ (PMF.pure _).support
    simp only [joint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]
  exact ⟨prior.extend joint legal realized, rfl⟩

namespace DirectedBindingFrame

variable {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : (application setup timeouts leaks).Execution}

/-- An actual admitted raw binding extends a directed repair to an actual
admitted history with the same entire operational record. Freshness and legal
repair are consequences of the histories and the finite value bounds. -/
theorem binding_trace (frame : DirectedBindingFrame (timeouts := timeouts) memory owner original
  repaired)
    (remaining : Nat)
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, original⟩))
    (imagePrior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, repaired⟩))
    (records : operationalRecord setup timeouts leaks bounds horizon scheduler prior =
      operationalRecord setup timeouts leaks bounds horizon scheduler imagePrior)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (ready : original.application.config.cut.Ready event)
    (turn : original.application.publicView.ownTurn? owner = some event)
    (covered : bounds.CoversOutputValues)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩ :
      (application setup timeouts leaks).Action) ∈ bounds.onePacketActions timeouts leaks owner
        (original.logs owner) (original.observe (application setup timeouts leaks) owner)) :
    let app := application setup timeouts leaks
    let view := repaired.observe app owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let change := memory.repairResponse timeouts leaks owner view response
    let remembered : BindingMemory timeouts leaks :=
      ⟨change.2, memory.responses ++ [(memory.shadow.inputView timeouts leaks view,
        response)]⟩
    DirectedBindingFrame (timeouts := timeouts) remembered owner (original.respond app owner
      response)
        (repaired.respond app owner change.1) ∧
      ∃ trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
          (some ⟨remaining, none, repaired.respond app owner change.1⟩),
        operationalRecord setup timeouts leaks bounds horizon scheduler trace =
          operationalState setup timeouts leaks
              (some ⟨remaining, none, original.respond app owner response⟩) ::
            operationalRecord setup timeouts leaks bounds horizon scheduler prior := by
  intro app view response change remembered
  have initializedPrior := prior
  change ((bounds.onePacketMenu timeouts leaks).protocol
    (serviceInitialLaw setup .sequential) horizon scheduler).Trace _ at initializedPrior
  rw [serviceInitialLaw_eq_inputs] at initializedPrior
  have fresh := bounds.onePacket_binding_fresh timeouts leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler initializedPrior owner event serial
    opening member
  have originalCount := (countRecall_history timeouts) leaks
    ((bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      prior)
  have repairedCount := (countRecall_history timeouts) leaks
    ((bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      imagePrior)
  have legalRepair := frame.toFrame.repairResponse_onePacket (timeouts :=
    timeouts) bounds frame.recalled originalCount
    repairedCount event payload outputEq codeEq node serial opening fresh covered member
  have repairedFrame := frame.binding_submission event payload outputEq
    codeEq node serial
    opening fresh ready
  change DirectedBindingFrame (timeouts := timeouts) remembered owner (original.respond app owner
    response)
    (repaired.respond app owner change.1) at repairedFrame
  refine ⟨repairedFrame, ?_⟩
  obtain ⟨trace, record⟩ := exists_response_trace_with_record (timeouts := timeouts) remaining
    repaired owner change.1
    imagePrior legalRepair
  refine ⟨trace, ?_⟩
  have afterPublic := ((reactive_respond_application timeouts) leaks original owner
    response).2
  have afterTurn : (original.respond app owner response).application.publicView.ownTurn? owner =
      some event := by
    rw [afterPublic]
    exact turn
  have bothDelivered : deliveredValue setup timeouts leaks owner
        ((original.respond app owner response).observe app owner) =
      deliveredValue setup timeouts leaks owner
        ((repaired.respond app owner change.1).observe app owner) := by
    have repairedTurn : (repaired.respond app owner change.1).application.publicView.ownTurn?
        owner = some event := by
      rw [← repairedFrame.toFrame.publicView]
      exact afterTurn
    have firstTurn :
        ((original.respond app owner response).observe app owner).application.publicView.ownTurn?
          owner = some event := afterTurn
    have secondTurn :
        ((repaired.respond app owner change.1).observe app owner).application.publicView.ownTurn?
          owner = some event := repairedTurn
    unfold deliveredValue
    rw [firstTurn, secondTurn]
    simp only [node]
  have stateEq := repairedFrame.toFrame.operationalState
    repairedFrame.recalled bothDelivered
    remaining none
  rw [record, ← stateEq, ← records]

end DirectedBindingFrame

end Vegas

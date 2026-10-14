/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketForeignBindingRegularity
import Vegas.Game.OnePacketDirectedRepairSteps
import Vegas.Pending.ReactiveBindingAcceptedRecords

/-! # Finite composition of actual hidden-binding repairs

Single-owner repairs preserve all foreign full decision inputs and every
successful binding. Iterating their actual traces therefore repairs any finite
set of owners while retaining the excluded players' full information and the
common operational record. The single-owner construction remains explicit.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem bindingRefines_trans {Field : Type}
    {layout : Field → EventGraph.EventField Player L}
    {first middle last : EventGraph.Store layout}
    (left : first.BindingRefines middle) (right : middle.BindingRefines last) :
    first.BindingRefines last := by
  have compose (kind : EventGraph.EventField Player L) (first middle last : Option kind.Value)
      (left : kind.BindingRefines first middle) (right : kind.BindingRefines middle last) :
      kind.BindingRefines first last := by
    cases kind with
    | binding owner payload => exact fun value stored => right value (left value stored)
    | publicData | privateInput | publication => trivial
  exact fun field => compose _ _ _ _ (left field) (right field)

omit [Fintype Player] in
private theorem outputSucceeded_of_bindingRefines
    {first last : EventGraph.Store (graph setup).layout}
    (preserved : first.BindingRefines last) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    (layoutEq : (graph setup).outputLayout event = .binding owner payload)
    (successful : OutputSucceeded first event) : OutputSucceeded last event := by
  obtain ⟨value, stored, notFailed⟩ := successful
  have transport : ∀ (kind : EventGraph.EventField Player L)
      (_ : kind = .binding owner payload) (first last : Option kind.Value),
      kind.BindingRefines first last → ∀ value, first = some value → ¬ kind.IsFailure value →
        ∃ next, last = some next ∧ ¬ kind.IsFailure next := by
    rintro _ rfl first last preserved value stored notFailed
    cases value with
    | failure => exact (notFailed rfl).elim
    | success value => exact ⟨.success value, preserved value stored, fun failed => by cases failed⟩
  exact transport _ layoutEq _ _ (preserved (.inr event)) value stored notFailed

omit [Fintype Player] in
private theorem completed_iff_of_frame
    {memory : BindingMemory (runtime setup) leaks} {owner : Player}
    {original repaired : (application setup leaks).Execution}
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (event : (graph setup).EventId) :
    event ∈ original.application.config.cut.completed ↔
      event ∈ repaired.application.config.cut.completed := by
  have order : original.application.config.history.map EventGraph.Completion.event =
      repaired.application.config.history.map EventGraph.Completion.event :=
    congrArg (fun view : PublicView (graph setup) => view.observation.completionOrder)
      frame.publicView
  constructor
  · intro completed
    apply (repaired.application.config.history_exact event).mp
    rw [← order]
    exact (original.application.config.history_exact event).mpr completed
  · intro completed
    apply (original.application.config.history_exact event).mp
    rw [order]
    exact (repaired.application.config.history_exact event).mpr completed

/-- An actual repair with recorded submissions succeeds at every completed
binding owned by its repaired player when the focal public record rules out
missed foreign bindings. -/
theorem directedRepair_completed_outputs_succeeded
    {focal owner : Player} (foreign : owner ≠ focal)
    {original repaired : (application setup leaks).Control}
    (first : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some original))
    (last : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired))
    {memory : BindingMemory (runtime setup) leaks}
    (frame : DirectedBindingFrame memory owner original.execution repaired.execution)
    (recorded : memory.RecordsSubmittedBindings (runtime setup) leaks owner
      original.execution repaired.execution)
    (record : PublicRecord setup focal original)
    (event : (graph setup).EventId) (payload : L.Ty)
    (layoutEq : (graph setup).outputLayout event = .binding owner payload)
    (completed : event ∈ repaired.execution.application.config.cut.completed) :
    OutputSucceeded repaired.execution.application.config.store event := by
  have rawFirst := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler first
  have rawLast := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler last
  have signed := signedCommitments_history (runtime setup) leaks (initialLaw setup)
    (fun state member => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
      exact ⟨_, rfl⟩) horizon scheduler rawFirst
  have count := (runtime setup).countRecall_history leaks rawFirst
  have valid : repaired.execution.application.BindingInvariant :=
    ((runtime setup).reactiveBindingInvariant leaks).history (initialLaw setup) horizon
      scheduler (fun state member => by
        obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
        exact State.initial_bindingInvariant _) rawLast
  have acceptedEq : repaired.execution.application.accepted =
      original.execution.application.accepted :=
    (congrArg PublicView.accepted frame.toFrame.publicView).symm
  apply recorded.accepted_output_succeeded signed count valid acceptedEq event payload layoutEq
  rw [acceptedEq]
  exact record.1 event owner payload layoutEq foreign
    ((completed_iff_of_frame frame.toFrame event).mpr completed)

private theorem infoOf_eq_of_frame
    {focal owner : Player} (foreign : focal ≠ owner)
    {original repaired : (application setup leaks).Control}
    (first : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some original))
    (last : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired))
    {memory : BindingMemory (runtime setup) leaks}
    (frame : DirectedBindingFrame memory owner original.execution repaired.execution)
    (actor : repaired.actor = original.actor) :
    (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal last =
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal first := by
  rw [onePacket_infoOf, onePacket_infoOf]
  simp only [ReactiveApplication.observe, actor]
  rw [frame.toFrame.decisionInput foreign]

/-- Finite single-owner actual repairs compose, preserving the complete final
information of every excluded player and every previously successful binding.
The callback constructs an actual trace and its submitted-binding record. -/
theorem exists_bindingRepairs_for_owners
    (focal : Player)
    (info : (onePacketInformation setup leaks bounds horizon scheduler).InfoState focal)
    (original : (application setup leaks).Control)
    (first : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some original))
    (seen : (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal first = info)
    (record : ∀ current
      (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current)),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal trace = info →
        PublicRecord setup focal current)
    (owners : Finset Player) (focalNotIn : focal ∉ owners)
    (repair : ∀ owner ∈ owners, ∀ current
      (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current)),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal trace = info →
      ∃ repaired : (application setup leaks).Control,
        ∃ image : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired),
        ∃ memory : BindingMemory (runtime setup) leaks,
          repaired.remaining = current.remaining ∧ repaired.actor = current.actor ∧
          DirectedBindingFrame memory owner current.execution repaired.execution ∧
          operationalRecord setup leaks bounds horizon scheduler trace =
            operationalRecord setup leaks bounds horizon scheduler image ∧
          memory.RecordsSubmittedBindings (runtime setup) leaks owner
            current.execution repaired.execution) :
    ∃ repaired : (application setup leaks).Control,
      ∃ image : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired),
        (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal image = info ∧
        repaired.remaining = original.remaining ∧ repaired.actor = original.actor ∧
        operationalRecord setup leaks bounds horizon scheduler first =
          operationalRecord setup leaks bounds horizon scheduler image ∧
        (∀ player, player ∉ owners →
          (original.execution.recall player,
            original.execution.observe (application setup leaks) player) =
          (repaired.execution.recall player,
            repaired.execution.observe (application setup leaks) player)) ∧
        original.execution.application.config.store.BindingRefines
          repaired.execution.application.config.store ∧
        ∀ owner ∈ owners, ∀ event payload,
          (graph setup).outputLayout event = .binding owner payload →
          event ∈ repaired.execution.application.config.cut.completed →
          OutputSucceeded repaired.execution.application.config.store event := by
  classical
  revert focalNotIn repair
  induction owners using Finset.induction_on with
  | empty =>
      intro _ _
      exact ⟨original, first, seen, rfl, rfl, rfl, fun _ _ => rfl,
        EventGraph.Store.BindingRefines.refl _, by simp⟩
  | @insert owner owners fresh ih =>
      intro focalNotIn repair
      have focalNotInPrior : focal ∉ owners := fun member =>
        focalNotIn (Finset.mem_insert_of_mem member)
      obtain ⟨middle, middleTrace, middleSeen, middleRemaining, middleActor, middleRecord,
        middleOutside, middleRefined, middleSuccessful⟩ := ih focalNotInPrior
          (fun player member => repair player (Finset.mem_insert_of_mem member))
      obtain ⟨repaired, image, memory, remaining, actor, frame, sameRecord, recorded⟩ :=
        repair owner (Finset.mem_insert_self owner owners) middle middleTrace middleSeen
      have foreign : owner ≠ focal := by
        intro same
        subst owner
        exact focalNotIn (Finset.mem_insert_self focal owners)
      refine ⟨repaired, image, (infoOf_eq_of_frame foreign.symm middleTrace image frame actor).trans
        middleSeen, remaining.trans middleRemaining, actor.trans middleActor,
        middleRecord.trans sameRecord, ?_, bindingRefines_trans middleRefined frame.successful, ?_⟩
      · intro player excluded
        have before : player ∉ owners := fun member =>
          excluded (Finset.mem_insert_of_mem member)
        have other : player ≠ owner := by
          intro same
          subst player
          exact excluded (Finset.mem_insert_self owner owners)
        exact (middleOutside player before).trans (frame.toFrame.decisionInput other)
      · intro player member event payload layoutEq completed
        rcases Finset.mem_insert.mp member with same | prior
        · subst player
          exact directedRepair_completed_outputs_succeeded foreign middleTrace image frame
            recorded (record middle middleTrace middleSeen) event payload layoutEq completed
        · exact outputSucceeded_of_bindingRefines frame.successful event layoutEq
            (middleSuccessful player prior event payload layoutEq
              ((completed_iff_of_frame frame.toFrame event).mpr completed))

end Vegas

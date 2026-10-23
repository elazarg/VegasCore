/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOpeningService
import Vegas.Pending.PhaseLatestBindingHistory
import Vegas.Pending.PhasePacketEvidence
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseInputAddress
import Vegas.Pending.PhaseInputBindings
import Vegas.Pending.PhaseBindingInvariant

/-! # Physical acceptance of surviving counted openings

The accepted handle is derived from the latest physical signed binding, not
supplied as an acceptance premise. Completed omitted bindings belong to excluded
owners; authentic candidate certificates remain sound across every rollback.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
private theorem binding_before_reveal (state : PhaseRuntimeState graph)
    (frontier : state.Frontier) (phase : RuntimePhase graph)
    (head : phase ∈ state.phases.head?) (event : graph.EventId) (inside : event ∈ phase.events)
    (payload : L.Ty) (publication : graph.outputLayout event = .publication payload)
    (producer : graph.EventId) (owner : Player) (ty : L.Ty)
    (binding : graph.outputLayout producer = .binding owner ty)
    (completed : producer ∈ state.current.native.config.cut.completed) :
    producer.val < state.attempt.phase := by
  cases phases : state.phases with
  | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at head
  | cons first rest =>
      have same : first = phase := by
        simpa only [phases, List.head?_cons, Option.mem_some_iff] using head
      subst first
      have positioned := frontier.positioned
      rw [phases] at positioned
      have upper := positioned.2.2 producer completed
      have bounds := (phase.mem_events event).mp inside
      have before : producer.val < phase.low := by
        by_contra contrary
        have lower : phase.low ≤ producer.val := Nat.le_of_not_gt contrary
        have firstKind := phase.fields event bounds.1 bounds.2
        have secondKind := phase.fields producer lower upper
        cases kind : phase.kind with
        | commitment =>
            rw [kind] at firstKind
            obtain ⟨author, valueType, shape⟩ := firstKind
            cases publication.symm.trans shape
        | sample =>
            rw [kind] at firstKind
            obtain ⟨valueType, shape⟩ := firstKind
            cases publication.symm.trans shape
        | reveal =>
            rw [kind] at secondKind
            obtain ⟨valueType, shape⟩ := secondKind
            cases binding.symm.trans shape
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some] using before

theorem accepted_of_latest (execution : (app).Execution)
    (physical : PhysicalBindings runtime leaks execution)
    (bindingValid : execution.application.current.native.BindingInvariant)
    (covered : execution.application.current.FailureCoverage)
    (initial : ∀ input owner payload, graph.inputLayout input = .binding owner payload →
      execution.application.current.native.accepted (.inl input) = some (owner, .initial input))
    (unique : execution.network.UniqueIds)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (opening : message.payload.packet.call = .opening event candidate raw)
    (owner : Player) (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (_node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : execution.application.current.native.config.cut.Ready event)
    (request : execution.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (sender : message.sender = owner)
    (latest : LatestSignedBinding (Earlier execution.network.inputs message)
      message.sender candidate binding.field) :
    execution.application.current.native.accepted binding.field = some candidate := by
  have available : (execution.application.current.native.config.store binding.field).isSome =
      true := by
    apply execution.application.current.native.config.read_available ready
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact Finset.mem_insert_self _ _
  cases field : binding.field with
  | inl input =>
      rw [field] at latest
      change candidate = (message.sender, .initial input) at latest
      rw [latest, sender]
      apply initial input owner payload
      have kind := binding.layout_eq
      rw [field] at kind
      exact kind
  | inr producer =>
      have producerLayout : graph.outputLayout producer = .binding owner payload := by
        have kind := binding.layout_eq
        rw [field] at kind
        exact kind
      have completed : producer ∈ execution.application.current.native.config.cut.completed := by
        rw [field] at available
        exact (execution.application.current.native.config.output_available producer).mp available
      obtain ⟨acceptedHandle, associated⟩ : ∃ acceptedHandle,
          execution.application.current.native.accepted (.inr producer) = some acceptedHandle := by
        cases table : execution.application.current.native.accepted (.inr producer) with
        | some handle => exact ⟨handle, rfl⟩
        | none =>
            have missed := (execution.application.current.native.publicView_missedBinding producer
              owner payload producerLayout).mpr ⟨completed, table⟩
            have excluded := covered.covered producer owner
              (EventGraph.actor?_of_outputLayout_binding graph producerLayout) (Or.inl missed)
            exact ((sender ▸ request.2.2.2.2) excluded).elim
      have acceptedOwner : acceptedHandle.1 = owner := by
        obtain ⟨ty, typed⟩ := bindingValid.accepted_typed (.inr producer) acceptedHandle associated
        exact (EventField.binding.inj (producerLayout.symm.trans typed)).1.symm
      obtain ⟨actual, actualInput, actualSender, actualCall, actualLatest⟩ :=
        physical.active producer acceptedHandle associated
      have actualOwner : actual.sender = message.sender :=
        actualSender.trans (acceptedOwner.trans sender.symm)
      obtain ⟨phase, head, inside⟩ := request.2.1
      have earlierPhase := binding_before_reveal execution.application physical.record.frontier
        phase head event inside payload outputEq producer owner payload producerLayout completed
      have current : message.payload.attempt = execution.application.attempt := request.1
      have actualEarlier : actual.id.2 < message.id.2 := by
        rcases lt_trichotomy actual.id.2 message.id.2 with before | same | after
        · exact before
        · have identified := (unique.inputs message member).inputs actual actualInput
            (Prod.ext actualOwner same)
          rw [identified, opening] at actualCall
          cases actualCall
        · have order := physical.namespaces.monotone message member actual actualInput
            actualOwner.symm after
          have validToken := ((permits_eq_true_iff _ _).mp
            (physical.clean.2 actual actualInput)).1
          have lower := issued_address_lower runtime leaks execution actual
            (physical.origins.inputs actual actualInput) producer validToken
            (by rw [actualCall]; rfl)
          rw [← current] at earlierPhase
          omega
      have clean : ∀ packet ∈ execution.network.inputs, Permits execution.network.inputs packet :=
        fun packet present => (permits_eq_true_iff _ _).mp (physical.clean.2 packet present)
      rw [field] at latest
      obtain ⟨declared, declaredEarlier, declaredCall, declaredLatest⟩ :=
        (latestSignedBinding_iff_last_of_clean execution.network.inputs message producer candidate
          clean).mp latest
      have firstBound := declaredLatest actual ⟨actualInput, actualOwner, actualEarlier⟩
        acceptedHandle actualCall
      have secondBound := actualLatest declared declaredEarlier.1
        (declaredEarlier.2.1.trans actualOwner.symm) candidate declaredCall
      have same := (unique.inputs actual actualInput).inputs declared declaredEarlier.1
        (Prod.ext (declaredEarlier.2.1.trans actualOwner.symm)
          (Nat.le_antisymm secondBound firstBound))
      rw [same, actualCall] at declaredCall
      have equal := (Payload.commitment.inj declaredCall).2
      rw [← equal]
      exact associated

end Vegas.EventGraphRuntime.PhaseCount

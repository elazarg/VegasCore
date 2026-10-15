/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

private theorem accepted_of_latest (execution : (app).Execution)
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

/-- At an actual counted history, a current ready timely opening receives a
physical accepting receipt, including when its deferred source guard fails.
Its raw completion and exact normalized successor are both retained. -/
theorem opening_accepted_of_history [Fintype Player] (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (opening : message.payload.packet.call = .opening event candidate raw)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime event) :
    ∃ native next,
      handle runtime control.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      event ∈ native.config.cut.completed ∧
      next = ({control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧
      (app).handle control.execution.application message = some next := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace
  have physical := physicalBindings_history runtime leaks bounds plan inputs horizon scheduler trace
  have invariant := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawTrace
  have covered := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler rawTrace
  have permitted := (permits_eq_true_iff _ _).mp (physical.clean.2 message member)
  have correct := permitted.2.1
  unfold CountCallCorrect at correct
  dsimp only [nativeMessage] at correct
  rw [opening] at correct
  obtain ⟨certified, resolves⟩ := correct
  have latest := permitted.2.2.2
  unfold OpeningBinding at latest
  rw [opening] at latest
  have ready := request.2.2.1
  cases node : nodeView graph event with
  | bind | sample => simp only [node] at resolves
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [node] at resolves latest
      obtain ⟨sender, typed, signed⟩ := resolves
      have sender' : message.sender = owner := sender
      have associated := accepted_of_latest runtime leaks control.execution physical
        invariant.active covered.active
        (phaseInputBinding_history runtime leaks plan inputs horizon scheduler rawTrace)
        ((app).uniqueIds_history scheduler initial horizon control rawTrace)
        message member event candidate raw opening owner payload binding checks outputEq codeEq node
        ready request sender' latest
      have owned : candidate.1 = owner := by
        obtain ⟨ty, kind⟩ := invariant.active.accepted_typed binding.field candidate associated
        exact (EventField.binding.inj (binding.layout_eq.symm.trans kind)).1.symm
      have certificate : message.payload.packet.evidence = some ⟨candidate, raw⟩ := by
        unfold certifiedOpening at certified
        rw [opening] at certified
        cases evidence : message.payload.packet.evidence with
        | none => simp only [evidence, Bool.false_eq_true] at certified
        | some fact =>
            simp only [evidence, decide_eq_true_eq] at certified
            exact congrArg some certified
      have sound := (phasePacketEvidence runtime leaks).history_sound initial horizon scheduler
        rawTrace
      have verified := sound.inputs message member ⟨candidate, raw⟩ (by
        simp only [phasePacketEvidence, certificate, Option.toList_some, List.mem_singleton])
      change control.execution.application.current.native.candidates.lookup candidate =
        .openable raw at verified
      rcases raw with ⟨rawType, value⟩
      change rawType = payload at typed
      subst rawType
      have stored := invariant.active.opening_stored binding candidate value associated verified
      have defined := EventCode.resolveOutput?_isSome binding checks true
        control.execution.application.current.native.config.store (by
          intro field read
          apply control.execution.application.current.native.config.read_available ready
          rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
          exact read)
      obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp defined
      have rawAccepted := handle_opening_eq runtime control.execution.application.current.native
        message.id event candidate owner payload binding checks outputEq codeEq node ready timely
        sender' owned associated value verified stored result resolved
      obtain ⟨native, accepted⟩ : ∃ native,
          handle runtime control.execution.application.current.native
            ⟨message.id, message.payload.packet.call⟩ = some native := by
        rw [opening]
        exact ⟨_, rawAccepted⟩
      obtain ⟨named, addressed, unfinished, completed⟩ :=
        handle_completes runtime _ native _ accepted
      have same : named = event := Option.some.inj (addressed.symm.trans (by
        simp only [opening, Payload.event?]))
      let next := ({control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize
      refine ⟨native, next, accepted, by rwa [same] at completed, rfl, ?_⟩
      change control.execution.application.handle runtime message = some next
      have current : message.payload.attempt = control.execution.application.attempt := request.1
      have token : message.payload.tokenValid control.execution.application.attempt = true :=
        Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr current, permitted.1⟩
      have allowed : control.execution.application.allows message.payload.packet.call = true := by
        obtain ⟨phase, member, inside⟩ := request.2.1
        have head : control.execution.application.phases.head? = some phase := member
        simp only [PhaseRuntimeState.allows, head, opening, Payload.event?, decide_eq_true_eq]
        exact inside
      have active : control.execution.application.current.excludedCall
          message.payload.packet.call = false := by
        rw [opening]
        change (graph.actor? event).any
          (fun owner => decide (owner ∈ control.execution.application.current.excluded)) = false
        have acting : graph.actor? event = some message.sender := request.2.2.2.1
        rw [acting, Option.any_some]
        exact decide_eq_false (request.2.2.2.2 :
          message.sender ∉ control.execution.application.current.excluded)
      simp only [PhaseRuntimeState.handle, token, allowed, active, Bool.not_false,
        Bool.and_self, ↓reduceIte, accepted, Option.map_some, next]

end Vegas.EventGraphRuntime.PhaseCount

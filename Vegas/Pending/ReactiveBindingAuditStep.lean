/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRetainedBlock
import Vegas.Pending.ReactiveServiceConformance
import Interaction.ReactiveTrafficState

/-! # The exhaustive audited binding response

At an optional binding visit, every effective raw response either waits,
fixes the canonical opaque binding, or emits a record
rejected by the public service checker. The corresponding mixed law is coupled
to the actual retained implementation without a conformance premise on the
deviator. Required final-slot omission is a separate deadline obligation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Public conformance yields a complete clean-response classification. The
binding alternative deliberately retains every allowed private raw value. -/
theorem binding_audit_response_cases (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (turn : execution.application.publicView.OwnTurn owner event)
    (fresh : execution.application.candidates.lookup
      (owner, .prepared (execution.application.publicView.bindingCount owner)) = .fresh)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (response : (runtime.reactiveApplication leaks).Action)
    (available : response ∈ (bounds.menu runtime leaks).actions owner (execution.recall owner)
      (execution.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    response ∈ (app.silentPolicy (execution.recall owner) (execution.observe app owner)).support ∨
      (∃ opening, bounds.AllowsOpening opening ∧
        execution.network.nextSerial owner =
          Message.distinctAuthoredCount execution.network.ledger owner ∧ response =
        ⟨some ⟨⟨.commitment event
          (owner, .prepared (execution.application.publicView.bindingCount owner)), opening⟩,
            .none⟩⟩) ∨
      ∃ record, app.trafficStep (some ⟨remaining, some owner, execution⟩)
          (some ⟨remaining, none, execution.respond app owner response⟩) = [record] ∧
        record.envelope.sender = owner ∧
        runtime.permittedServiceEnvelope record.observation record.ledger
          record.envelope = false := by
  classical
  let app := runtime.reactiveApplication leaks
  have member := (bounds.menu_mem runtime leaks owner _ _ response).mp available
  have known := app.known_from_recall execution owner recalled
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      exact Or.inl (app.silentPolicy_support _ _)
  | some submission =>
      let record : app.TrafficRecord :=
        ⟨execution.application.publicView, execution.network.ledger,
          ⟨(owner, execution.network.nextSerial owner), submission.emit
            (app.submit execution.application owner submission) owner
              (execution.network.known owner)⟩⟩
      by_cases permitted : runtime.permittedServiceEnvelope record.observation record.ledger
          record.envelope = true
      · have admissible := (runtime.permittedServiceEnvelope_unpublished_iff _ _ _
            (serials.next_unpublished owner)).mp permitted
        have normal : submission.normalizeReactive owner
            (app.observePlayer execution.application owner)
            (execution.network.known owner) = submission := by
          have fixed := member.2
          change (⟨some (submission.normalizeReactive owner _ _)⟩ : app.Action) =
            ⟨some submission⟩ at fixed
          have equal := (Option.some.inj (congrArg ReactiveApplication.Action.transmission fixed))
          change execution.network.known owner =
            ReactiveApplication.ResponseMenu.knownPackets (execution.recall owner)
              (execution.observe app owner) at known
          rw [← known] at equal
          exact equal
        have canonical := runtime.normalize_binding_at_servicePhase leaks
          execution.application owner (execution.network.known owner) submission event payload
          outputEq codeEq node (execution.network.nextSerial owner) fresh
          (runtime.freshServiceEnvelope_event_of_owned_unique _ event _ turn.2.2 admissible.2)
          admissible.2
        rw [normal] at canonical
        exact Or.inr (Or.inl ⟨submission.call.opening, member.1.1.2, admissible.1,
          congrArg (fun material => (⟨some material⟩ : app.Action)) canonical⟩)
      · refine Or.inr (Or.inr ⟨record, ?_, rfl, Bool.eq_false_iff.mpr permitted⟩)
        exact app.trafficStep_submit execution remaining owner submission

namespace BindingMemory.Frame

variable {runtime leaks} {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- An arbitrary effective binding response is coupled to the actual legal
repair. Every failure of the joint frame already has an authentic rejected
traffic record. There is no clean-support or strategic-optimality premise. -/
theorem binding_stopped_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (fresh : original.application.candidates.lookup
      (owner, .prepared (original.application.publicView.bindingCount owner)) = .fresh)
    (actualSlot : reactiveFreshSlot
      (repaired.observe (runtime.reactiveApplication leaks) owner).application =
        some (original.application.publicView.bindingCount owner))
    (capacity : original.application.publicView.bindingCount owner < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (turn : original.application.publicView.OwnTurn owner event)
    (ready : original.application.config.cut.Ready event)
    (first : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner →
        runtime.eventRecorded leaks (repaired.recall owner) event = false)
    (serials : original.network.SerialsBeforeNext)
    (coverage : bounds.compiledActions runtime leaks owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) ⊆
        menu.actions owner (repaired.recall owner)
          (repaired.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
          (original.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining, some owner, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length) := by
  classical
  let app := runtime.reactiveApplication leaks
  let serial := original.application.publicView.bindingCount owner
  let law := players owner (original.recall owner) (original.observe app owner)
  let proposed (response : app.Action) :=
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    (changed.1, (⟨changed.2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩ :
        BindingMemory runtime leaks))
  let adjusted (response : app.Action) :=
    (if (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
        (repaired.observe app owner) then (proposed response).1
      else (menu.nonempty owner (repaired.recall owner) (repaired.observe app owner)).choose,
      (proposed response).2)
  let coupling := law.map fun response =>
    (original.respond app owner response, repaired.respond app owner (adjusted response).1,
      (adjusted response).2)
  have responseLaw :
      (retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) = law.map adjusted := by
    change ((implementation runtime leaks owner reference (players owner)).respond memory
      (repaired.recall owner, repaired.observe app owner)).map _ = _
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed,
        PMF.map_comp]
    simp only [law, adjusted, proposed, frame.observed, app, Function.comp_def]
  have silentLaw :
      app.silentPolicy (original.recall owner) (original.observe app owner) =
        app.silentPolicy (repaired.recall owner) (repaired.observe app owner) := rfl
  have owned : graph.actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
    exact actor
  have rightReady : repaired.application.publicView.EventReady event := by
    rw [← frame.publicView]
    exact (original.application.publicView_eventReady event).mpr ready
  have rightTurn : repaired.application.publicView.OwnTurn owner event := by
    rw [← frame.publicView]
    exact turn
  have originalFresh : (memory.shadow.inputView runtime leaks
      (repaired.observe app owner)).application.candidates (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ =
      ((retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner)).map _
    rw [responseLaw, PMF.map_comp]
    rfl
  · intro next supported
    obtain ⟨response, selected, rfl⟩ := PMF.support_map .. ▸ supported
    rcases runtime.binding_audit_response_cases leaks bounds original owner remaining event
        payload outputEq codeEq node turn fresh leftRecall serials response
          (available response selected) with silenced | canonical | departure
    · have unchanged : memory.repairResponse runtime leaks owner
          (repaired.observe app owner) response = (response, memory.shadow) := by
        rcases app.silentPolicy_cases _ _ response silenced with rfl
        rfl
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        apply coverage
        dsimp only [proposed]
        rw [unchanged]
        rw [silentLaw] at silenced
        exact bounds.silent_compiled runtime leaks owner _ _ response silenced
      right
      dsimp only [adjusted]
      rw [ite_eq_left legal]
      dsimp only [proposed]
      rw [unchanged]
      refine ⟨frame.transport_response response ?_, ?_⟩
      · intro material
        rcases app.silentPolicy_cases _ _ response silenced with rfl
        simp
      · rw [app.respond_recall_length]
        omega
    · obtain ⟨opening, bounded, counted, rfl⟩ := canonical
      have legal : (proposed
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩).1 ∈
            menu.actions owner (repaired.recall owner) (repaired.observe app owner) := by
        apply coverage
        apply bounds.requiredDecisionActions_subset_compiled runtime leaks owner
        exact repairResponse_binding_available runtime leaks bounds owner memory
          (repaired.recall owner) (repaired.observe app owner) event payload outputEq codeEq node
          rightTurn owned rightReady (first counted) serial actualSlot capacity default opening
          bounded originalFresh
      right
      dsimp only [adjusted]
      rw [ite_eq_left legal]
      refine ⟨frame.binding_submission event payload outputEq codeEq node serial opening fresh
        ready, ?_⟩
      rw [app.respond_recall_length]
      omega
    · exact Or.inl departure

/-- The stopping split survives the real partial pending-message sample at
an owner activation. Both executions use the same draw from the same pending
pool; the bound does not suppress or reveal that draw to the scheduler. -/
theorem binding_stopped_activation_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (fresh : original.application.candidates.lookup
      (owner, .prepared (original.application.publicView.bindingCount owner)) = .fresh)
    (actualSlot : reactiveFreshSlot
      (repaired.observe (runtime.reactiveApplication leaks) owner).application =
        some (original.application.publicView.bindingCount owner))
    (capacity : original.application.publicView.bindingCount owner < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (turn : original.application.publicView.OwnTurn owner event)
    (ready : original.application.config.cut.Ready event)
    (first : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner →
        runtime.eventRecorded leaks (repaired.recall owner) event = false)
    (serials : original.network.SerialsBeforeNext)
    (coverage : ∀ selected ∈ (leaks owner original.network.pending).support,
      let activated := repaired.sampledActivation (runtime.reactiveApplication leaks)
        owner selected
      bounds.compiledActions runtime leaks owner (activated.recall owner)
        (activated.observe (runtime.reactiveApplication leaks) owner) ⊆
          menu.actions owner (activated.recall owner)
            (activated.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ selected ∈ (leaks owner original.network.pending).support,
      let activated := original.sampledActivation (runtime.reactiveApplication leaks)
        owner selected
      ∀ response ∈ (players owner (activated.recall owner)
        (activated.observe (runtime.reactiveApplication leaks) owner)).support,
          response ∈ (bounds.menu runtime leaks).actions owner (activated.recall owner)
            (activated.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.dispatch players (.activate owner) original ∧
      coupling.map Prod.snd = (repaired.environmentStep app (.activate owner)).bind
        (fun execution => strategy.resume owner players (some owner) execution memory) ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining + 1, none, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length) := by
  classical
  let app := runtime.reactiveApplication leaks
  let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
  let sample := leaks owner original.network.pending
  have existsStep (selected) (supported : selected ∈ sample.support) :=
    (frame.activate owner selected).binding_stopped_response_coupling bounds menu players
      reference started leftRecall remaining event payload outputEq codeEq node
      fresh actualSlot capacity default turn ready first (serials.learn owner selected)
      (coverage selected supported) (available selected supported)
  let step := fun selected supported => (existsStep selected supported).choose
  refine ⟨sample.bindOnSupport step, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    change _ = (original.environmentStep app (.activate owner)).bind _
    rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.1
  · rw [map_bindOnSupport, ReactiveApplication.Execution.activation_samples,
      PMF.bind_map]
    have same : leaks owner repaired.network.pending = sample := by
      rw [← frame.network]
    change _ = (leaks owner repaired.network.pending).bind _
    rw [same]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.2.1
  · intro next supported
    obtain ⟨selected, member, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    rcases (existsStep selected member).choose_spec.2.2 next reached with bad | good
    · left
      exact bad
    · exact Or.inr good

end BindingMemory.Frame

end Vegas.EventGraphRuntime

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceOpening
import Vegas.Pending.ReactiveBindingResolveLaw
import Interaction.ReactiveTrafficState

/-! # Exhaustive guarded-disclosure stopping

Every effective raw response at a resolution either preserves the concrete
binding-repair frame or immediately emits an attributed record failing the
public service checker. The entire mixed response law uses the actual retained
implementation, including its fallback after departure. Deferred guards and
previously unusable bindings are included.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The source-like branch is established from actual packet soundness and
public checking, not assumed for the deviator's responses. -/
theorem resolution_audit_response_cases (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (remaining : Nat)
    (sound : (runtime.packetEvidence leaks).Sound execution)
    (invariant : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : execution.application.publicView.OwnTurn owner event)
    (first : execution.network.nextSerial owner =
      Message.distinctAuthoredCount execution.network.ledger owner →
        runtime.eventRecorded leaks (execution.recall owner) event = false)
    (response : (runtime.reactiveApplication leaks).Action)
    (available : response ∈ (bounds.menu runtime leaks).actions owner (execution.recall owner)
      (execution.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    response ∈ (app.silentPolicy (execution.recall owner) (execution.observe app owner)).support ∨
      (response = runtime.serviceDecision leaks owner (execution.recall owner)
        (execution.observe app owner) event
          (cast (congrArg EventField.Action outputEq.symm) false) ∧
        runtime.firstSubmission leaks (execution.recall owner) response = true) ∨
      (∃ value, binding.get? execution.application.config.store = some (.success value) ∧
        EventCode.resolveOutput? binding checks true execution.application.config.store =
          some (.success value) ∧
        response = runtime.serviceDecision leaks owner (execution.recall owner)
          (execution.observe app owner) event
            (cast (congrArg EventField.Action outputEq.symm) true) ∧
        runtime.firstSubmission leaks (execution.recall owner) response = true) ∨
      ∃ record, app.trafficStep (some ⟨remaining, some owner, execution⟩)
          (some ⟨remaining, none, execution.respond app owner response⟩) = [record] ∧
        record.envelope.sender = owner ∧
        runtime.permittedServiceEnvelope record.observation record.ledger
          record.envelope = false := by
  classical
  let app := runtime.reactiveApplication leaks
  have member := (bounds.menu_mem runtime leaks owner _ _ response).mp available
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
        have named := runtime.freshServiceEnvelope_event_of_owned_unique
          execution.application.publicView event _ (by exact turn.2.2) admissible.2
        have addressed : runtime.submittedEvent? leaks ⟨some submission⟩ =
            some event := named
        have firstResponse : runtime.firstSubmission leaks (execution.recall owner)
            ⟨some submission⟩ = true := by
          simp only [firstSubmission, addressed, first admissible.1, Bool.not_false]
        rcases runtime.service_resolution_response leaks bounds execution owner sound invariant
            recalled event payload binding checks outputEq codeEq node submission named available
              admissible.2 with withheld | ⟨value, stored, resolved, canonical⟩
        · exact Or.inr (Or.inl ⟨withheld, firstResponse⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨value, stored, resolved, canonical, firstResponse⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨record, ?_, rfl, Bool.eq_false_iff.mpr permitted⟩))
        exact app.trafficStep_submit execution remaining owner submission

namespace BindingMemory.Frame

variable {runtime leaks} {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Full-law stopping for guarded resolution. The original policy is arbitrary
within the effective raw menu; every clean branch has the same complete joint
observations and its real private-memory reconstruction. -/
theorem resolution_stopped_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : original.application.publicView.OwnTurn owner event)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (first : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner →
        runtime.eventRecorded leaks (original.recall owner) event = false)
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
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  let app := runtime.reactiveApplication leaks
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
    rcases runtime.resolution_audit_response_cases leaks bounds original owner remaining sound
        leftBinding leftRecall serials event payload binding checks outputEq codeEq node turn
          first response (available response selected) with silenced | withheld | canonical |
          departure
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
    · obtain ⟨same, firstResponse⟩ := withheld
      have actual : response = ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ :=
        same.trans (runtime.serviceDecision_resolution_false leaks owner (original.recall owner)
          (original.observe app owner) event owner payload binding checks outputEq codeEq node)
      have unchanged : memory.repairResponse runtime leaks owner
          (repaired.observe app owner) response = (response, memory.shadow) := by
        rw [actual]
        rfl
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        apply coverage
        dsimp only [proposed]
        rw [unchanged, actual]
        apply frame.withholding_response_retained bounds event payload binding checks outputEq
          codeEq node turn owned
        rwa [actual] at firstResponse
      right
      dsimp only [adjusted]
      rw [ite_eq_left legal]
      dsimp only [proposed]
      rw [unchanged]
      refine ⟨?_, ?_⟩
      · rw [actual]
        exact frame.withholding_response_frame event
      · rw [app.respond_recall_length]
        omega
    · obtain ⟨value, stored, resolved, same, firstResponse⟩ := canonical
      have unchanged : memory.repairResponse runtime leaks owner
          (repaired.observe app owner) response = (response, memory.shadow) := by
        obtain ⟨_, candidate, associated, _, candidateOwned, fixed, _⟩ :=
          frame.successful_opening leftBinding rightBinding binding value stored
        have actual := runtime.serviceDecision_successful_opening leaks original leftRecall owner
          event payload binding checks outputEq codeEq node candidate value associated
            candidateOwned fixed resolved
        rw [same, actual]
        simp only [repairResponse, disclosureSubmission, WitnessedSubmission.normalizeReactive,
          Submission.normalizeReactive_none]
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        apply coverage
        dsimp only [proposed]
        rw [unchanged]
        exact frame.successful_serviceDecision_retained bounds leftRecall rightRecall leftBinding
          rightBinding event payload binding checks outputEq codeEq node turn owned ready timely
            value stored resolved response same (available response selected) firstResponse
      right
      dsimp only [adjusted]
      rw [ite_eq_left legal]
      dsimp only [proposed]
      rw [unchanged]
      refine ⟨?_, ?_⟩
      · rw [same]
        exact frame.successful_response_frame leftRecall leftBinding rightBinding event payload
          binding checks outputEq codeEq node value stored resolved
      · rw [app.respond_recall_length]
        omega
    · exact Or.inl departure

/-- Actual passive observation followed by the arbitrary resolution response
has the same exhaustive stopping split, with a shared sample on the two sides. -/
theorem resolution_stopped_activation_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : original.application.publicView.OwnTurn owner event)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (first : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner →
        runtime.eventRecorded leaks (original.recall owner) event = false)
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
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  let app := runtime.reactiveApplication leaks
  let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
  let sample := leaks owner original.network.pending
  have existsStep (selected) (supported : selected ∈ sample.support) :=
    (frame.activate owner selected).resolution_stopped_response_coupling bounds menu players
      reference started leftRecall rightRecall (sound.learn owner selected) leftBinding
      rightBinding remaining event payload binding checks outputEq codeEq node turn ready
      timely first (serials.learn owner selected) (coverage selected supported)
      (available selected supported)
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

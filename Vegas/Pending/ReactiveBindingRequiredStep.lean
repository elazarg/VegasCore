/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAuditStep
import Vegas.Pending.ReactiveBindingFinalOmission

/-! # The final required binding response with both evidence sources

Every effective mixed response has one coupling to the fixed legal repair.
Canonical opaque bindings preserve the joint frame, nonconforming emitted
traffic gives an audit record, and silence or replay entails a public missed
binding after the actual foreign tail and deadline. Later policies are arbitrary.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- One actual mixed response law covers every final-slot deviation. The
omission alternative is a proved deadline conclusion, not an assumption about
later policies. Only the canonical branch retains the private joint frame. -/
theorem required_binding_stopped_response_coupling
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
    (unsent : runtime.eventRecorded leaks (repaired.recall owner) event = false)
    (unbound : original.application.accepted (.inr event) = none)
    (published : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (serials : original.network.SerialsBeforeNext)
    (coverage : bounds.requiredBindingActions runtime leaks owner (repaired.recall owner)
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
        (∀ (later : Player → app.Policy) (network : runtime.NetworkPolicy leaks)
          (final : app.Execution), final ∈ (runtime.runInteractionPlan leaks later network
            (visits.map ServiceInstruction.player ++
              (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
                next.1).support → final.application.publicView.missedBinding event = true) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length) := by
  classical
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
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
          (available response selected) with replay | canonical | departure
    · right
      left
      intro later network final reached
      apply runtime.last_binding_transport_omission leaks later network original owner event payload
        outputEq codeEq node ready unbound published entered ticks activated due visits absent
        response _ final reached
      intro material
      rcases app.silentPolicy_cases _ _ response replay with rfl
      simp
    · obtain ⟨opening, bounded, _, rfl⟩ := canonical
      have legal : (proposed
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩).1 ∈
            menu.actions owner (repaired.recall owner) (repaired.observe app owner) := by
        apply coverage
        exact repairResponse_binding_available runtime leaks bounds owner memory
          (repaired.recall owner) (repaired.observe app owner) event payload outputEq codeEq node
          rightTurn owned rightReady unsent serial actualSlot capacity default opening
          bounded originalFresh
      right
      right
      dsimp only [adjusted]
      rw [ite_eq_left legal]
      refine ⟨frame.binding_submission event payload outputEq codeEq node serial opening fresh
        ready, ?_⟩
      rw [app.respond_recall_length]
      omega
    · exact Or.inl departure

/-- The same exhaustive split includes the actual passive sample before the
last response; both sides retain the existing partial-observation interface. -/
theorem required_binding_stopped_activation_coupling
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
    (unsent : runtime.eventRecorded leaks (repaired.recall owner) event = false)
    (unbound : original.application.accepted (.inr event) = none)
    (published : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (serials : original.network.SerialsBeforeNext)
    (coverage : ∀ selected ∈ (leaks owner original.network.pending).support,
      let activated := repaired.sampledActivation (runtime.reactiveApplication leaks)
        owner selected
      bounds.requiredBindingActions runtime leaks owner (activated.recall owner)
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
        (∀ (later : Player → app.Policy) (network : runtime.NetworkPolicy leaks)
          (final : app.Execution), final ∈ (runtime.runInteractionPlan leaks later network
            (visits.map ServiceInstruction.player ++
              (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
                next.1).support → final.application.publicView.missedBinding event = true) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length) := by
  classical
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  let app := runtime.reactiveApplication leaks
  let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
  let sample := leaks owner original.network.pending
  have existsStep (selected) (supported : selected ∈ sample.support) :=
    (frame.activate owner selected).required_binding_stopped_response_coupling bounds menu players
      reference started leftRecall remaining event payload outputEq codeEq node
      fresh actualSlot capacity default turn ready unsent unbound
      (published.learn owner selected) entered ticks activated due visits absent
      (serials.learn owner selected)
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

end Vegas.EventGraphRuntime.BindingMemory.Frame
